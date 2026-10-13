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

/-- Smooth cutoff: for a compact `K` inside an open `U ⊆ ℝ^P` there is a `C^∞` function
`0 ≤ χ ≤ 1` with compact support in `U` that equals `1` on an open neighbourhood `N` of `K`. -/
theorem Submission.fiw_tb_ext_cutoff :
    ∀ (P : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U →
      ∃ (χ : Eucl P → ℝ) (N : Set (Eucl P)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ IsOpen N ∧ K ⊆ N ∧
        ∀ x ∈ N, χ x = 1 := by
  intro P U K hU hK hKU
  -- Compact `L₁, L` with `K ⊆ interior L₁ ⊆ L₁ ⊆ interior L ⊆ L ⊆ U`.
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L₁, hL₁, hKL₁, hL₁L⟩ := exists_compact_between hK isOpen_interior hKL
  -- Smooth Urysohn: `f` is `C^∞`, `0 ≤ f ≤ 1`, `support f = interior L`, `f = 1` exactly on `L₁`.
  obtain ⟨f, hf, hfr, hfs, hf1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) isOpen_interior hL₁.isClosed hL₁L
  -- `L` is closed, so `tsupport f = closure (interior L) ⊆ L`; hence it is compact and `⊆ U`.
  have htsupp : tsupport f ⊆ L :=
    closure_minimal (hfs.symm ▸ interior_subset) hL.isClosed
  refine ⟨f, interior L₁, hf, fun x => hfr (mem_range_self x), ?_, htsupp.trans hLU,
    isOpen_interior, hKL₁, fun x hx => (hf1 x).mp (interior_subset hx)⟩
  exact hL.of_isClosed_subset (isClosed_tsupport _) htsupp
/-- Products with a cutoff (Simon Ch. 6, §2): if `χ` is `C^∞` with `tsupport χ ⊆ W`, then
`ω ↦ χ ω` is a linear map `𝒟^q(V) → 𝒟^q(W)`, acting pointwise on the underlying forms. -/
theorem Submission.fiw_tb_ext_smul_testForm :
    ∀ (P q : ℕ) (V W : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ →
      tsupport χ ⊆ W → ∃ L : TestFormOn V q →ₗ[ℝ] TestFormOn W q, ∀ (ω : TestFormOn V q)
        (x : Eucl P), (L ω : DifferentialForm (Eucl P) q) x =
          χ x • (ω : DifferentialForm (Eucl P) q) x := by
  intro P q V W χ hχ hχW
  -- `χ ω` is smooth, its support lies in the compact `tsupport ω` and in `tsupport χ ⊆ W`.
  have hmem : ∀ ω : TestFormOn V q,
      (fun x => χ x • (ω : DifferentialForm (Eucl P) q) x) ∈ TestFormOn W q := by
    intro ω
    obtain ⟨⟨hs, hc⟩, -⟩ := ω.property
    refine ⟨⟨hχ.smul hs, ?_⟩, (tsupport_smul_subset_left _ _).trans hχW⟩
    exact hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)
  -- Additivity and homogeneity hold pointwise on the underlying forms.
  refine ⟨{ toFun := fun ω => ⟨_, hmem ω⟩, map_add' := ?_, map_smul' := ?_ }, fun ω x => rfl⟩
  · intro a b
    apply Subtype.ext
    funext x
    change χ x • ((a : DifferentialForm (Eucl P) q) x + (b : DifferentialForm (Eucl P) q) x) = _
    rw [smul_add]
    rfl
  · intro c a
    apply Subtype.ext
    funext x
    change χ x • (c • (a : DifferentialForm (Eucl P) q) x) =
      c • (χ x • (a : DifferentialForm (Eucl P) q) x)
    rw [smul_comm]
/-- Locality of a current (cf. the support `spt T`, Simon Ch. 6, 2.11): if `Z` vanishes on every
test form whose support misses `K`, and `η = ω` on an open `N ⊇ K`, then `Z(η) = Z(ω)`.  The difference
`η - ω` vanishes on `N`, so its support lies in the closed set `ℝ^P ∖ N`, which misses `K`; by
linearity `Z(η) - Z(ω) = Z(η - ω) = 0`. -/
theorem Submission.fiw_tb_ext_apply_eq_of_eqOn : ∀ (P q : ℕ) (V K N : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen N → K ⊆ N → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → ∀ ω η : TestFormOn V q, (∀ x ∈ N, (η : DifferentialForm (Eucl P) q) x = (ω : DifferentialForm (Eucl P) q) x) → Z η = Z ω := by
  intro P q V K N Z hN hKN hZ ω η hηω
  -- `η - ω` vanishes on the open set `N`, so its support lies in the closed set `Nᶜ`.
  have hsupp : tsupport ((η - ω : TestFormOn V q) : DifferentialForm (Eucl P) q) ⊆ Nᶜ := by
    apply closure_minimal _ hN.isClosed_compl
    intro x hx hxN
    apply hx
    change (η : DifferentialForm (Eucl P) q) x - (ω : DifferentialForm (Eucl P) q) x = 0
    rw [hηω x hxN, sub_self]
  -- `Nᶜ` misses `K ⊆ N`, so `Z(η - ω) = 0`; conclude by linearity.
  have h0 : Z (η - ω) = 0 :=
    hZ _ (Disjoint.mono_left hsupp (disjoint_compl_left.mono_right hKN))
  have h1 : Z (η - ω) = Z η - Z ω := Z.toCurrent.map_sub η ω
  rw [h1] at h0
  exact sub_eq_zero.mp h0
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
/-- Homogeneity of the Euclidean coefficient norm (Simon Ch. 6, 1.15, 2.4–2.5):
`|c α| = |c| |α|`.  Every coefficient of `c • α` on an increasing tuple of basis vectors is
`c` times that of `α`, so each squared coefficient gains the factor `c²`; pull `c²` out of the
finite sum and use `√(c² s) = √(c²) √s = |c| √s`. -/
theorem Submission.fiw_tb_ext_covectorNorm_smul : ∀ (P q : ℕ) (c : ℝ) (α : Covector (Eucl P) q), covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
  intro P q c α
  unfold covectorEuclideanNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs
  · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
  · simp
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Y) < ∞` and `|ω(x)| ≤ C` everywhere (Euclidean
coefficient norm) with `C > 0`, then `|Y(ω)| ≤ C · M(Y)`. -/
theorem Submission.br_la_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U n) (ω : TestFormOn U n) (C : ℝ),
      0 < C → (∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      Y.mass ≠ ∞ → |Y ω| ≤ C * Y.mass.toReal := by
  intro P n U Y ω C hC hω hY
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
  -- If `|η| ≤ C` pointwise, then `C⁻¹ η` is mass-admissible, hence `Y(η) ≤ C · M(Y)`.
  have hone : ∀ η : TestFormOn U n,
      (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ C) →
        Y η ≤ C * Y.mass.toReal := by
    intro η hη
    have hadm : C⁻¹ • η ∈ massAdmissibleOn U n U := by
      refine ⟨(C⁻¹ • η).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (C⁻¹ • (η : DifferentialForm (Eucl P) n) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hC), inv_mul_le_iff₀ hC, mul_one]
      exact hη x
    have hle : ENNReal.ofReal (Y (C⁻¹ • η)) ≤ Y.mass := Y.le_massOn hadm
    rwa [ENNReal.ofReal_le_iff_le_toReal hY, map_smul, smul_eq_mul, inv_mul_le_iff₀ hC] at hle
  -- Apply this to `ω` and to `-ω`, using `|-ω(x)| = |ω(x)|` and `Y(-ω) = -Y(ω)`.
  have hneg := hone (-ω) fun x => by
    change covectorEuclideanNorm (-(ω : DifferentialForm (Eucl P) n) x) ≤ C
    rw [covectorEuclideanNorm_neg]
    exact hω x
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hneg
  exact abs_le.mpr ⟨by linarith, hone ω hω⟩
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Z) < ∞` and `|η(x)| ≤ c` everywhere (Euclidean
coefficient norm) with `c > 0`, then `|Z(η)| ≤ c · M(Z)`. -/
theorem Submission.fiw_tb_te_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U n) (η : TestFormOn U n) (c : ℝ),
      0 < c → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ c) →
      Z.mass ≠ ∞ → |Z η| ≤ c * Z.mass.toReal := by
  intro P n U Z η c hc hη hZ
  -- Homogeneity of the Euclidean coefficient norm: `|t β| = |t| |β|`.
  have hsmul : ∀ (t : ℝ) (β : Covector (Eucl P) n),
      covectorEuclideanNorm (t • β) = |t| * covectorEuclideanNorm β := by
    intro t β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- If `|θ| ≤ c` pointwise, then `c⁻¹ θ` is mass-admissible, hence `Z(θ) ≤ c · M(Z)`.
  have hone : ∀ θ : TestFormOn U n,
      (∀ x, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) n) x) ≤ c) →
        Z θ ≤ c * Z.mass.toReal := by
    intro θ hθ
    have hadm : c⁻¹ • θ ∈ massAdmissibleOn U n U := by
      refine ⟨(c⁻¹ • θ).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (c⁻¹ • (θ : DifferentialForm (Eucl P) n) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ hc, mul_one]
      exact hθ x
    have hle : ENNReal.ofReal (Z (c⁻¹ • θ)) ≤ Z.mass := Z.le_massOn hadm
    rwa [ENNReal.ofReal_le_iff_le_toReal hZ, map_smul, smul_eq_mul, inv_mul_le_iff₀ hc] at hle
  -- Apply this to `η` and to `-η`, using `|-η(x)| = |η(x)|` and `Z(-η) = -Z(η)`.
  have hneg := hone (-η) fun x => by
    change covectorEuclideanNorm (-(η : DifferentialForm (Eucl P) n) x) ≤ c
    rw [covectorEuclideanNorm_neg]
    exact hη x
  have hZneg : Z (-η) = -Z η := map_neg Z.toCurrent η
  rw [hZneg] at hneg
  exact abs_le.mpr ⟨by linarith, hone η hη⟩
/-- The Euclidean coefficient norm of an `n`-covector on `ℝ^P` is at most `√(P^n)` times its
operator norm: each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` (`b` the standard
orthonormal basis) is bounded by `‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.fiw_ims_sc_covectorNorm_le_opNorm :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
  intro P n α
  -- Every coefficient is at most `‖α‖`, since the standard basis vectors are unit vectors.
  have hcoef : ∀ I : Fin n → Fin P,
      |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
    intro I
    have h := ContinuousAlternatingMap.le_opNorm α
      (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
    simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
      Real.norm_eq_abs] at h
    exact h
  rw [covectorEuclideanNorm]
  calc Real.sqrt _ ≤ Real.sqrt ((P : ℝ) ^ n * ‖α‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        -- The sum has `P ^ n` terms, each at most `‖α‖ ^ 2`.
        calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro I _
              split_ifs
              · rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) (hcoef I) 2
              · positivity
          _ = (P : ℝ) ^ n * ‖α‖ ^ 2 := by simp [Finset.card_univ]
    _ = Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- **Test forms have bounded Euclidean coefficient norm**: Simon's
`|ω| = sup_x √⟨ω(x), ω(x)⟩` (Ch. 6, 1.15, p. 134) is finite, with a positive bound.
A test form is smooth, hence continuous, and has compact support, so `‖ω(x)‖ ≤ B` for its
operator norm; `|α| ≤ √(Pⁿ) ‖α‖` (`fiw_ims_sc_covectorNorm_le_opNorm`) then gives the bound
`C = √(Pⁿ) B + 1 > 0`. -/
theorem Submission.fiw_ims_sc_testForm_bounded : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U n), ∃ C : ℝ, 0 < C ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C := by
  intro P n U ω
  -- `ω` is smooth, hence continuous, and has compact support, so `‖ω(x)‖ ≤ B` for all `x`.
  have hω : Continuous (ω : DifferentialForm (Eucl P) n) := ω.property.1.1.continuous
  obtain ⟨B, hB⟩ := ω.property.1.2.exists_bound_of_continuous hω
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ Real.sqrt ((P : ℝ) ^ n) := Real.sqrt_nonneg _
  refine ⟨Real.sqrt ((P : ℝ) ^ n) * B + 1, by positivity, fun x => ?_⟩
  calc covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)
      ≤ Real.sqrt ((P : ℝ) ^ n) * ‖(ω : DifferentialForm (Eucl P) n) x‖ :=
        Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
    _ ≤ Real.sqrt ((P : ℝ) ^ n) * B := mul_le_mul_of_nonneg_left (hB x) hD0
    _ ≤ Real.sqrt ((P : ℝ) ^ n) * B + 1 := by linarith
/-- **A null sequence of test forms is uniformly small (Simon Ch. 6, 2.1).**  If `ω_q → 0` in
`𝒟ⁿ(U)`, then all `ω_q` are supported in one compact `K ⊆ U` and, for every `ε > 0`, eventually
`|ω_q(x)| ≤ ε` for every `x`, in the Euclidean coefficient norm of Remark 2.6.  The `k = 0` part
of the convergence makes the operator norm `‖ω_q(x)‖` uniformly small on `K`, and `ω_q = 0` off
`K`; `Submission.fiw_ims_sc_covectorNorm_le_opNorm` gives `|α| ≤ √(P^n) ‖α‖`. -/
theorem Submission.fiw_ims_sc_converges_zero_small : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : ℕ → TestFormOn U n), TestFormOnConverges ω 0 → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ U ∧ (∀ q, tsupport ((ω q : DifferentialForm (Eucl P) n)) ⊆ K) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop, ∀ x, covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x) ≤ ε := by
  intro P n U ω hω
  obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hω
  refine ⟨K, hK, hKU, hsupp, fun ε hε => ?_⟩
  set D := Real.sqrt ((P : ℝ) ^ n)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hδ : 0 < ε / (D + 1) := by positivity
  -- `k = 0`: eventually `‖ω_q(x) - 0‖ < ε / (D + 1)` for all `x ∈ K`.
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv 0) _ hδ] with q hq x
  have hx : ‖(ω q : DifferentialForm (Eucl P) n) x‖ ≤ ε / (D + 1) := by
    by_cases hxK : x ∈ K
    · have h := hq x hxK
      rw [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
        norm_iteratedFDeriv_zero] at h
      exact h.le
    · -- off `K ⊇ tsupport ω_q` the form vanishes
      rw [image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp q h), norm_zero]
      exact hδ.le
  calc covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x)
      ≤ D * ‖(ω q : DifferentialForm (Eucl P) n) x‖ :=
        Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
    _ ≤ D * (ε / (D + 1)) := mul_le_mul_of_nonneg_left hx hD
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
/-- If `M ⊆ U` is `μ`-null on every open `W ⊂⊂ U` on which `T` vanishes, then `μ(M ∖ spt T) = 0`:
`M ∖ spt T` lies in the zero region (Simon 2.11), a countable union of such `W` (Lindelöf). -/
theorem Submission.lpf_rsn_null_diff_support_of_local_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0 := by
  intro P n U T M μ hMU hloc
  -- Countably many of the open sets whose union is `T.zeroRegion` already cover it.
  obtain ⟨S, hSc, hSsub, hSeq⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Eucl P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- As `M ⊆ U`, every point of `M ∖ spt T` lies in `T.zeroRegion = ⋃₀ S`.
  have hsub : M \ T.support ⊆ ⋃ W ∈ S, M ∩ W := by
    rintro x ⟨hxM, hxs⟩
    have hxZ : x ∈ ⋃₀ S := by
      rw [hSeq]
      by_contra hxZ
      exact hxs ⟨hMU hxM, hxZ⟩
    obtain ⟨W, hWS, hxW⟩ := hxZ
    exact mem_biUnion hWS ⟨hxM, hxW⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hSc).2 fun W hWS => ?_)
  obtain ⟨hWo, hWc, hWU, hWv⟩ := hSsub hWS
  exact hloc W hWo hWc hWU hWv
/-- Finitely many `n`-covectors separate `n`-vectors (Simon Ch. 6, §1; used for Lemma 3.9 to show
that a representation `τ(M, θ, ξ)` of `T` lives on `spt T` up to an `Hⁿ`-null set).  Evaluation on
tuples of standard basis vectors, `Φ(α)(r) = α(e_{r(1)}, …, e_{r(n)})`, embeds `Λⁿ(ℝ^P)` linearly
into `ℝ^(Fin n → Fin P)`, since a multilinear map is determined by its values on basis vectors.
So `Λⁿ(ℝ^P)` is finite-dimensional, and an `n`-vector vanishing on a basis `b₁, …, b_N` is zero. -/
theorem Submission.lpf_rsn_covector_separating_family : ∀ (P n : ℕ), ∃ (N : ℕ) (b : Fin N → Covector (Eucl P) n), ∀ w : NVector (Eucl P) n, (∀ i, w (b i) = 0) → w = 0 := by
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
/-- **Fundamental lemma of the calculus of variations with a positive weight** (a step of the
proof that a rectifiable `τ(M, θ, ξ)` lives on its support, Simon Ch. 6, 3.9).  If `θ > 0` on `M`,
`θ` is `μ`-integrable on `M ∩ W` with `W` open, `g` is a.e.-strongly measurable and a.e. bounded
for `μ ⌞ M`, and `∫_M θ φ g dμ = 0` for every smooth compactly supported `φ` with
`tsupport φ ⊆ W`, then `g = 0` `μ ⌞ M`-a.e. on `W`.  Mathlib's fundamental lemma applied to `θ g`,
which is integrable on `W` for `μ ⌞ M`, gives `θ g = 0` there; divide by `θ`. -/
theorem Submission.lpf_rsn_weighted_fundamental_lemma : ∀ (P : ℕ) (μ : Measure (Eucl P)) (M W : Set (Eucl P)) (θ g : Eucl P → ℝ) (C : ℝ), IsOpen W → NullMeasurableSet M μ → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) μ → AEStronglyMeasurable g (μ.restrict M) → (∀ᵐ x ∂(μ.restrict M), |g x| ≤ C) → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W → ∫ x in M, θ x * (φ x * g x) ∂μ = 0) → ∀ᵐ x ∂(μ.restrict M), x ∈ W → g x = 0 := by
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
  -- Step 4: `μ ⌞ M`-a.e. point lies in `M`, where `θ > 0`.
  filter_upwards [hzero, ae_restrict_mem₀ hM] with x hx hxM hxW
  rcases mul_eq_zero.mp (hx hxW) with h | h
  · exact absurd h (hpos x hxM).ne'
  · exact h

/-- **A representation is null where the current vanishes (steps 5–8 of (P2) in Simon Ch. 6,
Lemma 3.9).**  If `T = τ(M, θ, ξ)` with `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`, `T` vanishes on the open set
`W ⊆ U` and `θ` is integrable on `M ∩ W`, then `Hⁿ(M ∩ W) = 0`.  Testing `T` with `φ α`
(`φ ∈ C_c^∞(W)`, `α` an `n`-covector) gives `∫_M θ φ ⟨α, ξ⟩ dHⁿ = 0`, so `⟨α, ξ⟩ = 0` a.e. on
`M ∩ W` (`lpf_rsn_weighted_fundamental_lemma`).  Finitely many covectors separate `n`-vectors
(`lpf_rsn_covector_separating_family`), so `ξ = 0` a.e. on `M ∩ W`; as `‖ξ‖ = 1` a.e. on `M`,
the set `M ∩ W` is null. -/
theorem Submission.lpf_rsn_local_null : ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsOpen W → W ⊆ U → T.VanishesOn W → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) (μHE[n] : Measure (Eucl P)) → AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ = 1) → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M ∩ W) = 0 := by
  intro P n U W T M θ ξ hW hWU hvan hM hpos hθ hξm hξ1 hrep
  -- Each coordinate `x ↦ ξ x α` is bounded by `‖α‖` and vanishes a.e. on `M ∩ W`.
  have key : ∀ α : Covector (Eucl P) n,
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ W → ξ x α = 0 := by
    intro α
    refine Submission.lpf_rsn_weighted_fundamental_lemma P (μHE[n] : Measure (Eucl P)) M W θ
      (fun x => ξ x α) ‖α‖ hW hM hpos hθ ?_ ?_ ?_
    · exact (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable hξm
    · filter_upwards [hξ1] with x hx
      calc |ξ x α| = ‖ξ x α‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ξ x‖ * ‖α‖ := (ξ x).le_opNorm α
        _ = ‖α‖ := by rw [hx, one_mul]
    · -- `ω = φ α` is a test form supported in `W`, so `T ω = 0`.
      intro φ hφ hφc hφW
      let ω : DifferentialForm (Eucl P) n := fun x => φ x • α
      have hωs : IsSmoothForm ω := hφ.smul contDiff_const
      have hωc : HasCompactSupport ω := hφc.smul_right
      have hωW : tsupport ω ⊆ W := (tsupport_smul_subset_left φ (fun _ => α)).trans hφW
      let ωU : TestFormOn U n := ⟨ω, ⟨hωs, hωc⟩, hωW.trans hWU⟩
      have h0 : T ωU = 0 := hvan ωU hωW
      rw [hrep ωU] at h0
      simpa [tauAction, ωU, ω, map_smul, smul_eq_mul] using h0
  -- A finite separating family of covectors gives `ξ = 0` a.e. on `M ∩ W`, where `‖ξ‖ = 1`.
  obtain ⟨N, b, hb⟩ := Submission.lpf_rsn_covector_separating_family P n
  have hall : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ i, x ∈ W → ξ x (b i) = 0 :=
    ae_all_iff.mpr fun i => key (b i)
  have hnotW : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∉ W := by
    filter_upwards [hall, hξ1] with x hx h1 hxW
    rw [hb (ξ x) fun i => hx i hxW, ContinuousLinearMap.opNorm_zero] at h1
    exact zero_ne_one h1
  have hres : (μHE[n] : Measure (Eucl P)).restrict M W = 0 := by
    rw [ae_iff] at hnotW
    simpa using hnotW
  rwa [Measure.restrict_apply hW.measurableSet, Set.inter_comm] at hres
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

/-- **A rectifiable representation lives on the support (step (P2) of Simon Ch. 6, Lemma 3.9).**
If `T = τ(M, θ, ξ)` then `Hⁿ(M \ spt T) = 0`.  An orthonormal frame `τ` has Gram matrix `1`, so
`‖simpleNVector τ‖ = 1` by `lpf_simple_nvector_algebra` and `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`
(`orients`).  Hence `Hⁿ(M ∩ W) = 0` for every open `W ⊂⊂ U` on which `T` vanishes
(`lpf_rsn_local_null`), and countably many such `W` cover the zero region of `T`
(`lpf_rsn_null_diff_support_of_local_null`). -/
theorem Submission.lpf_rectifiable_support_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := by
  intro P n U T M θ ξ hM hT
  -- Unit norm: `ξ x = ±simpleNVector τ` with `τ` orthonormal for `Hⁿ`-a.e. `x ∈ M`, and
  -- `‖simpleNVector τ‖ ^ 2 = det (⟪τᵢ, τⱼ⟫) = det 1 = 1`.
  have hξ : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ = 1 := by
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, -, hξx⟩ := hx
    have hgram : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = 1 := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
    have hτ1 : ‖simpleNVector τ‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (ContinuousLinearMap.opNorm_nonneg _) two_ne_zero).mp ?_
      rw [Submission.lpf_simple_nvector_algebra.1, hgram, Matrix.det_one]
    rcases hξx with h | h
    · rw [h, hτ1]
    · rw [h, ContinuousLinearMap.opNorm_neg, hτ1]
  -- It suffices that `Hⁿ(M ∩ W) = 0` for each open `W ⊂⊂ U` on which `T` vanishes; there `θ` is
  -- integrable on `M ∩ W ⊆ M ∩ closure W`.
  refine Submission.lpf_rsn_null_diff_support_of_local_null P n U T M _ hM.subset
    fun W hW hWc hWU hTW => ?_
  exact Submission.lpf_rsn_local_null P n U W T M θ ξ hW (subset_closure.trans hWU) hTW
    hM.nullMeasurableSet hM.pos
    ((hM.integrableOn _ hWc hWU).mono_set (Set.inter_subset_inter_right M subset_closure))
    hM.aestronglyMeasurable hξ hT
/-- Simon Ch. 6, 2.4–2.5 and 2.16: restricting `Y ∈ 𝒟ₖ(U)` to a smaller domain `W ⊆ U` does
not increase mass, `M(Y|_W) ≤ M(Y)`.  Every `ω` admissible for `M_W(Y|_W)`, regarded as the
test form `ιω` on `U` with the same underlying form, is admissible for `M_U(Y)`, and
`Y|_W(ω) = Y(ιω)`.  `W` need not be open. -/
theorem Submission.fiw_tb_ri_restrictDomain_mass_le :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U) (Y : GeometricCurrentOn U k),
      (Y.restrictDomain hWU).mass ≤ Y.mass := by
  intro P k U W hWU Y
  -- `(Y|_W).mass` is the supremum of `ofReal (Y|_W ω)` over `ω ∈ massAdmissibleOn W k W`.
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  -- `ιω` has the same underlying form as `ω`, so `tsupport ιω ⊆ W ⊆ U` and `|ιω(x)| ≤ 1`.
  exact Y.le_massOn (omega := testFormOnInclusion hWU k ω) ⟨hω.1.trans hWU, hω.2⟩
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

/-- **Cut-off of a finite-mass current (Simon Ch. 6, 2.1, 2.4).**  If `χ` is smooth with
`tsupport χ ⊆ U` and `|χ| ≤ 1`, and `X ∈ 𝒟_q(U)` has `M(X) < ∞`, then `Y(ω) = X(χ ω)` is a
current in `ℝ^P`.  If `ω_j → 0` in `𝒟^q(ℝ^P)`, eventually `|χ ω_j(x)| ≤ |ω_j(x)| ≤ δ` for every
`x` (`Submission.fiw_ims_sc_converges_zero_small`), so `|Y(ω_j)| ≤ δ · M(X)` by
`Submission.br_la_abs_apply_le_mul_mass`. -/
theorem Submission.fiw_tb_ext_cutoff_current : ∀ (P q : ℕ) (U : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ U → (∀ x, |χ x| ≤ 1) → ∀ X : GeometricCurrentOn U q, X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) q, ∀ (ω : TestFormOn (univ : Set (Eucl P)) q) (η : TestFormOn U q), (∀ x, (η : DifferentialForm (Eucl P) q) x = χ x • (ω : DifferentialForm (Eucl P) q) x) → Y ω = X η := by
  intro P q U χ hχ hχU hχ1 X hX
  -- `L ω = χ ω` is a linear map `𝒟^q(ℝ^P) → 𝒟^q(U)`, and `Y = X ∘ L`.
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q (univ : Set (Eucl P)) U χ hχ hχU
  refine ⟨⟨X.toCurrent.comp L, ?_⟩, ?_⟩
  · intro ωs hωs
    obtain ⟨_, -, -, -, hsmall⟩ := Submission.fiw_ims_sc_converges_zero_small P q univ ωs hωs
    rw [Metric.tendsto_atTop]
    intro ε hε
    set μX := X.mass.toReal
    have hμ0 : 0 ≤ μX := ENNReal.toReal_nonneg
    have hδ : 0 < ε / (μX + 1) := by positivity
    -- Eventually `|ω_j(x)| ≤ δ := ε / (M(X) + 1)` for every `x`.
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hsmall (ε / (μX + 1)) hδ)
    refine ⟨j₀, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero]
    -- Then `|χ ω_j(x)| = |χ(x)| |ω_j(x)| ≤ δ`, as `|χ| ≤ 1`.
    have hbound : ∀ x, covectorEuclideanNorm
        ((L (ωs j) : DifferentialForm (Eucl P) q) x) ≤ ε / (μX + 1) := by
      intro x
      rw [hL, Submission.fiw_tb_ext_covectorNorm_smul]
      calc |χ x| * covectorEuclideanNorm ((ωs j : DifferentialForm (Eucl P) q) x)
          ≤ 1 * (ε / (μX + 1)) :=
            mul_le_mul (hχ1 x) (hj₀ j hj x) (covectorEuclideanNorm_nonneg _) zero_le_one
        _ = ε / (μX + 1) := one_mul _
    -- The mass estimate gives `|Y(ω_j)| ≤ δ · M(X) < ε`.
    have hY := Submission.br_la_abs_apply_le_mul_mass P q U X (L (ωs j)) _ hδ hbound hX
    change |X (L (ωs j))| < ε
    calc |X (L (ωs j))| ≤ ε / (μX + 1) * μX := hY
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  · -- `L ω = η` whenever `η = χ ω` pointwise.
    intro ω η hη
    change X (L ω) = X η
    congr 1
    exact Subtype.ext (funext fun x => by rw [hL, hη])

/-- **Mass does not drop under restriction near the support (Simon Ch. 6, 2.4–2.5).**  If
`Z ∈ 𝒟_q(ℝ^P)` vanishes on every test form whose support misses a compact `K ⊆ U` (`U` open),
then `M(Z) ≤ M(Z|_U)` for `Z|_U = Z.restrictDomain`.  With a cutoff `χ` (`0 ≤ χ ≤ 1`,
`tsupport χ ⊆ U`, `χ = 1` on an open `N ⊇ K`), every `ω` admissible for `M(Z)` gives the form
`χ ω ∈ 𝒟^q(U)`, admissible for `M(Z|_U)` as `|χ ω| = χ |ω| ≤ 1`, and `χ ω = ω` on `N`, so
`Z(ω) = Z(χ ω) = Z|_U(χ ω) ≤ M(Z|_U)`. -/
theorem Submission.fiw_tb_ext_mass_le_restrictDomain : ∀ (P q : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) q, (∀ ω : TestFormOn (univ : Set (Eucl P)) q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → Z.mass ≤ (Z.restrictDomain (subset_univ U)).mass := by
  intro P q U K hU hK hKU Z hZ
  obtain ⟨χ, N, hχ, hχ01, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  -- `L ω = χ ω`, a test form in `U`.
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q univ U χ hχ hχU
  -- `M(Z)` is the supremum of `Z(ω)` over the admissible `ω`.
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  have hadm : L ω ∈ massAdmissibleOn U q U := by
    refine ⟨(L ω).property.2, fun x => ?_⟩
    rw [hL, Submission.fiw_tb_ext_covectorNorm_smul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hω.2 x)
  -- `L ω = ω` on `N ⊇ K`, so `Z` cannot tell them apart.
  have hval : Z ω = Z.restrictDomain (subset_univ U) (L ω) := by
    rw [GeometricCurrentOn.restrictDomain_apply]
    refine (Submission.fiw_tb_ext_apply_eq_of_eqOn P q univ K N Z hN hKN hZ ω
      (testFormOnInclusion (subset_univ U) q (L ω)) fun x hx => ?_).symm
    rw [testFormOnInclusion_coe, hL, hχN x hx, one_smul]
  show ENNReal.ofReal (Z ω) ≤ _
  rw [hval]
  exact (Z.restrictDomain (subset_univ U)).le_massOn hadm
/-- **Integrality of the extension (Lemma B of the extension step in the proof of Simon Ch. 6,
Theorem 7.2).**  Let `U` be open, `K ⊆ U` compact and `Z ∈ 𝒟_q(ℝ^P)` vanish on test forms whose
support misses `K`.  If `Z|_U = τ(M, θ, ξ)` is integer multiplicity in `U`, then
`Z = τ(M ∩ K, θ, ξ)` is integer multiplicity in `ℝ^P`.  As `spt Z|_U ⊆ K`
(`fiw_tb_ext_support_subset`), `H^q(M ∖ K) = 0` (`lpf_rectifiable_support_null`), so
`(M ∩ K, θ, ξ)` is a rectifiable triple whose tangent spaces are those of `(M, θ)`
(`br_weightedTangent_congr`).  For `χ ∈ C_c^∞(U)` with `χ = 1` on an open `N ⊇ K`
(`fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`),
`Z(ω) = Z|_U(χ ω) = ∫_M θ ⟨χ ω, ξ⟩ dH^q = ∫_{M ∩ K} θ ⟨ω, ξ⟩ dH^q`. -/
theorem Submission.fiw_tb_ext_isIntegerMultiplicity : ∀ (P q : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) q, (∀ ω : TestFormOn (univ : Set (Eucl P)) q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → IsIntegerMultiplicity (Z.restrictDomain (subset_univ U)) → IsIntegerMultiplicity Z := by
  intro P q U K hU hK hKU Z hZ hIM
  obtain ⟨M, θ, ξ, htri, hθN, hrep⟩ := hIM
  -- (B1) `Z|_U` vanishes on test forms supported away from `K`, so `spt Z|_U ⊆ K`.
  have hZUv : ∀ ω : TestFormOn U q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K →
      (Z.restrictDomain (subset_univ U)) ω = 0 := fun ω hω => hZ _ hω
  have hsptU : (Z.restrictDomain (subset_univ U)).support ⊆ K :=
    Submission.fiw_tb_ext_support_subset P q U K _ hU hK.isClosed hZUv
  -- (B2) `H^q(M ∖ K) = 0`, hence `H^q ⌞ (M ∩ K) = H^q ⌞ M` and `H^q(M ∆ (M ∩ K)) = 0`.
  have hnull : (μHE[q] : Measure (Eucl P)) (M \ K) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hsptU)
      (Submission.lpf_rectifiable_support_null P q U _ M θ ξ htri hrep)
  have hae : (M ∩ K : Set (Eucl P)) =ᵐ[(μHE[q] : Measure (Eucl P))] M := by
    rw [ae_eq_set]
    constructor
    · exact measure_mono_null (fun x hx => (hx.2 hx.1.1).elim) measure_empty
    · simpa [sdiff_inter_self_eq_sdiff] using hnull
  have hrestr : (μHE[q] : Measure (Eucl P)).restrict (M ∩ K) =
      (μHE[q] : Measure (Eucl P)).restrict M := Measure.restrict_congr_set hae
  have hsymm : (μHE[q] : Measure (Eucl P)) (symmDiff M (M ∩ K) ∩ univ) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hnull
    rcases hx.1 with ⟨hxM, hxMK⟩ | ⟨hxMK, hxM⟩
    · exact ⟨hxM, fun hxK => hxMK ⟨hxM, hxK⟩⟩
    · exact absurd hxMK.1 hxM
  -- (B3)–(B4) `(M ∩ K, θ, ξ)` is a rectifiable triple in `ℝ^P`: `θ` is integrable on `M ∩ K`
  -- as `K ⊆ U` is compact, and the frames `τ` of `(M, θ)` still orient `(M ∩ K, θ)`.
  have htri' : IsRectifiableTriple (univ : Set (Eucl P)) q (M ∩ K) θ ξ :=
    { subset := subset_univ _
      nullMeasurableSet := htri.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
      countablyRectifiable := htri.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => htri.pos x hx.1
      integrableOn := fun K'' _ _ =>
        (htri.integrableOn K hK hKU).mono_set inter_subset_left
      aestronglyMeasurable := by rw [hrestr]; exact htri.aestronglyMeasurable
      orients := by
        rw [hrestr]
        filter_upwards [htri.orients] with x hx
        obtain ⟨τ, hτ, htan, hξ⟩ := hx
        exact ⟨τ, hτ, Submission.br_weightedTangent_congr P q M (M ∩ K) θ θ x univ isOpen_univ
          (mem_univ x) hsymm (ae_of_all _ fun _ => rfl) rfl _ htan, hξ⟩ }
  refine ⟨M ∩ K, θ, ξ, htri', fun x hx => hθN x hx.1, fun ω => ?_⟩
  -- (B5) A cutoff `χ ∈ C_c^∞(U)` with `χ = 1` on an open `N ⊇ K`; `Z(ω) = Z(χ ω)` as `χ ω = ω`
  -- on `N`, and `χ = 1` on `M ∩ K`.
  obtain ⟨χ, N, hχs, -, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q (univ : Set (Eucl P)) U χ hχs hχU
  have h1 : Z ω = Z (testFormOnInclusion (subset_univ U) q (L ω)) :=
    (Submission.fiw_tb_ext_apply_eq_of_eqOn P q univ K N Z hN hKN hZ ω _ (fun x hx => by
      change (L ω : DifferentialForm (Eucl P) q) x = _
      rw [hL, hχN x hx, one_smul])).symm
  rw [h1, ← GeometricCurrentOn.restrictDomain_apply, hrep]
  unfold tauAction
  rw [← hrestr]
  apply setIntegral_congr_fun₀ htri'.nullMeasurableSet
  intro x hx
  change θ x * ξ x ((L ω : DifferentialForm (Eucl P) q) x) = _
  rw [hL, hχN x (hKN hx.2), one_smul]
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
/-- A translation estimate `∫ |u(x + h) − u(x)| dx ≤ ‖h‖ Λ` bounds the double integral over
`r`-balls: `∫_x ∫_{closedBall(x, r)} |u(x) − u(y)| dy dx ≤ r Λ |closedBall(0, r)|`.
Substituting `y = x + h` turns the inner integral into `∫ 1_B(h) |u(x + h) − u(x)| dh` with
`B = closedBall(0, r)`; Tonelli swaps the integrals, and on `B` the hypothesis and `‖h‖ ≤ r`
bound the inner `x`-integral by `r Λ`. -/
theorem Submission.fiw_tb_tda_ps_translation_ball :
    ∀ (n : ℕ) (u : Eucl n → ℝ) (Λ : ℝ≥0∞) (r : ℝ), Measurable u →
      (∀ h : Eucl n, ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| ≤
        ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r) := by
  intro n u Λ r hu hΛ
  set B : Set (Eucl n) := closedBall 0 r
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- `x + h ∈ closedBall x r ↔ h ∈ closedBall 0 r`.
  have hmem : ∀ x h : Eucl n, x + h ∈ closedBall x r ↔ h ∈ B := by
    intro x h
    simp [B, mem_closedBall, dist_eq_norm]
  -- Substituting `y = x + h` in the inner integral.
  have hsub : ∀ x : Eucl n, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| =
      ∫⁻ h, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| := by
    intro x
    rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_left_eq_self
      ((closedBall x r).indicator fun y => ENNReal.ofReal |u x - u y|) x]
    refine lintegral_congr fun h => ?_
    by_cases hh : h ∈ B
    · rw [indicator_of_mem ((hmem x h).2 hh), indicator_of_mem hh, Pi.one_apply, one_mul,
        abs_sub_comm]
    · rw [indicator_of_notMem (fun h' => hh ((hmem x h).1 h')), indicator_of_notMem hh, zero_mul]
  -- The integrand is jointly measurable.
  have hk : Measurable fun p : Eucl n × Eucl n =>
      B.indicator 1 p.2 * ENNReal.ofReal |u (p.1 + p.2) - u p.1| :=
    ((measurable_one.indicator hBm).comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp ((hu.comp measurable_add).sub (hu.comp measurable_fst))))
  calc ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y|
      = ∫⁻ x, ∫⁻ h, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_congr fun x => hsub x
    _ = ∫⁻ h, ∫⁻ x, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_lintegral_swap hk.aemeasurable
    _ = ∫⁻ h, B.indicator 1 h * ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_congr fun h => lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp ((hu.comp (measurable_add_const h)).sub hu)))
    _ ≤ ∫⁻ h, B.indicator (fun _ => ENNReal.ofReal r * Λ) h := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ B
        · rw [indicator_of_mem hh, indicator_of_mem hh, Pi.one_apply, one_mul]
          refine (hΛ h).trans ?_
          gcongr
          exact mem_closedBall_zero_iff.1 hh
        · rw [indicator_of_notMem hh, indicator_of_notMem hh, zero_mul]
    _ = ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r) :=
        lintegral_indicator_const hBm _
/-- Box bound for the volume of a Euclidean ball, used in `fiw_tb_tda_poincare_sum`:
`closedBall(0, r) ⊆ [-r, r]ⁿ`, hence `Lⁿ(closedBall(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_ps_ball_volume_le : ∀ (n : ℕ) (r : ℝ), 0 ≤ r → volume (closedBall (0 : Eucl n) r) ≤ ENNReal.ofReal ((2 * r) ^ n) := by
  intro n r hr
  -- Steps 1–2: `|xᵢ| ≤ ‖x‖ ≤ r`, so `closedBall(0, r) ⊆ ofLp⁻¹(Icc(-r, r))`.
  have hsub : closedBall (0 : Eucl n) r ⊆
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => -r) (fun _ : Fin n => r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    have hcoord : ∀ i, |x i| ≤ r := fun i => by
      have h := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h
      exact h.trans hx
    exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
  -- Steps 3–4: `ofLp` preserves volume, and the box has volume `ofReal (2r) ^ n = ofReal ((2r)ⁿ)`.
  calc volume (closedBall (0 : Eucl n) r)
      ≤ volume (WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => -r) (fun _ : Fin n => r)) :=
        measure_mono hsub
    _ = volume (Icc (fun _ : Fin n => -r) (fun _ : Fin n => r)) :=
        (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ENNReal.ofReal ((2 * r) ^ n) := by
        rw [Real.volume_Icc_pi, ENNReal.ofReal_pow (by linarith)]
        simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, two_mul]
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
/-- Simon Ch. 6, (2.7) with `μ = Lⁿ` (`n = m + 1`): an integrable density `v` on `ℝⁿ` defines
the top-dimensional current `ω ↦ ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` in `𝒟ₙ(ℝⁿ)`.  Since `‖eᵢ‖ = 1`,
`|⟨ω(x), e₁ ∧ ⋯ ∧ eₙ⟩| ≤ ‖ω(x)‖`, so the integrand is dominated by `(sup ‖ω‖)·|v|`; linearity is
`integral_add`/`integral_const_mul`, and for a null sequence `ω_j → 0` of test forms
`sup ‖ω_j‖ → 0`, whence `|T(ω_j)| ≤ sup ‖ω_j‖ · ∫ |v| → 0`. -/
theorem Submission.fiw_tb_tda_density_current : ∀ (m : ℕ) (v : Eucl (m + 1) → ℝ), Integrable v → ∃ T : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), T ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m v hv
  -- Step 1: `|α(e₁, …, eₙ)| ≤ ‖α‖` for every `n`-covector `α`, since `‖eᵢ‖ = 1`.
  have hcov : ∀ α : Covector (Eucl (m + 1)) (m + 1),
      ‖α (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖α‖ := by
    intro α
    calc ‖α (fun i => EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖α‖ * ∏ i, ‖(EuclideanSpace.single i (1 : ℝ) : Eucl (m + 1))‖ := α.le_opNorm _
      _ = ‖α‖ := by simp
  -- Step 2: if `η` is continuous with `‖η‖ ≤ B`, then `v · η(e)` is integrable and
  -- `|∫ v η(e)| ≤ B ∫ |v|`.
  have hkey : ∀ (η : Eucl (m + 1) → Covector (Eucl (m + 1)) (m + 1)) (B : ℝ),
      Continuous η → (∀ x, ‖η x‖ ≤ B) →
      Integrable (fun x => v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))) ∧
        ‖∫ x, v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ B * ∫ x, ‖v x‖ := by
    intro η B hη hB
    have hbd : ∀ x, ‖η x (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ B :=
      fun x => (hcov _).trans (hB x)
    have hbound : ∀ᵐ x, ‖v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ B * ‖v x‖ :=
      Eventually.of_forall fun x => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _)
    refine ⟨hv.mul_bdd (hη.eval_const _).aestronglyMeasurable (Eventually.of_forall hbd), ?_⟩
    calc ‖∫ x, v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))‖
        ≤ ∫ x, B * ‖v x‖ := norm_integral_le_of_norm_le (hv.norm.const_mul B) hbound
      _ = B * ∫ x, ‖v x‖ := integral_const_mul B _
  -- Step 3: the integrand of every test form is integrable.
  have hintω : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1),
      Integrable (fun x => v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ))) := by
    intro ω
    have hcont : Continuous (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
      ContDiff.continuous ω.property.1.1
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support ω.property.1.2
    exact (hkey _ B hcont hB).1
  -- Step 4: the linear functional `ω ↦ ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.
  let T₀ : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ))
      map_add' := by
        intro ω₁ ω₂
        simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add]
        exact integral_add (hintω ω₁) (hintω ω₂)
      map_smul' := by
        intro c ω
        simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul, RingHom.id_apply, mul_left_comm (v _) c]
        exact integral_const_mul c _ }
  -- Step 5: sequential continuity at `0`, from uniform convergence of the forms themselves.
  refine ⟨⟨T₀, ?_⟩, fun ω => rfl⟩
  intro ωs hconv
  obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
  set I := ∫ x, ‖v x‖
  have hI0 : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  have h0 := Metric.tendstoUniformlyOn_iff.1 (hunif 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
  filter_upwards [h0 _ hδ] with j hj
  have hBj : ∀ y, ‖(ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) y‖ ≤ ε / (I + 1) := by
    intro y
    by_cases hy : y ∈ K
    · have h1 := hj y hy
      have h2 : iteratedFDeriv ℝ 0
          ((0 : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) :
            DifferentialForm (Eucl (m + 1)) (m + 1)) y = 0 := by
        rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
        simp
      rw [h2, dist_zero_left, norm_iteratedFDeriv_zero] at h1
      exact h1.le
    · rw [image_eq_zero_of_notMem_tsupport fun hy' => hy (hsupp j hy'), norm_zero]
      exact hδ.le
  have hcont : Continuous (ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
    ContDiff.continuous (ωs j).property.1.1
  have hle := (hkey _ _ hcont hBj).2
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith
/-- A top-dimensional current with an integrable integer density `v` that is locally constant
where it is nonzero is integer multiplicity (Simon Ch. 6, 3.1):
`T(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ = τ(M, θ, ξ)(ω)` with `M = {v ≠ 0}` (open), `θ = |v|` and
`ξ = ±e₁ ∧ ⋯ ∧ eₙ` according to the sign of `v`.  Near each `x ∈ M` the multiplicity `θ` is
constant, so the weighted blow-up integrals of Ch. 3, 1.7 are eventually equal to `θ(x) ∫ f dLⁿ`
and the approximate tangent space is `ℝⁿ = span(e)`. -/
theorem Submission.fiw_tb_tda_locally_constant_im : ∀ (m : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (v : Eucl (m + 1) → ℝ), Measurable v → Integrable v → (∀ x, ∃ k : ℤ, v x = k) → (∀ x, v x ≠ 0 → ∀ᶠ y in 𝓝 x, v y = v x) → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), T ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → IsIntegerMultiplicity T := by
  intro m T v hvm hvi hvZ hvloc hT
  -- Notation: `e = (e₀, …, e_m)`, `M = {v ≠ 0}`, `θ = |v|`, `ξ = ±e₀ ∧ ⋯ ∧ e_m` (`+` iff `v > 0`).
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ)
  set M : Set (Eucl (m + 1)) := {x | v x ≠ 0}
  set θ : Eucl (m + 1) → ℝ := fun x => |v x|
  set ξ : Eucl (m + 1) → NVector (Eucl (m + 1)) (m + 1) :=
    fun x => if 0 < v x then simpleNVector e else -simpleNVector e
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  -- Step 2: `M` is open (local constancy of `v` where `v ≠ 0`), hence measurable.
  have hMopen : IsOpen M := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hvloc x hx] with y hy
    show v y ≠ 0
    rw [hy]
    exact hx
  have hMmeas : MeasurableSet M := hMopen.measurableSet
  -- Step 1: `θ(x) ⟨α, ξ(x)⟩ = v(x) α(e)` for every covector `α`.
  have hθξ : ∀ x (α : Covector (Eucl (m + 1)) (m + 1)), θ x * ξ x α = v x * α e := by
    intro x α
    by_cases hpos : 0 < v x
    · simp [θ, ξ, hpos, abs_of_pos hpos]
    · simp [θ, ξ, hpos, abs_of_nonpos (not_lt.mp hpos)]
  -- Step 4: the weighted approximate tangent space at `x ∈ M` is `ℝⁿ`.
  have htan : ∀ x ∈ M, HasWeightedApproximateTangentSpaceAt (m + 1) M θ x ⊤ := by
    intro x hx
    refine ⟨by rw [finrank_top, finrank_euclideanSpace_fin], fun f => ?_⟩
    -- `v = v(x)` on `B(x, δ)`, and `spt f ⊆ B̄(0, R)`.
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hvloc x hx)
    obtain ⟨R, hR, hRsupp⟩ :=
      f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Eucl (m + 1))
    -- For `0 < r < δ / (R + 1)` and `f(y) ≠ 0`: `x + r y ∈ B(x, δ) ⊆ M`, so
    -- `y = η_{x,r}(x + r y) ∈ η_{x,r}(M)` and `θ(x + r y) = θ(x)`.
    have hsmall : ∀ r ∈ Ioo (0 : ℝ) (δ / (R + 1)), ∀ y, f y ≠ 0 →
        y ∈ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∧ θ (x + r • y) = θ x := by
      intro r hr y hy
      have hyR : ‖y‖ ≤ R := by
        simpa using hRsupp (subset_tsupport _ hy)
      have hdist : dist (x + r • y) x < δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
        calc r * ‖y‖ ≤ r * (R + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.1.le
          _ < δ := (lt_div_iff₀ (by linarith)).mp hr.2
      have hv : v (x + r • y) = v x := hball hdist
      refine ⟨⟨x + r • y, ?_, ?_⟩, ?_⟩
      · show v (x + r • y) ≠ 0
        rw [hv]
        exact hx
      · simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hr.1.ne']
      · simp [θ, hv]
    -- Hence the blow-up integral equals `θ(x) ∫ f dHⁿ` for all such `r`.
    have hconst : ∀ r ∈ Ioo (0 : ℝ) (δ / (R + 1)),
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y * θ (x + r • y)
            ∂(μHE[m + 1] : Measure (Eucl (m + 1))) =
          θ x * ∫ y in ((⊤ : Submodule ℝ (Eucl (m + 1))) : Set (Eucl (m + 1))), f y
            ∂(μHE[m + 1] : Measure (Eucl (m + 1))) := by
      intro r hr
      rw [Submodule.top_coe, Measure.restrict_univ, setIntegral_eq_integral_of_forall_compl_eq_zero,
        ← integral_const_mul]
      · congr 1
        funext y
        by_cases hy : f y = 0
        · simp [hy]
        · rw [(hsmall r hr y hy).2, mul_comm]
      · intro y hy
        by_cases hfy : f y = 0
        · simp [hfy]
        · exact absurd (hsmall r hr y hfy).1 hy
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ (by linarith : (0 : ℝ) < R + 1))] with r hr
    exact (hconst r hr).symm
  -- `span(range e) = ℝⁿ`.
  have hspan : Submodule.span ℝ (range e) = ⊤ := by
    have h := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.span_eq
    have hcoe : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis = e := by
      funext i
      simp [e]
    rwa [hcoe] at h
  refine ⟨M, θ, ξ, ⟨subset_univ M, hMmeas.nullMeasurableSet, ?_, fun x hx => abs_pos.mpr hx,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- Step 3: `M ⊆ range id` is countably `n`-rectifiable.
    exact (Poincare.SimonGMT.Chapter03.countablyRectifiable_range
      (LipschitzWith.id : LipschitzWith 1 (id : Eucl (m + 1) → Eucl (m + 1)))).mono
      (by rw [range_id]; exact subset_univ M)
  · -- `θ = |v|` is integrable.
    intro K _ _
    rw [hvol]
    exact hvi.abs.integrableOn
  · -- `ξ` is constant on `{v > 0}` and on its complement.
    exact (StronglyMeasurable.ite (measurableSet_lt measurable_const hvm)
      stronglyMeasurable_const stronglyMeasurable_const).aestronglyMeasurable
  · -- Orientation by the orthonormal frame `e` of `TₓM = ℝⁿ`, at every `x ∈ M`.
    refine ae_restrict_of_forall_mem hMmeas fun x hx =>
      ⟨e, EuclideanSpace.orthonormal_single, ?_, ?_⟩
    · rw [hspan]
      exact htan x hx
    · by_cases hpos : 0 < v x
      · left
        simp [ξ, hpos]
      · right
        simp [ξ, hpos]
  · -- `θ = |v|` is natural-valued.
    intro x _
    obtain ⟨k, hk⟩ := hvZ x
    exact ⟨k.natAbs, by rw [Nat.cast_natAbs, Int.cast_abs, ← hk]⟩
  · -- Step 5: `τ(M, θ, ξ)(ω) = ∫_M v ω_e dLⁿ = ∫ v ω_e dLⁿ = T(ω)`.
    intro ω
    rw [hT ω]
    unfold tauAction
    rw [hvol]
    simp_rw [hθξ]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have hx0 : v x = 0 := by
      by_contra h
      exact hx h
    simp [hx0]
/-- **Top-dimensional lattice chains** (Simon Ch. 6, proof of 5.1, (29) and (34), in `ℝⁿ` with
`n = m + 1`).  If `β_F ∈ ℤ` and `∑_F |β_F| ρⁿ < ∞`, let `v = ∑_F β_F 1_{F̊}`, i.e.
`v(x) = β(⌊x/ρ⌋, id)` when no coordinate of `x` lies in `ρℤ` and `v(x) = 0` otherwise.
Then `v` is integrable and integer-valued, `v = β_F` a.e. on each closed cube `F`, and `v` is
locally constant where it is nonzero.  The current `Pc(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` of
`fiw_tb_tda_density_current` is `∑_F β_F [[F]]` (split the integral over the cubes with
`fiw_tb_tda_lattice_cubes`) and is integer multiplicity by `fiw_tb_tda_locally_constant_im`. -/
theorem Submission.fiw_tb_tda_lattice_chain : ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ∀ β : LatticeFaceIndex (m + 1) (m + 1) → ℝ, (∀ F, ∃ k : ℤ, β F = k) → (∑' F, ENNReal.ofReal (|β F| * ρ ^ (m + 1))) < ∞ → ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (v : Eucl (m + 1) → ℝ), IsLatticeChain ρ β Pc ∧ IsIntegerMultiplicity Pc ∧ Integrable v ∧ (∀ F, ∀ᵐ x ∂((volume : Measure (Eucl (m + 1))).restrict (latticeFace ρ F)), v x = β F) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m ρ hρ β hβZ hβsum
  -- The cube toolkit: `F.2 = id`, `Q_F = ρ (F.1 + [0, 1]ⁿ)` has volume `ρⁿ`, a.e. point is
  -- good (no coordinate in `ρℤ`), and integrals split over the cubes.
  obtain ⟨hF2, hQ, hQmeas, hQvol, -, hgood, hlint, hint⟩ :=
    Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  have hcoord : ∀ i : Fin (m + 1), Continuous fun x : Eucl (m + 1) => x i := fun i => by
    fun_prop
  -- Step 1: `v(x) = β(z(x), α₀)`, `z(x) = ⌊x/ρ⌋`, at good points `x ∈ G`; `v = 0` off `G`.
  let α₀ : SimonMultiIndex (m + 1) (m + 1) := RelEmbedding.refl _
  have hα₀ : ∀ F : LatticeFaceIndex (m + 1) (m + 1), F.2 = α₀ := fun F =>
    RelEmbedding.ext (hF2 F)
  let G : Set (Eucl (m + 1)) := {x | ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k}
  let z : Eucl (m + 1) → Fin (m + 1) → ℤ := fun x i => ⌊x i / ρ⌋
  let v : Eucl (m + 1) → ℝ := G.indicator fun x => β (z x, α₀)
  -- Step 2: `v` is measurable and integer-valued.
  have hGmeas : MeasurableSet G := by
    have hG : G = ⋂ (i : Fin (m + 1)) (k : ℤ), {x : Eucl (m + 1) | x i ≠ ρ * k} := by
      ext x
      simp only [G, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hG]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      (isOpen_ne_fun (hcoord i) continuous_const).measurableSet
  have hfloor : Measurable (Int.floor : ℝ → ℤ) := measurable_to_countable' fun k => by
    rw [Int.preimage_floor_singleton]
    exact measurableSet_Ico
  have hzmeas : Measurable z :=
    measurable_pi_iff.mpr fun i => hfloor.comp ((hcoord i).measurable.div_const ρ)
  have hvmeas : Measurable v :=
    ((measurable_of_countable fun w : Fin (m + 1) → ℤ => β (w, α₀)).comp hzmeas).indicator
      hGmeas
  have hvZ : ∀ x, ∃ k : ℤ, v x = k := by
    intro x
    by_cases hx : x ∈ G
    · obtain ⟨k, hk⟩ := hβZ (z x, α₀)
      exact ⟨k, (Set.indicator_of_mem hx _).trans hk⟩
    · exact ⟨0, (Set.indicator_of_notMem hx _).trans Int.cast_zero.symm⟩
  -- Step 3: at good points of the closed cube `Q_F`, `⌊x/ρ⌋ = F.1`; so `v = β_F` a.e. on `Q_F`.
  have hval : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (x : Eucl (m + 1)),
      x ∈ latticeFace ρ F → x ∈ G → v x = β F := by
    intro F x hxQ hxG
    rw [hQ F] at hxQ
    have hz : z x = F.1 := by
      funext i
      obtain ⟨h1, h2⟩ := hxQ i
      have h1' : ρ * (F.1 i : ℝ) < x i := lt_of_le_of_ne h1 fun h => hxG i (F.1 i) h.symm
      have h2' : x i < ρ * ((F.1 i : ℝ) + 1) := lt_of_le_of_ne h2 fun h =>
        hxG i (F.1 i + 1) (by rw [h, Int.cast_add, Int.cast_one])
      show ⌊x i / ρ⌋ = F.1 i
      rw [Int.floor_eq_iff, le_div_iff₀ hρ, div_lt_iff₀ hρ]
      constructor <;> linarith
    exact (Set.indicator_of_mem hxG _).trans (congrArg β (Prod.ext hz (hα₀ F).symm))
  have hae : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∀ᵐ x ∂((volume : Measure (Eucl (m + 1))).restrict (latticeFace ρ F)), v x = β F := by
    intro F
    filter_upwards [ae_restrict_mem (hQmeas F), ae_restrict_of_ae hgood] with x hxQ hxG
    exact hval F x hxQ hxG
  -- Step 4: if `v(x) ≠ 0`, `v` is constant on the open cube `∏ᵢ (ρ zᵢ, ρ (zᵢ + 1)) ∋ x`.
  have hloc : ∀ x, v x ≠ 0 → ∀ᶠ y in 𝓝 x, v y = v x := by
    intro x hx
    have hxG : x ∈ G := by
      by_contra hxG
      exact hx (Set.indicator_of_notMem hxG _)
    have hO : IsOpen {y : Eucl (m + 1) |
        ∀ i, ρ * (z x i : ℝ) < y i ∧ y i < ρ * ((z x i : ℝ) + 1)} := by
      simp only [Set.ofPred_forall, Set.ofPred_and]
      exact isOpen_iInter_of_finite fun i =>
        (isOpen_lt continuous_const (hcoord i)).inter (isOpen_lt (hcoord i) continuous_const)
    have hxO : ∀ i, ρ * (z x i : ℝ) < x i ∧ x i < ρ * ((z x i : ℝ) + 1) := by
      intro i
      have h1 : ((z x i : ℤ) : ℝ) ≤ x i / ρ := Int.floor_le (x i / ρ)
      have h2 : x i / ρ < (z x i : ℝ) + 1 := Int.lt_floor_add_one (x i / ρ)
      rw [le_div_iff₀ hρ] at h1
      rw [div_lt_iff₀ hρ] at h2
      exact ⟨lt_of_le_of_ne (by linarith) fun h => hxG i (z x i) h.symm, by linarith⟩
    filter_upwards [hO.mem_nhds hxO] with y hy
    have hyz : z y = z x := by
      funext i
      obtain ⟨h1, h2⟩ := hy i
      show ⌊y i / ρ⌋ = z x i
      rw [Int.floor_eq_iff, le_div_iff₀ hρ, div_lt_iff₀ hρ]
      constructor <;> linarith
    have hyG : y ∈ G := by
      intro i k hk
      obtain ⟨h1, h2⟩ := hy i
      rw [hk] at h1 h2
      have h3 : z x i < k := by exact_mod_cast lt_of_mul_lt_mul_left h1 hρ.le
      have h4 : k < z x i + 1 := by exact_mod_cast lt_of_mul_lt_mul_left h2 hρ.le
      omega
    show G.indicator (fun x => β (z x, α₀)) y = G.indicator (fun x => β (z x, α₀)) x
    rw [Set.indicator_of_mem hyG, Set.indicator_of_mem hxG, hyz]
  -- Step 5: `∫ |v| = ∑_F |β_F| ρⁿ < ∞`, so `v ∈ L¹`.
  have hcube : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∫⁻ x in latticeFace ρ F, ‖v x‖ₑ = ENNReal.ofReal (|β F| * ρ ^ (m + 1)) := by
    intro F
    calc ∫⁻ x in latticeFace ρ F, ‖v x‖ₑ = ∫⁻ _ in latticeFace ρ F, ‖β F‖ₑ :=
          lintegral_congr_ae (by filter_upwards [hae F] with x hx; rw [hx])
      _ = ‖β F‖ₑ * volume (latticeFace ρ F) := setLIntegral_const _ _
      _ = ENNReal.ofReal (|β F| * ρ ^ (m + 1)) := by
          rw [hQvol F, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  have hvint : Integrable v := by
    refine ⟨hvmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hlint fun x => ‖v x‖ₑ, tsum_congr hcube]
    exact hβsum
  -- Step 6: the current `Pc(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.
  obtain ⟨Pc, hPc⟩ := Submission.fiw_tb_tda_density_current m v hvint
  -- Step 7: splitting `∫ v ω_e` over the cubes, where `v = β_F`, gives `∑_F β_F [[F]](ω)`.
  have hchain : IsLatticeChain ρ β Pc := by
    intro ω
    have hωcont : Continuous (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
      ContDiff.continuous ω.property.1.1
    have hωecont : Continuous fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      (continuous_eval_const _).comp hωcont
    have hωecs : HasCompactSupport fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      ω.property.1.2.comp_left (g := fun c : Covector (Eucl (m + 1)) (m + 1) =>
        c (fun i => EuclideanSpace.single i (1 : ℝ))) rfl
    obtain ⟨C, hC⟩ := hωecont.bounded_above_of_compact_support hωecs
    have hprod : Integrable fun x => v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      hvint.mul_bdd hωecont.aestronglyMeasurable (ae_of_all _ hC)
    rw [hPc ω, hint _ hprod]
    refine tsum_congr fun F => ?_
    rw [latticeFaceAction, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      ← integral_const_mul]
    simp only [hF2 F]
    exact integral_congr_ae (by filter_upwards [hae F] with x hx; rw [hx])
  -- Step 8: `v` is integer-valued and locally constant where nonzero, so `Pc` is integer
  -- multiplicity.
  exact ⟨Pc, v, hchain,
    Submission.fiw_tb_tda_locally_constant_im m Pc v hvmeas hvint hvZ hloc hPc, hvint, hae, hPc⟩
/-- **Difference of two top-dimensional density currents.**  On `ℝⁿ` (`n = m + 1`) let
`X(ω) = ∫ u ω_e dLⁿ` and `Pc(ω) = ∫ v ω_e dLⁿ` with `u, v ∈ L¹`, where
`ω_e(x) = ⟨ω(x), e₁ ∧ ⋯ ∧ eₙ⟩`.  Then `X − Pc` is a current `S` with `M(S) ≤ ∫ |u − v| dLⁿ`.
In top degree the Euclidean coefficient norm (Simon Ch. 6, 1.15 and Remark 2.6) of `ω(x)` is
`|ω_e(x)|`, so every form admissible for the mass (2.4) has `|ω_e| ≤ 1` and
`S(ω) = ∫ (u − v) ω_e dLⁿ ≤ ∫ |u − v| dLⁿ`. -/
theorem Submission.fiw_tb_tda_sub_mass : ∀ (m : ℕ) (X Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (u v : Eucl (m + 1) → ℝ), Integrable u → Integrable v → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → ∃ S : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), (∀ ω, X ω - Pc ω = S ω) ∧ S.mass ≤ ∫⁻ x, ENNReal.ofReal |u x - v x| := by
  intro m X Pc u v hu hv hX hPc
  classical
  -- Top degree: the only strictly monotone `I : Fin n → Fin n` is the identity, so the
  -- Euclidean coefficient norm of `α` is `|α(e₁, …, eₙ)|`.
  have hnorm : ∀ α : Covector (Eucl (m + 1)) (m + 1),
      covectorEuclideanNorm α = |α (fun i => EuclideanSpace.single i (1 : ℝ))| := by
    intro α
    unfold covectorEuclideanNorm
    rw [Finset.sum_eq_single (id : Fin (m + 1) → Fin (m + 1))]
    · rw [ite_eq_left strictMono_id]
      simp only [id, EuclideanSpace.basisFun_apply]
      exact Real.sqrt_sq_eq_abs _
    · intro I _ hI
      rw [ite_eq_right]
      intro h
      exact hI h.eq_id
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- `S = X − Pc`; its continuity is the difference of the continuity fields of `X` and `Pc`.
  refine ⟨⟨X.toCurrent - Pc.toCurrent, fun ωs h => by
    simpa using (X.continuous' ωs h).sub (Pc.continuous' ωs h)⟩, fun ω => rfl, ?_⟩
  unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
  refine sSup_le ?_
  rintro b ⟨ω, hω, rfl⟩
  -- For admissible `ω`, `ω_e` is continuous and `|ω_e| ≤ 1`.
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  set f : Eucl (m + 1) → ℝ := fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e with hf
  have hbd : ∀ x, |f x| ≤ 1 := fun x => by
    have := hω.2 x
    rwa [hnorm] at this
  have hωc : Continuous (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
    ω.property.1.1.continuous
  have hfc : Continuous f := hωc.eval_const e
  have hfm : AEStronglyMeasurable f volume := hfc.aestronglyMeasurable
  have hbd' : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ‖f x‖ ≤ 1 :=
    Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hbd x)
  have hu' : Integrable (fun x => u x * f x) := hu.mul_bdd hfm hbd'
  have hv' : Integrable (fun x => v x * f x) := hv.mul_bdd hfm hbd'
  have huv : Integrable (fun x => |u x - v x|) := (hu.sub hv).abs
  -- `S(ω) = ∫ (u − v) ω_e ≤ ∫ |u − v| |ω_e| ≤ ∫ |u − v|`.
  have key : (X.toCurrent - Pc.toCurrent) ω ≤ ∫ x, |u x - v x| := by
    rw [LinearMap.sub_apply]
    change X ω - Pc ω ≤ _
    rw [hX ω, hPc ω, ← integral_sub hu' hv']
    apply integral_mono (hu'.sub hv') huv
    intro x
    calc u x * f x - v x * f x = (u x - v x) * f x := by ring
      _ ≤ |(u x - v x) * f x| := le_abs_self _
      _ = |u x - v x| * |f x| := abs_mul _ _
      _ ≤ |u x - v x| * 1 := mul_le_mul_of_nonneg_left (hbd x) (abs_nonneg _)
      _ = |u x - v x| := mul_one _
  calc ENNReal.ofReal ((X.toCurrent - Pc.toCurrent) ω)
      ≤ ENNReal.ofReal (∫ x, |u x - v x|) := ENNReal.ofReal_le_ofReal key
    _ = ∫⁻ x, ENNReal.ofReal |u x - v x| :=
      ofReal_integral_eq_lintegral_ofReal huv (Eventually.of_forall (fun x => abs_nonneg _))

/-- Summed Poincaré bound over the top-dimensional lattice cubes of `ℝⁿ`, `n = m + 1`, with
`c = (2√n)ⁿ √n`.  A cube lies in the closed ball of radius `√n ρ` about any of its points, so
summing over the a.e. partition into cubes bounds the left side by
`ρ⁻ⁿ ∫⁻ₓ ∫⁻_{B(x, √n ρ)} |u x - u y|`.  The translation estimate bounds this double integral by
`√n ρ Λ L(B(0, √n ρ))`, and `L(B(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_poincare_sum :
    ∀ m : ℕ, ∃ c : ℝ≥0, ∀ (ρ : ℝ), 0 < ρ → ∀ (u : Eucl (m + 1) → ℝ) (Λ : ℝ≥0∞), Measurable u →
      (∀ h : Eucl (m + 1), ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        c * ENNReal.ofReal ρ * Λ := by
  intro m
  -- `s = √n` and `c = (2s)ⁿ s`.
  obtain ⟨s, hs, hs_def⟩ : ∃ s : ℝ, 0 ≤ s ∧ Real.sqrt ((m + 1 : ℕ) : ℝ) = s :=
    ⟨_, Real.sqrt_nonneg _, rfl⟩
  have hC : 0 ≤ (2 * s) ^ (m + 1) * s := by positivity
  refine ⟨NNReal.mk ((2 * s) ^ (m + 1) * s) hC, fun ρ hρ u Λ hu hΛ => ?_⟩
  obtain ⟨-, -, hc, -, he, -, hg, -⟩ := Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  rw [hs_def] at he
  have hr : 0 ≤ s * ρ := mul_nonneg hs hρ.le
  -- Step 1: a cube lies in the closed ball of radius `s ρ` about any of its points.
  have hcube : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
    fun F => setLIntegral_mono' (hc F) fun x hx =>
      lintegral_mono_set fun y hy => mem_closedBall.2 (he F y hy x hx)
  -- Step 6 (arithmetic): `(ρⁿ)⁻¹ (s ρ) (2 s ρ)ⁿ = (2s)ⁿ s ρ`.
  have hinv : 0 ≤ (ρ ^ (m + 1))⁻¹ := by positivity
  have hconst : (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1) =
      (2 * s) ^ (m + 1) * s * ρ := by
    calc (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)
        = (2 * s) ^ (m + 1) * s * ρ * ((ρ ^ (m + 1))⁻¹ * ρ ^ (m + 1)) := by ring
      _ = (2 * s) ^ (m + 1) * s * ρ := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), mul_one]
  calc ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y|
      ≤ ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
        ENNReal.tsum_le_tsum fun F => by gcongr _ * ?_; exact hcube F
    -- Step 2: the cubes form an a.e. partition of `ℝⁿ`.
    _ = ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| := by
        rw [ENNReal.tsum_mul_left, hg]
    -- Steps 3–5: the translation estimate and the volume of the ball.
    _ ≤ ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          (ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1))) := by
        gcongr _ * ?_
        calc ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y|
            ≤ ENNReal.ofReal (s * ρ) * Λ * volume (closedBall (0 : Eucl (m + 1)) (s * ρ)) :=
              Submission.fiw_tb_tda_ps_translation_ball (m + 1) u Λ (s * ρ) hu hΛ
          _ ≤ ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1)) := by
              gcongr _ * ?_
              exact Submission.fiw_tb_tda_ps_ball_volume_le (m + 1) (s * ρ) hr
    -- Step 6: collect the constants.
    _ = ENNReal.ofReal ((ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)) * Λ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hinv hr), ENNReal.ofReal_mul hinv]
        ring
    _ = ENNReal.ofReal ((2 * s) ^ (m + 1) * s) * ENNReal.ofReal ρ * Λ := by
        rw [hconst, ENNReal.ofReal_mul hC]
    _ = _ := by rw [ENNReal.ofReal_eq_coe_nnreal hC]
/-- Simon Ch. 6, 2.11: a current kills every test form whose support misses `spt T`.
`tsupport ω` is a compact subset of the zero region, so finitely many open `W ⊂⊂ U` on which `T`
vanishes cover it, and a smooth partition of unity `ψᵢ` on `tsupport ω` subordinate to them
splits `ω = ∑ᵢ ψᵢ ω` into test forms supported in those `W`. -/
theorem Submission.fiw_tb_apply_eq_zero_of_disjoint_support :
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

/-- **A rectifiable representation lives on the support (Simon Ch. 6, proof of 7.2, (G2)).**
Under the mass formula `M_W(T) = ∫_{M ∩ W} θ dHⁿ` (MF), `T = τ(M, θ, ξ)` has `Hⁿ(M ∖ spt T) = 0`.
Let `V = U ∩ Z`, `Z` the zero region of `T`.  An admissible form for `M_V(T)` is supported in
`V ⊆ Z`, which misses `spt T = U ∖ Z`, so `T` kills it (`fiw_tb_apply_eq_zero_of_disjoint_support`):
`M_V(T) = 0`, and `∫_{M ∩ V} θ dHⁿ = 0` by MF.  For compact `K ⊆ U`, `θ` is integrable on `M ∩ K`,
hence a.e.-measurable, and positive on `M`, so `Hⁿ(M ∩ V ∩ K) = 0`.  The compact sets
`F i ∩ closedBall 0 j` (`F i ⊆ U` closed, `⋃ i, F i = U`) cover `M ∩ V ⊇ M ∖ spt T`. -/
theorem Submission.fiw_tb_rectifiable_support_null : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := by
  intro hMF P n U hU T M θ ξ hM hT
  -- `V = U ∩ Z` is open, and `M ∖ spt T ⊆ M ∩ V` since `M ⊆ U` and `spt T = U ∖ Z`.
  have hV : IsOpen (U ∩ T.zeroRegion) := hU.inter T.isOpen_zeroRegion
  have hsub : M \ T.support ⊆ M ∩ (U ∩ T.zeroRegion) := fun x hx =>
    ⟨hx.1, hM.subset hx.1, Classical.byContradiction fun hxZ => hx.2 ⟨hM.subset hx.1, hxZ⟩⟩
  -- `M_V(T) = 0`: an admissible form is supported in `V ⊆ Z`, which misses `spt T`.
  have hmass : T.massOn (U ∩ T.zeroRegion) = 0 := by
    refine nonpos_iff_eq_zero.1 (sSup_le ?_)
    rintro _ ⟨ω, hω, rfl⟩
    refine (ENNReal.ofReal_eq_zero.2 (le_of_eq ?_)).le
    exact Submission.fiw_tb_apply_eq_zero_of_disjoint_support P n U T ω
      (Set.disjoint_left.2 fun x hxω hxs => hxs.2 (hω.1 hxω).2)
  -- MF with `W = V`: `∫_{M ∩ V} θ dHⁿ = 0`.
  have hint : ∫⁻ x in M ∩ (U ∩ T.zeroRegion), ENNReal.ofReal (θ x)
      ∂(μHE[n] : Measure (Eucl P)) = 0 :=
    (hMF P n U hU T M θ ξ hM hT _ hV).symm.trans hmass
  -- `Hⁿ(M ∩ V ∩ K) = 0` for compact `K ⊆ U`: `θ` is a.e.-measurable there, so `θ = 0` a.e. on
  -- `M ∩ V ∩ K`, while `θ > 0` on `M`.
  have hnull : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      (μHE[n] : Measure (Eucl P)) (M ∩ (U ∩ T.zeroRegion) ∩ K) = 0 := by
    intro K hKc hKU
    have hθ : AEMeasurable (fun x => ENNReal.ofReal (θ x))
        ((μHE[n] : Measure (Eucl P)).restrict (M ∩ (U ∩ T.zeroRegion) ∩ K)) :=
      ((hM.integrableOn K hKc hKU).aestronglyMeasurable.aemeasurable.mono_set
        (fun x hx => ⟨hx.1.1, hx.2⟩ : M ∩ (U ∩ T.zeroRegion) ∩ K ⊆ M ∩ K)).ennreal_ofReal
    have hae := (lintegral_eq_zero_iff' hθ).1
      (nonpos_iff_eq_zero.1 ((lintegral_mono_set inter_subset_left).trans hint.le))
    have h0 : (μHE[n] : Measure (Eucl P)).restrict (M ∩ (U ∩ T.zeroRegion) ∩ K)
        (M ∩ (U ∩ T.zeroRegion) ∩ K) = 0 :=
      measure_mono_null (t := {x | ENNReal.ofReal (θ x) ≠ 0})
        (fun x hx => (ENNReal.ofReal_pos.2 (hM.pos x hx.1.1)).ne') (ae_iff.1 hae)
    rwa [Measure.restrict_apply_self] at h0
  -- The compact sets `F i ∩ closedBall 0 j ⊆ U` (`F i` closed, `⋃ i, F i = U`) cover `M ∩ V`.
  obtain ⟨F, hFc, hFU, hFeq, -⟩ := hU.exists_iUnion_isClosed
  refine measure_mono_null (hsub.trans fun x hx => ?_) (measure_iUnion_null fun k : ℕ × ℕ =>
    hnull _ ((isCompact_closedBall 0 k.2).inter_left (hFc k.1)) (inter_subset_left.trans (hFU k.1)))
  obtain ⟨i, hi⟩ := mem_iUnion.1 (by rw [hFeq]; exact hx.2.1 : x ∈ ⋃ i, F i)
  exact mem_iUnion.2 ⟨(i, ⌈‖x‖⌉₊), hx, hi, mem_closedBall_zero_iff.2 (Nat.le_ceil _)⟩
/-- Simon Ch. 6, 2.4–2.5 and 2.16: restricting `Y ∈ 𝒟ₖ(U)` to a smaller domain `W ⊆ U` does
not increase mass, `M(Y|_W) ≤ M(Y)`.  Every `ω` admissible for `M_W(Y|_W)`, regarded as the
test form `ιω` on `U` with the same underlying form, is admissible for `M_U(Y)`, and
`Y|_W(ω) = Y(ιω)`.  `W` need not be open. -/
theorem Submission.fiw_tb_ri_restrictDomain_mass_le :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U) (Y : GeometricCurrentOn U k),
      (Y.restrictDomain hWU).mass ≤ Y.mass := by
  intro P k U W hWU Y
  -- `(Y|_W).mass` is the supremum of `ofReal (Y|_W ω)` over `ω ∈ massAdmissibleOn W k W`.
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  -- `ιω` has the same underlying form as `ω`, so `tsupport ιω ⊆ W ⊆ U` and `|ιω(x)| ≤ 1`.
  exact Y.le_massOn (omega := testFormOnInclusion hWU k ω) ⟨hω.1.trans hWU, hω.2⟩
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

/-- Simon Ch. 6, 2.4, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of `Y ∈ 𝒟ₖ(U)` to an open
`W ⊆ U` has `M_W(Y|_W) ≤ M_U(Y)`, since every admissible form for `M_W` is admissible for `M_U`,
and it is integer multiplicity when `Y` is: `Y|_W = τ(M ∩ W, θ, ξ)` for `Y = τ(M, θ, ξ)`. -/
theorem Submission.fiw_tb_restrictDomain_mass_im :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U), IsOpen W →
      ∀ Y : GeometricCurrentOn U k, (Y.restrictDomain hWU).mass ≤ Y.mass ∧
        (IsIntegerMultiplicity Y → IsIntegerMultiplicity (Y.restrictDomain hWU)) := by
  intro P k U W hWU hW Y
  exact ⟨Submission.fiw_tb_ri_restrictDomain_mass_le P k U W hWU Y,
    Submission.br_restrictDomain_isIntegerMultiplicity P k U W hWU hW Y⟩

/-- **Extension of a compactly supported current to `ℝ^P` (Simon Ch. 6, proof of 7.2, (G3)).**
If `spt X ⊆ K` with `K ⊆ U` compact and `M(X) < ∞`, then `Y(ω) = X(χ ω)`, `χ` a smooth cutoff
with `tsupport χ ⊆ U` and `χ = 1` on an open `N ⊇ K`, is a current on `ℝ^P` (`fiw_tb_ext_cutoff`,
`fiw_tb_ext_cutoff_current`).  Since `X` kills test forms whose support misses `K`
(`fiw_tb_apply_eq_zero_of_disjoint_support`) and `χ ω = ω` on `N`, `Y|_U = X`
(`fiw_tb_ext_apply_eq_of_eqOn`); `Y` and `∂Y` kill test forms whose support misses `K`, as
`tsupport (χ ω) ⊆ tsupport ω` and `tsupport dω ⊆ tsupport ω`, and `(∂Y)|_U = ∂X`.  Support,
mass and integer multiplicity of `Y` and `∂Y` are then controlled by those of their restrictions
`X` and `∂X` (`fiw_tb_ext_support_subset`, `fiw_tb_ext_mass_le_restrictDomain`,
`fiw_tb_ext_isIntegerMultiplicity`).  The mass formula (MF) is not needed. -/
theorem Submission.fiw_tb_extend_to_univ : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P m : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ X : GeometricCurrentOn U (m + 1), X.support ⊆ K → X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧ (IsIntegerMultiplicity X.boundary → IsIntegerMultiplicity Y.boundary) := by
  intro _hMF P m U K hU hK hKU X hXK hXm
  -- (V) for `X`: as `spt X ⊆ K`, `X` kills every test form whose support misses `K`.
  have hXv : ∀ ω : TestFormOn U (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) K → X ω = 0 := fun ω hω =>
    Submission.fiw_tb_apply_eq_zero_of_disjoint_support P (m + 1) U X ω (hω.mono_right hXK)
  -- The cutoff `χ` and multiplication by `χ`, from test forms on `ℝ^P` and on `U` to `U`.
  obtain ⟨χ, N, hχ, hχ01, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P (m + 1) univ U χ hχ hχU
  obtain ⟨LU, hLU⟩ := Submission.fiw_tb_ext_smul_testForm P (m + 1) U U χ hχ hχU
  -- `Y(ω) = X(χ ω)` is a current on `ℝ^P`, since `M(X) < ∞` and `|χ| ≤ 1`.
  obtain ⟨Y, hY⟩ := Submission.fiw_tb_ext_cutoff_current P (m + 1) U χ hχ hχU
    (fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩) X hXm
  -- `Y|_U = X`: `Y(ω) = X(χ ω) = X(ω)`, as `χ ω = ω` on `N ⊇ K`.
  have hres : Y.restrictDomain (subset_univ U) = X := by
    ext ω
    rw [GeometricCurrentOn.restrictDomain_apply,
      hY (testFormOnInclusion (subset_univ U) (m + 1) ω) (LU ω) (hLU ω)]
    exact Submission.fiw_tb_ext_apply_eq_of_eqOn P (m + 1) U K N X hN hKN hXv ω (LU ω)
      fun x hx => by rw [hLU, hχN x hx, one_smul]
  -- (V) for `Y`: `Y(ω) = X(χ ω)` and `tsupport (χ ω) ⊆ tsupport ω`.
  have hYv : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) K → Y ω = 0 := by
    intro ω hω
    rw [hY ω (L ω) (hL ω)]
    refine hXv (L ω) (hω.mono_left ?_)
    rw [show (L ω : DifferentialForm (Eucl P) (m + 1)) =
      fun x => χ x • (ω : DifferentialForm (Eucl P) (m + 1)) x from funext (hL ω)]
    exact tsupport_smul_subset_right _ _
  -- (V) for `∂Y`, as `tsupport dω ⊆ tsupport ω`; and `(∂Y)|_U = ∂X`, as `d` commutes with the
  -- inclusion of test forms on `U` into test forms on `ℝ^P`.
  have hbYv : ∀ ω : TestFormOn (univ : Set (Eucl P)) m,
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) m)) K → Y.boundary ω = 0 := fun ω hω =>
    hYv _ (hω.mono_left (tsupport_exteriorDerivative_subset _))
  have hbres : Y.boundary.restrictDomain (subset_univ U) = X.boundary := by
    rw [← hres]
    rfl
  refine ⟨Y, hres, Submission.fiw_tb_ext_support_subset P (m + 1) univ K Y isOpen_univ
    hK.isClosed hYv, ?_, ?_, fun hX => ?_, fun hX => ?_⟩
  · -- `M(Y) ≤ M(Y|_U) = M(X)`.
    rw [← hres]
    exact Submission.fiw_tb_ext_mass_le_restrictDomain P (m + 1) U K hU hK hKU Y hYv
  · -- `M(∂Y) ≤ M((∂Y)|_U) = M(∂X)`.
    rw [← hbres]
    exact Submission.fiw_tb_ext_mass_le_restrictDomain P m U K hU hK hKU Y.boundary hbYv
  · rw [← hres] at hX
    exact Submission.fiw_tb_ext_isIntegerMultiplicity P (m + 1) U K hU hK hKU Y hYv hX
  · rw [← hbres] at hX
    exact Submission.fiw_tb_ext_isIntegerMultiplicity P m U K hU hK hKU Y.boundary hbYv hX
/-- The coordinate covector `dx^α = wedgeCovectors n (proj ∘ α)` on `ℝ^N` is dual to the
coordinate frames: `dx^α(e_α) = 1`, `dx^α(e_{α'}) = 0` for every other increasing multi-index
`α'`, and `covectorEuclideanNorm (c • dx^α) = |c|`. -/
theorem Submission.isoperimetric_coord_covector_eval : ∀ (n N : ℕ) (α : SimonMultiIndex n N), (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 1 ∧ (∀ α' : SimonMultiIndex n N, α' ≠ α → (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α' j) (1 : ℝ)) = 0) ∧ ∀ c : ℝ, covectorEuclideanNorm (c • (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n)) = |c| := by
  intro n N α
  classical
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) with hη
  -- Kronecker property on increasing coordinate frames: `dx^α(e_I) = δ_{α I}`.
  have hK : ∀ I : Fin n → Fin N, StrictMono I →
      η (fun j => EuclideanSpace.single (I j) (1 : ℝ)) = if I = ⇑α then 1 else 0 := by
    intro I hI
    rw [hη, wedgeCovectors_apply_det]
    split_ifs with hIα
    · -- the matrix `[δ_{α i, α j}]` is the identity
      subst hIα
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [Matrix.one_apply, PiLp.single_apply, α.injective.eq_iff]
    · -- some `α i` is not among the `I j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, α i ≠ I j := by
        by_contra! h
        apply hIα
        rw [← StrictMono.range_inj_of_wellFoundedLT hI α.strictMono]
        have hsub : Set.range α ⊆ Set.range I := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range I)).symm
        rw [Set.ncard_range_of_injective hI.injective, Set.ncard_range_of_injective α.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hK α α.strictMono
  · intro α' hα'
    rw [hK α' α'.strictMono, ite_eq_right fun h => hα' (DFunLike.coe_injective h)]
  · intro c
    -- only the summand `I = α` survives, and it contributes `c²`
    have hs : ∀ I : Fin n → Fin N, (if StrictMono I then
        ((c • η) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (I i))) ^ 2 else 0) =
        if I = ⇑α then c ^ 2 else 0 := by
      intro I
      by_cases hI : StrictMono I
      · rw [ite_eq_left hI]
        simp only [EuclideanSpace.basisFun_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        rw [hK I hI]
        split_ifs <;> ring
      · have hIα : I ≠ ⇑α := fun h => hI (h ▸ α.strictMono)
        rw [ite_eq_right hI, ite_eq_right hIα]
    rw [covectorEuclideanNorm, Finset.sum_congr rfl fun I _ => hs I, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _), Real.sqrt_sq_eq_abs]
/-- The `n`-dimensional coordinate box `{x : c_i + a ≤ x_i ≤ c_i + b (i ∈ range α), x_i = c_i
(i ∉ range α)}` in `ℝ^N` has `μHE[n]`-measure `(b - a)^n`.  The map
`ι(y)_i = c_i + ∑_j [α j = i] y_j` is an isometry `ℝⁿ → ℝ^N` carrying the cube `[a, b]ⁿ` onto the
box; `μHE[n]` is invariant under isometries and equals Lebesgue measure on `ℝⁿ`. -/
theorem Submission.isoperimetric_coord_box_measure :
    ∀ (n N : ℕ) (α : SimonMultiIndex n N) (c : Fin N → ℝ) (a b : ℝ), a ≤ b →
      (μHE[n] : Measure (Eucl N)) {x : Eucl N | ∀ i : Fin N,
        (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧ (i ∉ range α → x i = c i)} =
        ENNReal.ofReal ((b - a) ^ n) := by
  intro n N α c a b hab
  classical
  -- The parametrization `ι(y)_i = c_i + ∑_j [α j = i] y_j` of the box.
  set ι : EuclideanSpace ℝ (Fin n) → Eucl N :=
    fun y => WithLp.toLp 2 (fun i => c i + ∑ j, if α j = i then y j else 0) with hι
  have hι_on : ∀ y j, ι y (α j) = c (α j) + y j := by
    intro y j
    simp only [hι, PiLp.toLp_apply, α.inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hι_off : ∀ y i, i ∉ range α → ι y i = c i := by
    intro y i hi
    have hne : ∀ j, α j ≠ i := fun j hj => hi ⟨j, hj⟩
    simp [hι, hne]
  -- `ι` is an isometry: coordinates off `range α` agree, the others reindex along `α`.
  have hiso : Isometry ι := by
    refine Isometry.of_dist_eq fun y y' => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image α)) ?_,
      Finset.sum_image (fun j _ j' _ h => α.injective h)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hι_on, hι_on, dist_add_left]
    · intro i _ hi
      have hi' : i ∉ range α := by
        rintro ⟨j, rfl⟩
        exact hi (Finset.mem_image_of_mem α (Finset.mem_univ j))
      rw [hι_off y i hi', hι_off y' i hi', dist_self]
      ring
  -- `ι` maps the cube `[a, b]ⁿ` onto the box, with preimage `y_j = x_{α j} - c_{α j}`.
  have himage : ι '' {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      {x : Eucl N | ∀ i : Fin N, (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧
        (i ∉ range α → x i = c i)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨?_, hι_off y i⟩
      rintro ⟨j, rfl⟩
      rw [hι_on]
      exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
    · intro hx
      refine ⟨WithLp.toLp 2 (fun j => x (α j) - c (α j)), fun j => ?_, ?_⟩
      · have h := (hx (α j)).1 ⟨j, rfl⟩
        constructor <;> dsimp only <;> linarith [h.1, h.2]
      · ext i
        by_cases hi : i ∈ range α
        · obtain ⟨j, rfl⟩ := hi
          rw [hι_on]
          simp
        · rw [hι_off _ i hi, (hx i).2 hi]
  rw [← himage, hiso.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- The cube is the preimage of `Icc` under the volume-preserving `WithLp.ofLp`.
  have hQ : {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => a) (fun _ => b) := by
    ext y
    simp [Pi.le_def, forall_and]
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (sub_nonneg.2 hab)]
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Z) < ∞` and `|η(x)| ≤ c` everywhere (Euclidean
coefficient norm) with `c > 0`, then `|Z(η)| ≤ c · M(Z)`. -/
theorem Submission.fiw_tb_te_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U n) (η : TestFormOn U n) (c : ℝ),
      0 < c → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ c) →
      Z.mass ≠ ∞ → |Z η| ≤ c * Z.mass.toReal := by
  intro P n U Z η c hc hη hZ
  -- Homogeneity of the Euclidean coefficient norm: `|t β| = |t| |β|`.
  have hsmul : ∀ (t : ℝ) (β : Covector (Eucl P) n),
      covectorEuclideanNorm (t • β) = |t| * covectorEuclideanNorm β := by
    intro t β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image α)) ?_,
      Finset.sum_image (fun j _ j' _ h => α.injective h)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hι_on, hι_on, dist_add_left]
    · intro i _ hi
      have hi' : i ∉ range α := by
        rintro ⟨j, rfl⟩
        exact hi (Finset.mem_image_of_mem α (Finset.mem_univ j))
      rw [hι_off y i hi', hι_off y' i hi', dist_self]
      ring
  -- `ι` maps the cube `[a, b]ⁿ` onto the box, with preimage `y_j = x_{α j} - c_{α j}`.
  have himage : ι '' {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      {x : Eucl N | ∀ i : Fin N, (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧
        (i ∉ range α → x i = c i)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨?_, hι_off y i⟩
      rintro ⟨j, rfl⟩
      rw [hι_on]
      exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
    · intro hx
      refine ⟨WithLp.toLp 2 (fun j => x (α j) - c (α j)), fun j => ?_, ?_⟩
      · have h := (hx (α j)).1 ⟨j, rfl⟩
        constructor <;> dsimp only <;> linarith [h.1, h.2]
      · ext i
        by_cases hi : i ∈ range α
        · obtain ⟨j, rfl⟩ := hi
          rw [hι_on]
          simp
        · rw [hι_off _ i hi, (hx i).2 hi]
  rw [← himage, hiso.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- The cube is the preimage of `Icc` under the volume-preserving `WithLp.ofLp`.
  have hQ : {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => a) (fun _ => b) := by
    ext y
    simp [Pi.le_def, forall_and]
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (sub_nonneg.2 hab)]
/-- Smooth cut-off for a lattice face: for `ρ, δ > 0` there is a compactly supported smooth
`φ : ℝ^N → [0, 1]` equal to `1` on the shrunken face
`{x : ρ(zᵢ + δ) ≤ xᵢ ≤ ρ(zᵢ + 1 − δ) (i ∈ α), xᵢ = ρ zᵢ (i ∉ α)}` and vanishing on every other
lattice face `ρ (z' + F_α)`, `z' ≠ z`, of the same direction `α`. -/
theorem Submission.isoperimetric_lattice_face_cutoff :
    ∀ (n N : ℕ) (ρ δ : ℝ) (z : Fin N → ℤ) (α : SimonMultiIndex n N), 0 < ρ → 0 < δ →
      ∃ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x : Eucl N, (∀ i : Fin N,
          (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
          (i ∉ range α → x i = ρ * (z i : ℝ))) → φ x = 1) ∧
        ∀ z' : Fin N → ℤ, z' ≠ z → ∀ x ∈ latticeFace ρ ((z', α) : LatticeFaceIndex n N),
          φ x = 0 := by
  intro n N ρ δ z α hρ hδ
  -- `K`: the shrunken face; `L ⊇ O ⊇ K`: a closed and an open enlarged box (margins `ρδ/2`
  -- along `range α`, transversal slab of half-width `ρ/2`).
  set K : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
    (i ∉ range α → x i = ρ * (z i : ℝ))} with hK
  set L : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ / 2) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ / 2)) ∧
    (i ∉ range α → |x i - ρ * (z i : ℝ)| ≤ ρ / 2)} with hL
  set O : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ / 2) < x i ∧ x i < ρ * ((z i : ℝ) + 1 - δ / 2)) ∧
    (i ∉ range α → |x i - ρ * (z i : ℝ)| < ρ / 2)} with hO
  have hc : ∀ i : Fin N, Continuous fun x : Eucl N => x i := fun i => PiLp.continuous_apply 2 _ i
  -- Step 1: `K` and `L` are closed, `O` is open.
  have hKc : IsClosed K := by
    rw [hK, ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isClosed_eq (hc i) continuous_const
  have hLc : IsClosed L := by
    rw [hL, ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isClosed_le (((hc i).sub continuous_const).abs) continuous_const
  have hOo : IsOpen O := by
    rw [hO, ofPred_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isOpen_lt continuous_const (hc i)).inter (isOpen_lt (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isOpen_lt (((hc i).sub continuous_const).abs) continuous_const
  -- Step 2: `K ⊆ O ⊆ L`, hence `K ⊆ interior L`.
  have hKO : K ⊆ O := by
    intro x hx i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    · rw [(hx i).2 hi, sub_self, abs_zero]
      positivity
  have hOL : O ⊆ L := by
    intro x hx i
    exact ⟨fun hi => ⟨((hx i).1 hi).1.le, ((hx i).1 hi).2.le⟩, fun hi => ((hx i).2 hi).le⟩
  have hKL : K ⊆ interior L := hKO.trans (interior_maximal hOL hOo)
  -- Step 3: `L` is compact, being a closed subset of a compact coordinate box.
  have hLk : IsCompact L := by
    have hB : IsCompact (WithLp.toLp 2 '' (univ.pi fun i : Fin N =>
        Icc (ρ * (z i : ℝ) - ρ) (ρ * (z i : ℝ) + ρ)) : Set (Eucl N)) :=
      (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
    refine hB.of_isClosed_subset hLc fun x hx =>
      ⟨WithLp.ofLp x, fun i _ => ?_, WithLp.toLp_ofLp 2 x⟩
    by_cases hi : i ∈ range α
    · obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    · have h := abs_le.1 ((hx i).2 hi)
      constructor <;> nlinarith
  -- Steps 4–5: the smooth Urysohn function for `K ⊆ interior L`; it vanishes off the compact `L`.
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Eucl N)) (n := (⊤ : ℕ∞)) hKc hKL
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, HasCompactSupport.intro hLk hf0,
    fun x => hf01 x, fun x hx => hf1.self_of_nhdsSet x hx, ?_⟩
  -- Step 6: every point of another face of direction `α` lies outside `L`.
  intro z' hz' x hx
  apply hf0
  intro hxL
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz'
  have hzi : (z' i : ℝ) + 1 ≤ z i ∨ (z i : ℝ) + 1 ≤ z' i := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  simp only [latticeFace, mem_ofPred_eq] at hx
  by_cases hA : i ∈ range α
  · obtain ⟨h1, h2⟩ := (hx i).1 hA
    obtain ⟨h3, h4⟩ := (hxL i).1 hA
    rcases hzi with h | h <;> nlinarith
  · have h1 := (hx i).2 hA
    have h3 := abs_le.1 ((hxL i).2 hA)
    rw [h1] at h3
    rcases hzi with h | h <;> nlinarith

/-- A mass-admissible test form isolating one lattice face: for `ρ > 0`, `0 < δ < 1/4` and the
face `F₀ = ρ(z + F_α)`, the form `ω = φ dx^α` (`φ` the cut-off of `F₀`) has `[[F]](ω) = 0` for every
other face `F` (`dx^α` kills the faces of other directions, `φ` those of direction `α`), and
`[[F₀]](ω) = ∫_{F₀} φ dHⁿ ≥ Hⁿ(K) = (ρ(1 − 2δ))^n`, `K` the shrunken face where `φ = 1`. -/
theorem Submission.isoperimetric_lattice_face_isolating_form :
    ∀ (n N : ℕ) (ρ δ : ℝ) (F₀ : LatticeFaceIndex n N), 0 < ρ → 0 < δ → δ < 1 / 4 →
      ∃ ω : TestFormOn (univ : Set (Eucl N)) n, ω ∈ massAdmissibleOn (univ : Set (Eucl N)) n univ ∧
        (∀ F : LatticeFaceIndex n N, F ≠ F₀ →
          latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧
        (ρ * (1 - 2 * δ)) ^ n ≤ latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ δ F₀ hρ hδ hδ'
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the coordinate covector `η = dx^α` and the cut-off `φ` of the face `(z, α)`.
  obtain ⟨hηα, hηne, hηnorm⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ δ z α hρ hδ
  -- Step 2: the test form `ω = φ • η`, smooth with compact support.
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ x, (ω : DifferentialForm (Eucl N) n) x = φ x • η :=
    ⟨⟨fun x => φ x • η, ⟨hφs.smul contDiff_const, hφc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ x (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) x v = φ x * η v :=
    fun x v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ⟨subset_univ _, fun x => ?_⟩, ?_, ?_⟩
  -- Step 3: admissibility, `|ω(x)| = |φ(x)| ≤ 1`.
  · rw [hωx, hηnorm, abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- Step 4: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · -- same direction: `z' ≠ z`, and `φ = 0` on the face `(z', α)`.
      have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [hωv, hφ0 z' hz x (by rwa [hα] at hx), zero_mul]
    · -- other direction: `η(e_{α'}) = 0`.
      simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Steps 5–8: the face `F₀`.
  · set K : Set (Eucl N) := {x | ∀ i : Fin N,
      (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
      (i ∉ range α → x i = ρ * (z i : ℝ))} with hK
    -- Step 6: both `F₀` and `K` are coordinate boxes with base point `c_i = ρ z_i`.
    have hFmeas : (μHE[n] : Measure (Eucl N)) (latticeFace ρ ((z, α) : LatticeFaceIndex n N)) =
        ENNReal.ofReal (ρ ^ n) := by
      convert Submission.isoperimetric_coord_box_measure n N α (fun i => ρ * (z i : ℝ)) 0 ρ
        hρ.le using 2
      · ext x
        simp only [latticeFace, mem_ofPred_eq, add_zero, mul_add, mul_one]
      · rw [sub_zero]
    have hKmeas : (μHE[n] : Measure (Eucl N)) K = ENNReal.ofReal ((ρ * (1 - 2 * δ)) ^ n) := by
      convert Submission.isoperimetric_coord_box_measure n N α (fun i => ρ * (z i : ℝ)) (ρ * δ)
        (ρ * (1 - δ)) (by nlinarith) using 2
      · ext x
        simp only [hK, mem_ofPred_eq, mul_add, mul_sub, mul_one, add_sub_assoc]
      · ring
    -- Step 7: `K ⊆ F₀`, `K` is closed, and `φ` is integrable on `F₀`.
    have hKsub : K ⊆ latticeFace ρ ((z, α) : LatticeFaceIndex n N) := by
      intro x hx i
      refine ⟨fun hi => ?_, (hx i).2⟩
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    have hc : ∀ i : Fin N, Continuous fun x : Eucl N => x i := fun i => PiLp.continuous_apply 2 _ i
    have hKc : IsClosed K := by
      rw [hK, ofPred_forall]
      refine isClosed_iInter fun i => ?_
      by_cases hi : i ∈ range α
      · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
        exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
      · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
        exact isClosed_eq (hc i) continuous_const
    have hint : IntegrableOn φ (latticeFace ρ ((z, α) : LatticeFaceIndex n N))
        (μHE[n] : Measure (Eucl N)) :=
      Measure.integrableOn_of_bounded (M := 1) (by rw [hFmeas]; exact ENNReal.ofReal_ne_top)
        hφs.continuous.aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 x).1]; exact (hφ01 x).2)
    -- Step 8: `(ρ(1 − 2δ))^n = Hⁿ(K) = ∫_K φ ≤ ∫_{F₀} φ = [[F₀]](ω)`.
    calc (ρ * (1 - 2 * δ)) ^ n
        = ((μHE[n] : Measure (Eucl N)) K).toReal := by
          rw [hKmeas, ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg hρ.le (by linarith)) n)]
      _ = ∫ _ in K, (1 : ℝ) ∂(μHE[n] : Measure (Eucl N)) := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = ∫ x in K, φ x ∂(μHE[n] : Measure (Eucl N)) :=
          setIntegral_congr_fun hKc.measurableSet fun x hx => (hφ1 x hx).symm
      _ ≤ ∫ x in latticeFace ρ ((z, α) : LatticeFaceIndex n N), φ x ∂(μHE[n] : Measure (Eucl N)) :=
          setIntegral_mono_set hint (ae_of_all _ fun x => (hφ01 x).1)
            (Filter.EventuallySubset.of_subset hKsub)
      _ = latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N)
            (ω : DifferentialForm (Eucl N) n) := by
          simp only [latticeFaceAction, hωv, hηα, mul_one]

/-- Simon Ch. 6, proof of 6.1, (1) (p. 169): a lattice chain `Pc = ∑_F β_F [[F]]` in `ℝ^N` has
mass at least `|β_F| ρ^{m+1}` for every face `F` (`H^{m+1}(F) = ρ^{m+1}`).  For `0 < δ < 1/4`
the isolating form `ω` of `F` kills every other face, so testing `Pc` with `±ω` gives
`M(Pc) ≥ |β_F| [[F]](ω) ≥ |β_F| (ρ (1 - 2δ))^{m+1}`; then let `δ → 0⁺`. -/
theorem Submission.isoperimetric_lattice_chain_mass_ge :
    ∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ)
      (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc →
      ∀ F : LatticeFaceIndex (m + 1) N, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass := by
  intro m N ρ β Pc hρ hPc F₀
  -- Step 1: for `0 < δ < 1/4`, the bound with `ρ` replaced by `ρ (1 - 2δ)`.
  have hδ_bound : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
      ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)) ≤ Pc.mass := by
    intro δ hδ hδ'
    obtain ⟨ω, hadm, hoff, hlb⟩ :=
      Submission.isoperimetric_lattice_face_isolating_form (m + 1) N ρ δ F₀ hρ hδ hδ'
    -- Only `F₀` contributes to the lattice sum.
    have hPcω :
        Pc ω = β F₀ * latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) (m + 1)) := by
      rw [hPc ω, tsum_eq_single F₀ fun F hF => by rw [hoff F hF, mul_zero]]
    -- `-ω` is admissible as well, and `Pc(-ω) = -Pc(ω)`.
    have hadm' : -ω ∈ massAdmissibleOn (univ : Set (Eucl N)) (m + 1) univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
      exact hadm.2 x
    have hPcneg : Pc (-ω) = -Pc ω := map_neg Pc.toCurrent ω
    -- Test with `ω` if `β F₀ ≥ 0` and with `-ω` otherwise.
    rcases le_or_gt 0 (β F₀) with hβ | hβ
    · calc ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1))
          ≤ ENNReal.ofReal (Pc ω) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hPcω, abs_of_nonneg hβ]
            exact mul_le_mul_of_nonneg_left hlb hβ
        _ ≤ Pc.mass := Pc.le_massOn hadm
    · calc ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1))
          ≤ ENNReal.ofReal (Pc (-ω)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hPcneg, hPcω, abs_of_neg hβ, ← neg_mul]
            exact mul_le_mul_of_nonneg_left hlb (neg_nonneg.2 hβ.le)
        _ ≤ Pc.mass := Pc.le_massOn hadm'
  -- Step 2: let `δ → 0⁺`; the left-hand side is continuous in `δ`.
  have hc : Continuous fun δ : ℝ => ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (|β F₀| * ρ ^ (m + 1)))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
    fun δ hδ => hδ_bound δ hδ.1 hδ.2)
/-- Integrals over a lattice face as integrals over the parameter cube: for every `g`,
`∫_{latticeFace ρ G} g dHᵈ = ∫_{[0,ρ]^d} g(∑_l ρ w_l e_l + ∑_j s_j e_{γ(j)}) ds`, `G = (w, γ)`.
The map `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` is an isometry (`(e_{γ(j)})_j` is orthonormal)
whose range contains the face, so `L_* Hᵈ = Hᵈ ⌞ range L` and the integral is pulled back along
`L` and then along the volume-preserving `toLp : (Fin d → ℝ) → ℝᵈ`; the face pulls back to
`[0,ρ]^d`. -/
theorem Submission.br_latticeFace_setIntegral_eq_cube :
    ∀ (P d : ℕ) (ρ : ℝ) (G : LatticeFaceIndex d P) (g : Eucl P → ℝ),
      ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P)) =
        ∫ s in Set.Icc (0 : Fin d → ℝ) (fun _ => ρ),
          g (∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (G.2 j) (1 : ℝ)) := by
  intro P d ρ G g
  -- The parametrization `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` of the face.
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin d) → Eucl P, ∀ t, L t =
      ∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
        ∑ j, t j • EuclideanSpace.single (G.2 j) (1 : ℝ) := ⟨_, fun _ => rfl⟩
  -- Coordinates: `L(t)_{γ(j)} = ρ w_{γ(j)} + t_j` and `L(t)_l = ρ w_l` for `l ∉ range γ`.
  have hcoord : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P),
      L t l = ρ * (G.1 l : ℝ) + ∑ j, if l = G.2 j then t j else 0 := by
    intro t l
    rw [hL]
    simp [Pi.single_apply]
  have hcoord₁ : ∀ (t : EuclideanSpace ℝ (Fin d)) (j : Fin d),
      L t (G.2 j) = ρ * (G.1 (G.2 j) : ℝ) + t j := by
    intro t j
    rw [hcoord]
    simp
  have hcoord₂ : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P), l ∉ Set.range G.2 →
      L t l = ρ * (G.1 l : ℝ) := by
    intro t l hl
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hl ⟨j, h.symm⟩
  -- `L` is an isometry because `(e_{γ(j)})_j` is orthonormal.
  have hv : Orthonormal ℝ (fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).comp _ G.2.injective
  have hiso : Isometry L := by
    refine Isometry.of_dist_eq fun t t' => ?_
    have hdiff : L t - L t' = ∑ j, (t j - t' j) • EuclideanSpace.single (G.2 j) (1 : ℝ) := by
      rw [hL, hL]
      simp [sub_smul, Finset.sum_sub_distrib]
    have h2 : ‖L t - L t'‖ ^ 2 = ‖t - t'‖ ^ 2 := by
      rw [hdiff, ← real_inner_self_eq_norm_sq, hv.inner_sum, EuclideanSpace.norm_sq_eq]
      simp [sq]
    rw [dist_eq_norm, dist_eq_norm]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  -- The face lies in the range of `L`.
  have hrange : latticeFace ρ G ⊆ Set.range L := by
/-- Summed Poincaré bound over the top-dimensional lattice cubes of `ℝⁿ`, `n = m + 1`, with
`c = (2√n)ⁿ √n`.  A cube lies in the closed ball of radius `√n ρ` about any of its points, so
summing over the a.e. partition into cubes bounds the left side by
`ρ⁻ⁿ ∫⁻ₓ ∫⁻_{B(x, √n ρ)} |u x - u y|`.  The translation estimate bounds this double integral by
`√n ρ Λ L(B(0, √n ρ))`, and `L(B(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_poincare_sum :
    ∀ m : ℕ, ∃ c : ℝ≥0, ∀ (ρ : ℝ), 0 < ρ → ∀ (u : Eucl (m + 1) → ℝ) (Λ : ℝ≥0∞), Measurable u →
      (∀ h : Eucl (m + 1), ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        c * ENNReal.ofReal ρ * Λ := by
  intro m
  -- `s = √n` and `c = (2s)ⁿ s`.
  obtain ⟨s, hs, hs_def⟩ : ∃ s : ℝ, 0 ≤ s ∧ Real.sqrt ((m + 1 : ℕ) : ℝ) = s :=
    ⟨_, Real.sqrt_nonneg _, rfl⟩
  have hC : 0 ≤ (2 * s) ^ (m + 1) * s := by positivity
  refine ⟨NNReal.mk ((2 * s) ^ (m + 1) * s) hC, fun ρ hρ u Λ hu hΛ => ?_⟩
  obtain ⟨-, -, hc, -, he, -, hg, -⟩ := Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  rw [hs_def] at he
  have hr : 0 ≤ s * ρ := mul_nonneg hs hρ.le
  -- Step 1: a cube lies in the closed ball of radius `s ρ` about any of its points.
  have hcube : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
    fun F => setLIntegral_mono' (hc F) fun x hx =>
      lintegral_mono_set fun y hy => mem_closedBall.2 (he F y hy x hx)
  -- Step 6 (arithmetic): `(ρⁿ)⁻¹ (s ρ) (2 s ρ)ⁿ = (2s)ⁿ s ρ`.
  have hinv : 0 ≤ (ρ ^ (m + 1))⁻¹ := by positivity
  have hconst : (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1) =
      (2 * s) ^ (m + 1) * s * ρ := by
    calc (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)
        = (2 * s) ^ (m + 1) * s * ρ * ((ρ ^ (m + 1))⁻¹ * ρ ^ (m + 1)) := by ring
      _ = (2 * s) ^ (m + 1) * s * ρ := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), mul_one]
  calc ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y|
      ≤ ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
        ENNReal.tsum_le_tsum fun F => by gcongr _ * ?_; exact hcube F
    -- Step 2: the cubes form an a.e. partition of `ℝⁿ`.
    _ = ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| := by
        rw [ENNReal.tsum_mul_left, hg]
    -- Steps 3–5: the translation estimate and the volume of the ball.
    _ ≤ ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          (ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1))) := by
        gcongr _ * ?_
        calc ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y|
            ≤ ENNReal.ofReal (s * ρ) * Λ * volume (closedBall (0 : Eucl (m + 1)) (s * ρ)) :=
              Submission.fiw_tb_tda_ps_translation_ball (m + 1) u Λ (s * ρ) hu hΛ
          _ ≤ ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1)) := by
              gcongr _ * ?_
              exact Submission.fiw_tb_tda_ps_ball_volume_le (m + 1) (s * ρ) hr
    -- Step 6: collect the constants.
    _ = ENNReal.ofReal ((ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)) * Λ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hinv hr), ENNReal.ofReal_mul hinv]
        ring
    _ = ENNReal.ofReal ((2 * s) ^ (m + 1) * s) * ENNReal.ofReal ρ * Λ := by
        rw [hconst, ENNReal.ofReal_mul hC]
    _ = _ := by rw [ENNReal.ofReal_eq_coe_nnreal hC]
/-- Simon Ch. 6, 2.11: a current kills every test form whose support misses `spt T`.
`tsupport ω` is a compact subset of the zero region, so finitely many open `W ⊂⊂ U` on which `T`
vanishes cover it, and a smooth partition of unity `ψᵢ` on `tsupport ω` subordinate to them
splits `ω = ∑ᵢ ψᵢ ω` into test forms supported in those `W`. -/
theorem Submission.fiw_tb_apply_eq_zero_of_disjoint_support :
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
    refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), PiLp.ext fun l => ?_⟩
    by_cases hl : l ∈ Set.range G.2
    · obtain ⟨j, rfl⟩ := hl
      rw [hcoord₁]
      simp
    · rw [hcoord₂ _ _ hl]
      exact ((hx l).2 hl).symm
  -- The face pulls back to the cube `[0,ρ]^d` of parameters.
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      (L ⁻¹' latticeFace ρ G) = Set.Icc 0 (fun _ => ρ) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).1
        rw [hcoord₁] at this
        simp only [Pi.zero_apply]
        linarith
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).2
        rw [hcoord₁] at this
        linarith
    · rintro ⟨h0, h1⟩ i
      refine ⟨?_, hcoord₂ _ i⟩
      rintro ⟨j, rfl⟩
      rw [hcoord₁]
      have h0j := h0 j
      have h1j := h1 j
      simp only [Pi.zero_apply] at h0j
      constructor <;> nlinarith
  -- `L_* Hᵈ = Hᵈ ⌞ range L`; change variables along `L`, then along `toLp`.
  calc ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P))
      = ∫ x in latticeFace ρ G, g x
          ∂((μHE[d] : Measure (EuclideanSpace ℝ (Fin d))).map L) := by
        rw [hiso.map_euclideanHausdorffMeasure, Measure.restrict_restrict_of_subset hrange]
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t)
          ∂(μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) :=
        hiso.isClosedEmbedding.setIntegral_map _
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    _ = ∫ s in (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
          (L ⁻¹' latticeFace ρ G), g (L (WithLp.toLp 2 s)) :=
        ((PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
          (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
          (fun t => g (L t)) (L ⁻¹' latticeFace ρ G)).symm
    _ = _ := by
        rw [hpre]
        simp only [hL]

/-- A continuous `g ≥ 0` that is positive at a relative-interior point `p` of the face
`latticeFace ρ F` (`ρ > 0`) has positive integral over the face: by
`br_latticeFace_setIntegral_eq_cube` the integral is `∫_{[0,ρ]^n} g(ι(s)) ds`, the point
`s₀ = (p_{α(j)} − ρ z_{α(j)})_j` lies in the open cube `(0,ρ)^n` with `ι(s₀) = p`, and
`support (g ∘ ι) ∩ (0,ρ)^n` is open and nonempty, hence of positive Lebesgue measure. -/
theorem Submission.fiw_tb_lcc_face_integral_pos : ∀ (n N : ℕ) (ρ : ℝ) (F : LatticeFaceIndex n N) (g : Eucl N → ℝ) (p : Eucl N), 0 < ρ → Continuous g → (∀ x, 0 ≤ g x) → 0 < g p → (∀ i : Fin N, (i ∈ range F.2 → ρ * (F.1 i : ℝ) < p i ∧ p i < ρ * ((F.1 i : ℝ) + 1)) ∧ (i ∉ range F.2 → p i = ρ * (F.1 i : ℝ))) → 0 < ∫ x in latticeFace ρ F, g x ∂(μHE[n] : Measure (Eucl N)) := by
  intro n N ρ F g p hρ hg hg0 hgp hp
  rw [Submission.br_latticeFace_setIntegral_eq_cube N n ρ F g]
  -- the affine parametrization of the face
  set ι : (Fin n → ℝ) → Eucl N := fun s =>
    ∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
      ∑ j, s j • EuclideanSpace.single (F.2 j) (1 : ℝ) with hι
  have hιc : Continuous ι := by
    rw [hι]
    fun_prop
  have hcoord : ∀ (s : Fin n → ℝ) (l : Fin N),
      ι s l = ρ * (F.1 l : ℝ) + ∑ j, if l = F.2 j then s j else 0 := by
    intro s l
    simp [hι, Pi.single_apply]
  set s₀ : Fin n → ℝ := fun j => p (F.2 j) - ρ * (F.1 (F.2 j) : ℝ) with hs₀
  have hιs₀ : ι s₀ = p := by
    ext l
    rw [hcoord]
    by_cases hl : l ∈ range F.2
    · obtain ⟨j, rfl⟩ := hl
      simp [hs₀, F.2.injective.eq_iff]
    · have hne : ∀ j, l ≠ F.2 j := fun j h => hl ⟨j, h.symm⟩
      simp [hne, (hp l).2 hl]
  have hs₀mem : s₀ ∈ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ) := by
    intro j _
    obtain ⟨h1, h2⟩ := (hp (F.2 j)).1 ⟨j, rfl⟩
    constructor <;> simp only [hs₀] <;> linarith
  have hh : Continuous fun s => g (ι s) := hg.comp hιc
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun s => hg0 _)
    (hh.continuousOn.integrableOn_compact isCompact_Icc)]
  have hopen : IsOpen (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
    hh.isOpen_support.inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hne : (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)).Nonempty :=
    ⟨s₀, by simp only [Function.mem_support, hιs₀]; exact hgp.ne', hs₀mem⟩
  calc (0 : ℝ≥0∞) < volume (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
        hopen.measure_pos volume hne
    _ ≤ volume (Function.support (fun s => g (ι s)) ∩ Icc (0 : Fin n → ℝ) (fun _ => ρ)) := by
        refine measure_mono (inter_subset_inter_right _ fun s hs => ⟨fun j => ?_, fun j => ?_⟩)
        · exact (hs j (mem_univ j)).1.le
        · exact (hs j (mem_univ j)).2.le

/-- Local isolating form for a lattice face: near any point `x` of the face `F₀ = ρ (z + F_α)`
and inside any open `W ∋ x` there is a test form `ω = (ψ φ) • dx^α` on `ℝ^N` with
`tsupport ω ⊆ W`, `[[F]](ω) = 0` for every other face `F ≠ F₀` and `[[F₀]](ω) > 0`. -/
theorem Submission.fiw_tb_lcc_local_isolating_form : ∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ F₀ x W hρ hx hW hxW
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the centre `c` of the face.
  set c : Eucl N := WithLp.toLp 2 (fun i => if i ∈ range α then ρ * ((z i : ℝ) + 1 / 2)
    else ρ * (z i : ℝ)) with hc
  -- Step 2: a point `p = x + t (c - x)`, `0 < t ≤ 1`, of `W`.
  have hcont : Continuous fun t : ℝ => x + t • (c - x) := by fun_prop
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x + t • (c - x)) ⁻¹' W := by simpa using hxW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW.preimage hcont) 0 h0
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set p : Eucl N := x + t • (c - x) with hp
  have hpW : p ∈ W :=
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε)
  have hpcoord : ∀ i, p i = x i + t * (c i - x i) := fun i => by simp [hp]
  -- Step 3: `p` lies in the shrunken face `K_{t/2}`, hence in the open face.
  have hpK : ∀ i : Fin N, (i ∈ range α → ρ * ((z i : ℝ) + t / 2) ≤ p i ∧
      p i ≤ ρ * ((z i : ℝ) + 1 - t / 2)) ∧ (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    constructor
    · intro hi
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      have hci : c i = ρ * ((z i : ℝ) + 1 / 2) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci]
      constructor <;> nlinarith
    · intro hi
      have hci : c i = ρ * (z i : ℝ) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci, (hx i).2 hi]
      ring
  have hpopen : ∀ i : Fin N, (i ∈ range α → ρ * (z i : ℝ) < p i ∧ p i < ρ * ((z i : ℝ) + 1)) ∧
      (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    refine ⟨fun hi => ?_, (hpK i).2⟩
    obtain ⟨h1, h2⟩ := (hpK i).1 hi
    constructor <;> nlinarith
  -- Step 4: a bump `ψ` at `p` supported in `W`, the cut-off `φ` of the face, `dx^α`.
  obtain ⟨ψ, hψW, hψc, hψs, hψr, hψp⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hW.mem_nhds hpW)
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ (t / 2) z α hρ (half_pos ht0)
  obtain ⟨hηα, hηne, -⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  -- Step 5: the test form `ω = (ψ φ) • dx^α`.
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y * φ y) := hψs.mul hφs
  have hgc : HasCompactSupport (fun y => ψ y * φ y) := hψc.mul_right
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ y, (ω : DifferentialForm (Eucl N) n) y = (ψ y * φ y) • η :=
    ⟨⟨fun y => (ψ y * φ y) • η, ⟨hgs.smul contDiff_const, hgc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ y (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) y v = ψ y * φ y * η v :=
    fun y v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ?_, ?_, ?_⟩
  -- Step 6: `tsupport ω ⊆ tsupport ψ ⊆ W`.
  · have hω : (ω : DifferentialForm (Eucl N) n) = fun y => (ψ y * φ y) • η := funext hωx
    rw [hω]
    exact (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hψW)
  -- Step 7: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hωv, hφ0 z' hz y (by rwa [hα] at hy), mul_zero, zero_mul]
    · simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Step 8: `[[F₀]](ω) = ∫_{F₀} ψ φ dHⁿ > 0`.
  · have hval : latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N)
          (ω : DifferentialForm (Eucl N) n) =
        ∫ y in latticeFace ρ ((z, α) : LatticeFaceIndex n N), ψ y * φ y
          ∂(μHE[n] : Measure (Eucl N)) := by
      simp only [latticeFaceAction, hωv, hηα, mul_one]
    rw [hval]
    refine Submission.fiw_tb_lcc_face_integral_pos n N ρ (z, α) (fun y => ψ y * φ y) p hρ
      hgs.continuous (fun y => mul_nonneg (hψr ⟨y, rfl⟩).1 (hφ01 y).1) ?_ hpopen
    rw [hψp, hφ1 p hpK, one_mul]
    exact one_pos

/-- Simon Ch. 6, proof of 7.2, (2) (p. 171): every face `F` of a lattice chain
`Pc = ∑_F β_F [[F]]` in `ℝ^N` with `β_F ≠ 0` lies in `spt Pc`, and `|β_F| ρ^{m+1} ≤ M(Pc)`.  If a
point `x ∈ F` were outside `spt Pc`, then `Pc` would vanish on some open `W ∋ x`; the isolating
form `ω` of `F` localized at `x` (`tsupport ω ⊆ W`, `[[G]](ω) = 0` for `G ≠ F`, `[[F]](ω) > 0`)
would give `0 = Pc(ω) = β_F [[F]](ω) ≠ 0`.  The mass bound is
`isoperimetric_lattice_chain_mass_ge`. -/
theorem Submission.fiw_tb_lattice_chain_coeff : ∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ) (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc → ∀ F : LatticeFaceIndex (m + 1) N, β F ≠ 0 → latticeFace ρ F ⊆ Pc.support ∧ ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass := by
  intro m N ρ β Pc hρ hPc F hF
  refine ⟨fun x hx => ?_, Submission.isoperimetric_lattice_chain_mass_ge m N ρ β Pc hρ hPc F⟩
  -- Otherwise `x` lies in the zero region: some open `W ∋ x` on which `Pc` vanishes.
  by_contra hxs
  have hxz : x ∈ Pc.zeroRegion := by
    by_contra h
    exact hxs ⟨mem_univ x, h⟩
  obtain ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩ := hxz
  -- The isolating form of `F` localized at `x` is supported in `W`, so `Pc` kills it.
  obtain ⟨ω, hωW, hoff, hpos⟩ :=
    Submission.fiw_tb_lcc_local_isolating_form (m + 1) N ρ F x W hρ hx hWo hxW
  have h1 : Pc ω = 0 := hWv ω hωW
  -- Only `F` contributes to the lattice sum, so `Pc ω = β_F [[F]](ω) ≠ 0`.
  have h2 : Pc ω = β F * latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) (m + 1)) := by
    rw [hPc ω, tsum_eq_single F fun G hG => by rw [hoff G hG, mul_zero]]
  exact mul_ne_zero hF hpos.ne' (h2 ▸ h1)
/-- Simon Ch. 6, proof of 7.2 (p. 171, "only finitely many currents `P` as in (2)"): for `ρ > 0`,
a bounded `Y ⊆ ℝ^N` and `A ∈ ℝ`, only finitely many integer coefficient families `β` have the
face `F` inside `Y` and `|β_F| ≤ A` whenever `β_F ≠ 0`. -/
theorem Submission.fiw_tb_lattice_coeff_finite :
    ∀ (n N : ℕ) (ρ : ℝ), 0 < ρ → ∀ (Y : Set (Eucl N)), Bornology.IsBounded Y → ∀ A : ℝ,
      {β : LatticeFaceIndex n N → ℝ | (∀ F, ∃ k : ℤ, β F = k) ∧
        ∀ F, β F ≠ 0 → latticeFace ρ F ⊆ Y ∧ |β F| ≤ A}.Finite := by
  intro n N ρ hρ Y hY A
  -- Faces inside `Y`: the vertex `ρ z` of the face `(z, α)` lies in `Y ⊆ closedBall 0 R`, so
  -- `z` lies in a finite box, and `α` ranges over a finite type.
  obtain ⟨R, hR⟩ := hY.subset_closedBall 0
  have hS : {F : LatticeFaceIndex n N | latticeFace ρ F ⊆ Y}.Finite := by
    refine ((Set.Finite.pi fun _ : Fin N => Set.finite_Icc (-⌈R / ρ⌉) ⌈R / ρ⌉).prod
      Set.finite_univ).subset ?_
    rintro ⟨z, α⟩ hF
    refine ⟨fun i _ => ?_, Set.mem_univ _⟩
    have hv : (WithLp.toLp 2 fun i => ρ * (z i : ℝ) : Eucl N) ∈ latticeFace ρ (z, α) :=
      fun j => ⟨fun _ => ⟨le_rfl, mul_le_mul_of_nonneg_left (by linarith) hρ.le⟩, fun _ => rfl⟩
    have hi := (PiLp.norm_apply_le _ i).trans (mem_closedBall_zero_iff.mp (hR (hF hv)))
    rw [PiLp.toLp_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hρ] at hi
    have hz : |(z i : ℝ)| ≤ R / ρ := by
      rw [le_div_iff₀ hρ]
      linarith
    have hc := Int.le_ceil (R / ρ)
    obtain ⟨h1, h2⟩ := abs_le.mp hz
    constructor
    · have : ((-⌈R / ρ⌉ : ℤ) : ℝ) ≤ z i := by push_cast; linarith
      exact_mod_cast this
    · have : (z i : ℝ) ≤ ((⌈R / ρ⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  -- Admissible values: integers of absolute value at most `|A|` (this includes `0`).
  have hV : {x : ℝ | (∃ k : ℤ, x = k) ∧ |x| ≤ |A|}.Finite := by
    refine ((Set.finite_Icc (-⌈|A|⌉) ⌈|A|⌉).image fun k : ℤ => (k : ℝ)).subset ?_
    rintro x ⟨⟨k, rfl⟩, hx⟩
    have hc := Int.le_ceil |A|
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · have : ((-⌈|A|⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
      exact_mod_cast this
    · have : (k : ℝ) ≤ ((⌈|A|⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  -- Restriction to the faces inside `Y` maps the set into the finite set of maps into the
  -- admissible values, and is injective on it since every `β` in it vanishes off these faces.
  have := hS.to_subtype
  refine Set.Finite.of_finite_image
    (f := fun β (F : {F : LatticeFaceIndex n N | latticeFace ρ F ⊆ Y}) => β F) ?_ ?_
  · refine (Set.Finite.pi' fun _ => hV).subset ?_
    rintro _ ⟨β, ⟨hint, hsupp⟩, rfl⟩ F
    dsimp only
    refine ⟨hint F, ?_⟩
    by_cases h : β F = 0
    · rw [h, abs_zero]
      exact abs_nonneg A
    · exact (hsupp F h).2.trans (le_abs_self A)
  · rintro β ⟨-, hsupp⟩ β' ⟨-, hsupp'⟩ h
    funext F
    by_cases hF : latticeFace ρ F ⊆ Y
    · exact congrFun h ⟨F, hF⟩
    · have h0 : β F = 0 := by
        by_contra h'
        exact hF (hsupp F h').1
      have h0' : β' F = 0 := by
        by_contra h'
        exact hF (hsupp' F h').1
      rw [h0, h0']
/-- Simon Ch. 6, proof of 7.2 (translation estimate): for `φ ∈ C_c^∞(ℝⁿ)`, `n = m + 1`, and
`h ∈ ℝⁿ`, the test `m`-form `ω = φ α` with `α = ∑ₖ (-1)ᵏ hₖ dx⁽ᵏ⁾`, where `dx⁽ᵏ⁾` is the wedge of
the coordinate covectors `dxʲ`, `j ≠ k`, in increasing order (indices `0, …, m`), satisfies
`|ω(x)| = ‖h‖ |φ(x)|` and `dω(x)(e₀, …, eₘ) = ∑ᵢ hᵢ ∂ᵢφ(x) = Dφ(x) h`. -/
theorem Submission.fiw_tb_te_directional_form :
    ∀ (m : ℕ) (φ : Eucl (m + 1) → ℝ) (h : Eucl (m + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∃ ω : TestFormOn (univ : Set (Eucl (m + 1))) m,
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ ‖h‖ * |φ x|) ∧
        ∀ x, ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) m ω :
            TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1))
          x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h := by
  intro m φ h hφ hcs
  -- The coordinate `m`-covector omitting direction `k`, on the frame omitting `eᵢ`, is `δₖᵢ`.
  have hcoord : ∀ k i : Fin (m + 1),
      (wedgeCovectors m (fun a => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ)))
        (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = if k = i then 1 else 0 := by
    intro k i
    rw [wedgeCovectors_apply_det]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl]
      have hM : (Matrix.of fun a b => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ)
          (EuclideanSpace.single (k.succAbove b) (1 : ℝ))) = 1 := by
        ext a b
        simp [Matrix.one_apply]
      rw [hM, Matrix.det_one]
    · -- `i = k.succAbove a₀` for some `a₀`, and row `a₀` of the matrix vanishes.
      rw [ite_eq_right hki]
      obtain ⟨a₀, ha₀⟩ : i ∈ Set.range k.succAbove := by
        rw [Fin.range_succAbove]; exact Ne.symm hki
      apply Matrix.det_eq_zero_of_row_eq_zero a₀
      intro b
      simp [ha₀, (Fin.succAbove_ne i b).symm]
  -- The strictly increasing `I : Fin m → Fin (m + 1)` are exactly the maps `k.succAbove`.
  have hincr : ∀ I : Fin m → Fin (m + 1), StrictMono I → ∃ k : Fin (m + 1), I = k.succAbove := by
    intro I hI
    have hinj := hI.injective
    have hns : ¬ Function.Surjective I := by
      intro hs
      have := Fintype.card_le_of_surjective I hs
      simp at this
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨k, hk⟩ := hns
    refine ⟨k, ?_⟩
    have hsub : Set.range I ⊆ Set.range k.succAbove := by
      rw [Fin.range_succAbove]
      rintro _ ⟨a, rfl⟩
      exact hk a
    have hcard : (Set.range k.succAbove).ncard ≤ (Set.range I).ncard := by
      rw [Set.ncard_range_of_injective hinj,
        Set.ncard_range_of_injective Fin.succAbove_right_injective]
    have heq : Set.range I = Set.range k.succAbove := Set.eq_of_subset_of_ncard_le hsub hcard
    exact (StrictMono.range_inj_of_wellFoundedLT hI (Fin.strictMono_succAbove k)).1 heq
  -- The constant covector `α` with `α(e ∘ i.succAbove) = (-1)ⁱ hᵢ`.
  set α : Covector (Eucl (m + 1)) m := ∑ k : Fin (m + 1), ((-1 : ℝ) ^ (k : ℕ) * h k) •
    wedgeCovectors m (fun a => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ))
    with hα
  have hαe : ∀ i : Fin (m + 1),
      α (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = (-1 : ℝ) ^ (i : ℕ) * h i := by
    intro i
    simp only [hα, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hcoord, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  -- `ω₀ = φ α` is a test form on `univ`.
  set ω₀ : DifferentialForm (Eucl (m + 1)) m := fun y => φ y • α with hω₀
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω₀ := hφ.smul contDiff_const
  have hcs₀ : HasCompactSupport ω₀ := hcs.smul_right
  have hmem : ω₀ ∈ testFormOnSubmodule (univ : Set (Eucl (m + 1))) m :=
    ⟨⟨hsmooth, hcs₀⟩, subset_univ _⟩
  refine ⟨⟨ω₀, hmem⟩, ?_, ?_⟩
  · -- Norm: reindex the increasing multi-indices by `k ↦ k.succAbove`; then `|ω₀(x)| = |φ(x)| ‖h‖`.
    intro x
    apply le_of_eq
    change covectorEuclideanNorm (φ x • α) = ‖h‖ * |φ x|
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin m → Fin (m + 1),
        if StrictMono I then
          ((φ x • α) (fun i ↦ EuclideanSpace.basisFun (Fin (m + 1)) ℝ (I i))) ^ 2
        else 0) = ∑ k : Fin (m + 1), (φ x) ^ 2 * (h k) ^ 2 := by
      symm
      apply Fintype.sum_of_injective (fun k : Fin (m + 1) => k.succAbove)
        Fin.succAbove_left_injective
      · intro I hI
        rw [ite_eq_right]
        intro hmono
        obtain ⟨k, rfl⟩ := hincr I hmono
        exact hI ⟨k, rfl⟩
      · intro k
        simp only [Fin.strictMono_succAbove, ite_true, EuclideanSpace.basisFun_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        rw [hαe k, mul_pow, mul_pow, ← pow_mul, mul_comm (k : ℕ) 2, pow_mul]
        norm_num
    rw [hsum, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      EuclideanSpace.norm_eq, mul_comm]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.norm_eq_abs, sq_abs]
  · -- Exterior derivative: `dω₀(x)(e) = ∑ᵢ (-1)ⁱ (-1)ⁱ hᵢ Dφ(x) eᵢ = Dφ(x) h`.
    intro x
    change exteriorDerivative ω₀ x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h
    have hdiff : DifferentiableAt ℝ ω₀ x := (hsmooth.differentiable (by simp)).differentiableAt
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply hdiff]
    have key : ∀ i : Fin (m + 1),
        (fun y => ω₀ y (i.removeNth (fun j => EuclideanSpace.single j (1 : ℝ)))) =
          fun y => ((-1 : ℝ) ^ (i : ℕ) * h i) * φ y := by
      intro i
      funext y
      change (φ y • α) (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = _
      rw [ContinuousAlternatingMap.smul_apply, hαe i, smul_eq_mul, mul_comm]
    have hstep : ∀ i : Fin (m + 1),
        (-1 : ℤ) ^ (i : ℕ) • fderiv ℝ
            (fun y => ω₀ y (i.removeNth (fun j => EuclideanSpace.single j (1 : ℝ)))) x
            (EuclideanSpace.single i (1 : ℝ)) =
          h i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      intro i
      rw [key i, fderiv_const_mul hφd]
      simp only [smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, smul_eq_mul]
/-- Weak translation estimate: if `|∫ u · Dφ(h)| ≤ B` for every `C^∞` compactly supported `φ`
with `|φ| ≤ 1`, then `|∫ (u(· + h) − u) · g| ≤ B` for every such `g`.  For `φ_t = g(· − t h)`,
`F(t) = ∫ u(y) g(y − t h) dy` has `F'(t) = −∫ u(y) Dφ_t(y)(h) dy`, so `|F'| ≤ B`, and
`F(1) − F(0) = ∫ (u(x + h) − u(x)) g(x) dx` by translation invariance. -/
theorem Submission.fiw_tb_te_translation_dual :
    ∀ (n : ℕ) (u : Eucl n → ℝ) (h : Eucl n) (B : ℝ), Integrable u →
      (∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, |φ x| ≤ 1) → |∫ x, u x * fderiv ℝ φ x h| ≤ B) →
      ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        (∀ x, |g x| ≤ 1) → |∫ x, (u (x + h) - u x) * g x| ≤ B := by
  intro n u h B hu hB g hg hgc hg1
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- `Dg` is continuous with compact support, hence bounded.
  obtain ⟨K, hK⟩ := (hg.continuous_fderiv hn).bounded_above_of_compact_support (hgc.fderiv ℝ)
  have hcont : ∀ t : ℝ, Continuous fun y : Eucl n => g (y - t • h) := fun t =>
    hg.continuous.comp (continuous_id.sub continuous_const)
  have hcont' : ∀ t : ℝ, Continuous fun y : Eucl n => fderiv ℝ g (y - t • h) (-h) := fun t =>
    ((hg.continuous_fderiv hn).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const
  have hgle : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure (Eucl n)), ‖g (y - t • h)‖ ≤ 1 := fun t =>
    ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hg1 _
  -- Differentiation under the integral sign, dominated by `‖u‖ K ‖h‖`:
  -- `d/dt ∫ u(y) g(y - t h) dy = ∫ u(y) Dg(y - t h)(-h) dy`.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ∫ y, u y * g (y - s • h))
      (∫ y, u y * fderiv ℝ g (y - t • h) (-h)) t := by
    intro t
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
      (F := fun s y => u y * g (y - s • h)) (F' := fun s y => u y * fderiv ℝ g (y - s • h) (-h))
      (bound := fun y => ‖u y‖ * (K * ‖h‖)) Filter.univ_mem
      (Filter.Eventually.of_forall fun s => hu.aestronglyMeasurable.mul
        (hcont s).aestronglyMeasurable)
      (hu.mul_bdd (hcont t).aestronglyMeasurable (hgle t))
      (hu.aestronglyMeasurable.mul (hcont' t).aestronglyMeasurable)
      (ae_of_all _ fun y s _ => ?_) (hu.norm.mul_const _) (ae_of_all _ fun y s _ => ?_)).2
    · rw [norm_mul]
      gcongr
      calc ‖fderiv ℝ g (y - s • h) (-h)‖ ≤ K * ‖-h‖ :=
            (fderiv ℝ g (y - s • h)).le_of_opNorm_le (hK _) (-h)
        _ = K * ‖h‖ := by rw [norm_neg]
    · have hline : HasDerivAt (fun s : ℝ => y - s • h) (-h) s := by
        simpa using ((hasDerivAt_id s).smul_const h).const_sub y
      exact ((hg.differentiable hn (y - s • h)).hasFDerivAt.comp_hasDerivAt s hline).const_mul (u y)
  -- Each derivative is bounded by `B`: apply the hypothesis to `φ_t = g(· - t h)`.
  have hbound : ∀ t : ℝ, ‖∫ y, u y * fderiv ℝ g (y - t • h) (-h)‖ ≤ B := by
    intro t
    have hφ := hB (fun y => g (y - t • h)) (hg.comp (contDiff_id.sub contDiff_const))
      (hgc.comp_homeomorph (Homeomorph.subRight (t • h))) (fun y => hg1 _)
    simp only [fderiv_comp_sub] at hφ
    have heq : ∫ y, u y * fderiv ℝ g (y - t • h) (-h) = -∫ y, u y * fderiv ℝ g (y - t • h) h := by
      rw [← integral_neg]
      simp only [map_neg, mul_neg]
    rw [heq, norm_neg, Real.norm_eq_abs]
    exact hφ
  -- Mean value inequality on `[0, 1]`.
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => ∫ y, u y * g (y - s • h))
    (fun t _ => (hderiv t).hasDerivWithinAt) (fun t _ => hbound t)
  -- Identify the endpoints, using translation invariance of Lebesgue measure.
  have h1 : ∫ y, u y * g (y - (1 : ℝ) • h) = ∫ x, u (x + h) * g x := by
    rw [one_smul, ← integral_add_right_eq_self (μ := volume) (fun y => u y * g (y - h)) h]
    simp only [add_sub_cancel_right]
  have h0 : ∫ y, u y * g (y - (0 : ℝ) • h) = ∫ x, u x * g x := by
    simp only [zero_smul, sub_zero]
  have hint1 : Integrable fun x => u (x + h) * g x := by
    simpa using (hu.comp_add_right h).mul_bdd (hcont 0).aestronglyMeasurable (hgle 0)
  have hint0 : Integrable fun x => u x * g x := by
    simpa using hu.mul_bdd (hcont 0).aestronglyMeasurable (hgle 0)
  have hJ : ∫ x, (u (x + h) - u x) * g x = (∫ x, u (x + h) * g x) - ∫ x, u x * g x := by
    rw [← integral_sub hint1 hint0]
    simp only [sub_mul]
  rw [hJ, ← h1, ← h0, ← Real.norm_eq_abs]
  exact hmvt
/-- Smooth `±1` separation of two disjoint compact sets `K₁, K₂ ⊆ ℝ^n`: a `C^∞` function
`g : ℝ^n → ℝ` with compact support, `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`.
`Disjoint.exists_thickenings` gives `δ > 0` with disjoint open thickenings `Vᵢ ⊇ Kᵢ`; the smooth
Urysohn lemma `exists_contDiff_support_eq_eq_one_iff` gives `gᵢ : ℝ^n → [0, 1]` with
`support gᵢ = Vᵢ` and `gᵢ = 1` on `Kᵢ`, compactly supported since `closure Vᵢ ⊆ cthickening δ Kᵢ`.
At each point one of `g₁, g₂` vanishes, and `g = g₁ - g₂`. -/
theorem Submission.fiw_tb_te_l1d_smooth_sign_sep : ∀ (n : ℕ) (K₁ K₂ : Set (Eucl n)), IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ → ∃ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧ (∀ x, |g x| ≤ 1) ∧ (∀ x ∈ K₁, g x = 1) ∧ (∀ x ∈ K₂, g x = -1) := by
  intro n K₁ K₂ hK₁ hK₂ hd
  -- Steps 1–2: disjoint δ-thickenings `V₁ ⊇ K₁`, `V₂ ⊇ K₂`.
  obtain ⟨δ, hδ, hdδ⟩ := hd.exists_thickenings hK₁ hK₂.isClosed
  -- Step 3: smooth Urysohn functions `gᵢ : ℝ^n → [0, 1]`, `support gᵢ = Vᵢ`, `gᵢ = 1` on `Kᵢ`.
  obtain ⟨g₁, hg₁, hr₁, hs₁, he₁⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₁)) hK₁.isClosed (self_subset_thickening hδ K₁)
  obtain ⟨g₂, hg₂, hr₂, hs₂, he₂⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₂)) hK₂.isClosed (self_subset_thickening hδ K₂)
  -- Step 4: `tsupport gᵢ = closure Vᵢ ⊆ cthickening δ Kᵢ`, which is compact.
  have hc : ∀ (K : Set (Eucl n)) (f : Eucl n → ℝ), IsCompact K →
      Function.support f = thickening δ K → HasCompactSupport f := by
    intro K f hK hs
    refine (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport f) ?_
    rw [tsupport, hs]
    exact closure_thickening_subset_cthickening δ K
  have h01₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1 := fun x => hr₁ (mem_range_self x)
  have h01₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1 := fun x => hr₂ (mem_range_self x)
  -- Step 5: at every point one of `g₁, g₂` vanishes, since `V₁ ∩ V₂ = ∅`.
  have hdis : ∀ x, g₁ x = 0 ∨ g₂ x = 0 := by
    intro x
    by_contra h
    rw [not_or] at h
    have h1 : x ∈ Function.support g₁ := h.1
    have h2 : x ∈ Function.support g₂ := h.2
    rw [hs₁] at h1
    rw [hs₂] at h2
    exact Set.disjoint_left.mp hdδ h1 h2
  -- Steps 6–8: `g = g₁ - g₂`.
  refine ⟨g₁ - g₂, hg₁.sub hg₂, (hc K₁ g₁ hK₁ hs₁).sub (hc K₂ g₂ hK₂ hs₂), ?_, ?_, ?_⟩
  · intro x
    have a := h01₁ x
    have b := h01₂ x
    rw [Pi.sub_apply, abs_le]
    rcases hdis x with h | h <;> constructor <;> linarith
  · intro x hx
    have h1 : g₁ x = 1 := (he₁ x).1 hx
    have h2 : g₂ x = 0 := by
      rcases hdis x with h | h
      · rw [h1] at h; norm_num at h
      · exact h
    simp [h1, h2]
  · intro x hx
    have h2 : g₂ x = 1 := (he₂ x).1 hx
    have h1 : g₁ x = 0 := by
      rcases hdis x with h | h
      · exact h
      · rw [h2] at h; norm_num at h
    simp [h1, h2]
/-- Compact approximation of the sign of an integrable `w : ℝ^n → ℝ`: for `ε > 0` there are
disjoint compact sets `K₁, K₂` such that every a.e.-strongly measurable `g` with `|g| ≤ 1`,
`g = 1` on `K₁` and `g = -1` on `K₂` satisfies `∫ |w| < ∫ w g + ε`.
For a Borel representative `v` of `w`, the finite measure `ν = |v| dx` is inner regular, so there
are compact `K₁ ⊆ {v > 0}` and `K₂ ⊆ {v < 0}` with `ν({v > 0} \ K₁), ν({v < 0} \ K₂) < ε/4`.
Off `S = ({v > 0} \ K₁) ∪ ({v < 0} \ K₂)` we have `v g = |v|`, and on `S` we have `v g ≥ -|v|`,
so `∫ |v| ≤ ∫ v g + 2 ν(S) < ∫ v g + ε`. -/
theorem Submission.fiw_tb_te_l1d_compact_sign_approx : ∀ (n : ℕ) (w : Eucl n → ℝ), Integrable w → ∀ ε : ℝ, 0 < ε → ∃ K₁ K₂ : Set (Eucl n), IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧ ∀ g : Eucl n → ℝ, AEStronglyMeasurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ K₁, g x = 1) → (∀ x ∈ K₂, g x = -1) → (∫ x, |w x|) < (∫ x, w x * g x) + ε := by
  intro n w hw ε hε
  -- A Borel representative `v` of `w` and the finite measure `ν = |v| dx`.
  set v : Eucl n → ℝ := hw.aestronglyMeasurable.mk w with hv_def
  have hv_meas : StronglyMeasurable v := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hwv : w =ᵐ[volume] v := hw.aestronglyMeasurable.ae_eq_mk
  have hvi : Integrable v := hw.congr hwv
  set ν : Measure (Eucl n) := volume.withDensity (fun x => ENNReal.ofReal |v x|) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hvi.abs.hasFiniteIntegral
  -- Inner approximation of `{v > 0}` and `{v < 0}` by compact sets.
  set Ap : Set (Eucl n) := {x | 0 < v x} with hAp_def
  set Am : Set (Eucl n) := {x | v x < 0} with hAm_def
  have hAp : MeasurableSet Ap := measurableSet_lt measurable_const hv_meas.measurable
  have hAm : MeasurableSet Am := measurableSet_lt hv_meas.measurable measurable_const
  have hε4 : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨Kp, hKpA, hKp, hKpν⟩ := hAp.exists_isCompact_sdiff_lt (measure_ne_top ν Ap) hε4
  obtain ⟨Km, hKmA, hKm, hKmν⟩ := hAm.exists_isCompact_sdiff_lt (measure_ne_top ν Am) hε4
  have hdisj : Disjoint Kp Km := by
    rw [Set.disjoint_left]
    intro x hp hm
    have h1 : 0 < v x := hKpA hp
    have h2 : v x < 0 := hKmA hm
    linarith
  refine ⟨Kp, Km, hKp, hKm, hdisj, ?_⟩
  intro g hg hg1 hgp hgm
  -- The pointwise inequality `|v| - 2·1_S|v| ≤ v g`.
  set S : Set (Eucl n) := (Ap \ Kp) ∪ (Am \ Km) with hS_def
  have hS : MeasurableSet S := (hAp.diff hKp.measurableSet).union (hAm.diff hKm.measurableSet)
  have hpt : ∀ x, |v x| - 2 * S.indicator (fun y => |v y|) x ≤ v x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have h : |v x * g x| ≤ |v x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hg1 x)
      linarith [(abs_le.mp h).1]
    · rw [indicator_of_notMem hx]
      have hx' : (0 < v x → x ∈ Kp) ∧ (v x < 0 → x ∈ Km) := by
        constructor
        · intro h
          by_contra hK
          exact hx (Or.inl ⟨h, hK⟩)
        · intro h
          by_contra hK
          exact hx (Or.inr ⟨h, hK⟩)
      rcases lt_trichotomy (v x) 0 with h | h | h
      · rw [hgm x (hx'.2 h), abs_of_neg h]
        linarith
      · rw [h]
        simp
      · rw [hgp x (hx'.1 h), abs_of_pos h]
        linarith
  -- Integrate.
  have hvg : Integrable (fun x => v x * g x) :=
    hvi.mul_bdd hg (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg1 x)
  have hind : Integrable (fun x => S.indicator (fun y => |v y|) x) := hvi.abs.indicator hS
  have hlhs : Integrable (fun x => |v x| - 2 * S.indicator (fun y => |v y|) x) :=
    hvi.abs.sub (hind.const_mul 2)
  have hmono := integral_mono hlhs hvg hpt
  rw [integral_sub hvi.abs (hind.const_mul 2), integral_const_mul, integral_indicator hS] at hmono
  -- `∫_S |v| = (ν S).toReal < ε / 2`.
  have hνS : ν S = ∫⁻ x in S, ENNReal.ofReal |v x| := withDensity_apply _ hS
  have hSint : ∫ x in S, |v x| = (ν S).toReal := by
    rw [hνS, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _)
      hvi.abs.aestronglyMeasurable.restrict]
  have hνS_lt : ν S < ENNReal.ofReal (ε / 2) := by
    calc ν S ≤ ν (Ap \ Kp) + ν (Am \ Km) := measure_union_le _ _
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := ENNReal.add_lt_add hKpν hKmν
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
  have hSlt : ∫ x in S, |v x| < ε / 2 := by
    rw [hSint]
    exact ENNReal.toReal_lt_of_lt_ofReal hνS_lt
  -- Transfer back from `v` to `w`.
  have h1 : ∫ x, |w x| = ∫ x, |v x| := integral_congr_ae (hwv.fun_comp abs)
  have h2 : ∫ x, w x * g x = ∫ x, v x * g x :=
    integral_congr_ae (hwv.mono fun x hx => by simp only [hx])
  rw [h1, h2]
  linarith

/-- **Extension of a compactly supported current to `ℝ^P` (Simon Ch. 6, proof of 7.2, (G3)).**
If `spt X ⊆ K` with `K ⊆ U` compact and `M(X) < ∞`, then `Y(ω) = X(χ ω)`, `χ` a smooth cutoff
with `tsupport χ ⊆ U` and `χ = 1` on an open `N ⊇ K`, is a current on `ℝ^P` (`fiw_tb_ext_cutoff`,
`fiw_tb_ext_cutoff_current`).  Since `X` kills test forms whose support misses `K`
(`fiw_tb_apply_eq_zero_of_disjoint_support`) and `χ ω = ω` on `N`, `Y|_U = X`
(`fiw_tb_ext_apply_eq_of_eqOn`); `Y` and `∂Y` kill test forms whose support misses `K`, as
`tsupport (χ ω) ⊆ tsupport ω` and `tsupport dω ⊆ tsupport ω`, and `(∂Y)|_U = ∂X`.  Support,
mass and integer multiplicity of `Y` and `∂Y` are then controlled by those of their restrictions
`X` and `∂X` (`fiw_tb_ext_support_subset`, `fiw_tb_ext_mass_le_restrictDomain`,
`fiw_tb_ext_isIntegerMultiplicity`).  The mass formula (MF) is not needed. -/
theorem Submission.fiw_tb_extend_to_univ : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P m : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ X : GeometricCurrentOn U (m + 1), X.support ⊆ K → X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧ (IsIntegerMultiplicity X.boundary → IsIntegerMultiplicity Y.boundary) := by
  intro _hMF P m U K hU hK hKU X hXK hXm
  -- (V) for `X`: as `spt X ⊆ K`, `X` kills every test form whose support misses `K`.
  have hXv : ∀ ω : TestFormOn U (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) K → X ω = 0 := fun ω hω =>
    Submission.fiw_tb_apply_eq_zero_of_disjoint_support P (m + 1) U X ω (hω.mono_right hXK)
  -- The cutoff `χ` and multiplication by `χ`, from test forms on `ℝ^P` and on `U` to `U`.
  obtain ⟨χ, N, hχ, hχ01, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P (m + 1) univ U χ hχ hχU
  obtain ⟨LU, hLU⟩ := Submission.fiw_tb_ext_smul_testForm P (m + 1) U U χ hχ hχU
  -- `Y(ω) = X(χ ω)` is a current on `ℝ^P`, since `M(X) < ∞` and `|χ| ≤ 1`.
  obtain ⟨Y, hY⟩ := Submission.fiw_tb_ext_cutoff_current P (m + 1) U χ hχ hχU
    (fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩) X hXm
  -- `Y|_U = X`: `Y(ω) = X(χ ω) = X(ω)`, as `χ ω = ω` on `N ⊇ K`.
  have hres : Y.restrictDomain (subset_univ U) = X := by
    ext ω
    rw [GeometricCurrentOn.restrictDomain_apply,
      hY (testFormOnInclusion (subset_univ U) (m + 1) ω) (LU ω) (hLU ω)]
    exact Submission.fiw_tb_ext_apply_eq_of_eqOn P (m + 1) U K N X hN hKN hXv ω (LU ω)
      fun x hx => by rw [hLU, hχN x hx, one_smul]
  -- (V) for `Y`: `Y(ω) = X(χ ω)` and `tsupport (χ ω) ⊆ tsupport ω`.
  have hYv : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) K → Y ω = 0 := by
    intro ω hω
    rw [hY ω (L ω) (hL ω)]
    refine hXv (L ω) (hω.mono_left ?_)
    rw [show (L ω : DifferentialForm (Eucl P) (m + 1)) =
      fun x => χ x • (ω : DifferentialForm (Eucl P) (m + 1)) x from funext (hL ω)]
    exact tsupport_smul_subset_right _ _
  -- (V) for `∂Y`, as `tsupport dω ⊆ tsupport ω`; and `(∂Y)|_U = ∂X`, as `d` commutes with the
  -- inclusion of test forms on `U` into test forms on `ℝ^P`.
  have hbYv : ∀ ω : TestFormOn (univ : Set (Eucl P)) m,
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) m)) K → Y.boundary ω = 0 := fun ω hω =>
    hYv _ (hω.mono_left (tsupport_exteriorDerivative_subset _))
  have hbres : Y.boundary.restrictDomain (subset_univ U) = X.boundary := by
    rw [← hres]
    rfl
  refine ⟨Y, hres, Submission.fiw_tb_ext_support_subset P (m + 1) univ K Y isOpen_univ
    hK.isClosed hYv, ?_, ?_, fun hX => ?_, fun hX => ?_⟩
  · -- `M(Y) ≤ M(Y|_U) = M(X)`.
    rw [← hres]
    exact Submission.fiw_tb_ext_mass_le_restrictDomain P (m + 1) U K hU hK hKU Y hYv
  · -- `M(∂Y) ≤ M((∂Y)|_U) = M(∂X)`.
    rw [← hbres]
    exact Submission.fiw_tb_ext_mass_le_restrictDomain P m U K hU hK hKU Y.boundary hbYv
  · rw [← hres] at hX
    exact Submission.fiw_tb_ext_isIntegerMultiplicity P (m + 1) U K hU hK hKU Y hYv hX
  · rw [← hbres] at hX
    exact Submission.fiw_tb_ext_isIntegerMultiplicity P m U K hU hK hKU Y.boundary hbYv hX
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

/-- Simon Ch. 6, 2.4, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of `Y ∈ 𝒟ₖ(U)` to an open
`W ⊆ U` has `M_W(Y|_W) ≤ M_U(Y)`, since every admissible form for `M_W` is admissible for `M_U`,
and it is integer multiplicity when `Y` is: `Y|_W = τ(M ∩ W, θ, ξ)` for `Y = τ(M, θ, ξ)`. -/
theorem Submission.fiw_tb_restrictDomain_mass_im :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U), IsOpen W →
      ∀ Y : GeometricCurrentOn U k, (Y.restrictDomain hWU).mass ≤ Y.mass ∧
        (IsIntegerMultiplicity Y → IsIntegerMultiplicity (Y.restrictDomain hWU)) := by
  intro P k U W hWU hW Y
  exact ⟨Submission.fiw_tb_ri_restrictDomain_mass_le P k U W hWU Y,
    Submission.br_restrictDomain_isIntegerMultiplicity P k U W hWU hW Y⟩
/-- The coordinate covector `dx^α = wedgeCovectors n (proj ∘ α)` on `ℝ^N` is dual to the
coordinate frames: `dx^α(e_α) = 1`, `dx^α(e_{α'}) = 0` for every other increasing multi-index
`α'`, and `covectorEuclideanNorm (c • dx^α) = |c|`. -/
theorem Submission.isoperimetric_coord_covector_eval : ∀ (n N : ℕ) (α : SimonMultiIndex n N), (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 1 ∧ (∀ α' : SimonMultiIndex n N, α' ≠ α → (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α' j) (1 : ℝ)) = 0) ∧ ∀ c : ℝ, covectorEuclideanNorm (c • (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n)) = |c| := by
  intro n N α
  classical
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) with hη
  -- Kronecker property on increasing coordinate frames: `dx^α(e_I) = δ_{α I}`.
  have hK : ∀ I : Fin n → Fin N, StrictMono I →
      η (fun j => EuclideanSpace.single (I j) (1 : ℝ)) = if I = ⇑α then 1 else 0 := by
    intro I hI
    rw [hη, wedgeCovectors_apply_det]
    split_ifs with hIα
    · -- the matrix `[δ_{α i, α j}]` is the identity
      subst hIα
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [Matrix.one_apply, PiLp.single_apply, α.injective.eq_iff]
    · -- some `α i` is not among the `I j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, α i ≠ I j := by
        by_contra! h
        apply hIα
        rw [← StrictMono.range_inj_of_wellFoundedLT hI α.strictMono]
        have hsub : Set.range α ⊆ Set.range I := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range I)).symm
        rw [Set.ncard_range_of_injective hI.injective, Set.ncard_range_of_injective α.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hK α α.strictMono
  · intro α' hα'
    rw [hK α' α'.strictMono, ite_eq_right fun h => hα' (DFunLike.coe_injective h)]
  · intro c
    -- only the summand `I = α` survives, and it contributes `c²`
    have hs : ∀ I : Fin n → Fin N, (if StrictMono I then
        ((c • η) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (I i))) ^ 2 else 0) =
        if I = ⇑α then c ^ 2 else 0 := by
      intro I
      by_cases hI : StrictMono I
      · rw [ite_eq_left hI]
        simp only [EuclideanSpace.basisFun_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        rw [hK I hI]
        split_ifs <;> ring
      · have hIα : I ≠ ⇑α := fun h => hI (h ▸ α.strictMono)
        rw [ite_eq_right hI, ite_eq_right hIα]
    rw [covectorEuclideanNorm, Finset.sum_congr rfl fun I _ => hs I, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _), Real.sqrt_sq_eq_abs]
/-- The `n`-dimensional coordinate box `{x : c_i + a ≤ x_i ≤ c_i + b (i ∈ range α), x_i = c_i
(i ∉ range α)}` in `ℝ^N` has `μHE[n]`-measure `(b - a)^n`.  The map
`ι(y)_i = c_i + ∑_j [α j = i] y_j` is an isometry `ℝⁿ → ℝ^N` carrying the cube `[a, b]ⁿ` onto the
box; `μHE[n]` is invariant under isometries and equals Lebesgue measure on `ℝⁿ`. -/
theorem Submission.isoperimetric_coord_box_measure :
    ∀ (n N : ℕ) (α : SimonMultiIndex n N) (c : Fin N → ℝ) (a b : ℝ), a ≤ b →
      (μHE[n] : Measure (Eucl N)) {x : Eucl N | ∀ i : Fin N,
        (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧ (i ∉ range α → x i = c i)} =
        ENNReal.ofReal ((b - a) ^ n) := by
  intro n N α c a b hab
  classical
  -- The parametrization `ι(y)_i = c_i + ∑_j [α j = i] y_j` of the box.
  set ι : EuclideanSpace ℝ (Fin n) → Eucl N :=
    fun y => WithLp.toLp 2 (fun i => c i + ∑ j, if α j = i then y j else 0) with hι
  have hι_on : ∀ y j, ι y (α j) = c (α j) + y j := by
    intro y j
    simp only [hι, PiLp.toLp_apply, α.inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hι_off : ∀ y i, i ∉ range α → ι y i = c i := by
    intro y i hi
    have hne : ∀ j, α j ≠ i := fun j hj => hi ⟨j, hj⟩
    simp [hι, hne]
  -- `ι` is an isometry: coordinates off `range α` agree, the others reindex along `α`.
  have hiso : Isometry ι := by
    refine Isometry.of_dist_eq fun y y' => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image α)) ?_,
      Finset.sum_image (fun j _ j' _ h => α.injective h)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hι_on, hι_on, dist_add_left]
    · intro i _ hi
      have hi' : i ∉ range α := by
        rintro ⟨j, rfl⟩
        exact hi (Finset.mem_image_of_mem α (Finset.mem_univ j))
      rw [hι_off y i hi', hι_off y' i hi', dist_self]
      ring
  -- `ι` maps the cube `[a, b]ⁿ` onto the box, with preimage `y_j = x_{α j} - c_{α j}`.
  have himage : ι '' {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      {x : Eucl N | ∀ i : Fin N, (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧
        (i ∉ range α → x i = c i)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨?_, hι_off y i⟩
      rintro ⟨j, rfl⟩
      rw [hι_on]
      exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
    · intro hx
      refine ⟨WithLp.toLp 2 (fun j => x (α j) - c (α j)), fun j => ?_, ?_⟩
      · have h := (hx (α j)).1 ⟨j, rfl⟩
        constructor <;> dsimp only <;> linarith [h.1, h.2]
      · ext i
        by_cases hi : i ∈ range α
        · obtain ⟨j, rfl⟩ := hi
          rw [hι_on]
          simp
        · rw [hι_off _ i hi, (hx i).2 hi]
  rw [← himage, hiso.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- The cube is the preimage of `Icc` under the volume-preserving `WithLp.ofLp`.
  have hQ : {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => a) (fun _ => b) := by
    ext y
    simp [Pi.le_def, forall_and]
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (sub_nonneg.2 hab)]
/-- Smooth cut-off for a lattice face: for `ρ, δ > 0` there is a compactly supported smooth
`φ : ℝ^N → [0, 1]` equal to `1` on the shrunken face
`{x : ρ(zᵢ + δ) ≤ xᵢ ≤ ρ(zᵢ + 1 − δ) (i ∈ α), xᵢ = ρ zᵢ (i ∉ α)}` and vanishing on every other
lattice face `ρ (z' + F_α)`, `z' ≠ z`, of the same direction `α`. -/
theorem Submission.isoperimetric_lattice_face_cutoff :
    ∀ (n N : ℕ) (ρ δ : ℝ) (z : Fin N → ℤ) (α : SimonMultiIndex n N), 0 < ρ → 0 < δ →
      ∃ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x : Eucl N, (∀ i : Fin N,
          (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
          (i ∉ range α → x i = ρ * (z i : ℝ))) → φ x = 1) ∧
        ∀ z' : Fin N → ℤ, z' ≠ z → ∀ x ∈ latticeFace ρ ((z', α) : LatticeFaceIndex n N),
          φ x = 0 := by
  intro n N ρ δ z α hρ hδ
  -- `K`: the shrunken face; `L ⊇ O ⊇ K`: a closed and an open enlarged box (margins `ρδ/2`
  -- along `range α`, transversal slab of half-width `ρ/2`).
  set K : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
    (i ∉ range α → x i = ρ * (z i : ℝ))} with hK
  set L : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ / 2) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ / 2)) ∧
    (i ∉ range α → |x i - ρ * (z i : ℝ)| ≤ ρ / 2)} with hL
  set O : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ / 2) < x i ∧ x i < ρ * ((z i : ℝ) + 1 - δ / 2)) ∧
    (i ∉ range α → |x i - ρ * (z i : ℝ)| < ρ / 2)} with hO
  have hc : ∀ i : Fin N, Continuous fun x : Eucl N => x i := fun i => PiLp.continuous_apply 2 _ i
  -- Step 1: `K` and `L` are closed, `O` is open.
  have hKc : IsClosed K := by
    rw [hK, ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isClosed_eq (hc i) continuous_const
  have hLc : IsClosed L := by
    rw [hL, ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isClosed_le (((hc i).sub continuous_const).abs) continuous_const
  have hOo : IsOpen O := by
    rw [hO, ofPred_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isOpen_lt continuous_const (hc i)).inter (isOpen_lt (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isOpen_lt (((hc i).sub continuous_const).abs) continuous_const
  -- Step 2: `K ⊆ O ⊆ L`, hence `K ⊆ interior L`.
  have hKO : K ⊆ O := by
    intro x hx i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    · rw [(hx i).2 hi, sub_self, abs_zero]
      positivity
  have hOL : O ⊆ L := by
    intro x hx i
    exact ⟨fun hi => ⟨((hx i).1 hi).1.le, ((hx i).1 hi).2.le⟩, fun hi => ((hx i).2 hi).le⟩
  have hKL : K ⊆ interior L := hKO.trans (interior_maximal hOL hOo)
  -- Step 3: `L` is compact, being a closed subset of a compact coordinate box.
  have hLk : IsCompact L := by
    have hB : IsCompact (WithLp.toLp 2 '' (univ.pi fun i : Fin N =>
        Icc (ρ * (z i : ℝ) - ρ) (ρ * (z i : ℝ) + ρ)) : Set (Eucl N)) :=
      (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
    refine hB.of_isClosed_subset hLc fun x hx =>
      ⟨WithLp.ofLp x, fun i _ => ?_, WithLp.toLp_ofLp 2 x⟩
    by_cases hi : i ∈ range α
    · obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    · have h := abs_le.1 ((hx i).2 hi)
      constructor <;> nlinarith
  -- Steps 4–5: the smooth Urysohn function for `K ⊆ interior L`; it vanishes off the compact `L`.
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Eucl N)) (n := (⊤ : ℕ∞)) hKc hKL
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, HasCompactSupport.intro hLk hf0,
    fun x => hf01 x, fun x hx => hf1.self_of_nhdsSet x hx, ?_⟩
  -- Step 6: every point of another face of direction `α` lies outside `L`.
  intro z' hz' x hx
  apply hf0
  intro hxL
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz'
  have hzi : (z' i : ℝ) + 1 ≤ z i ∨ (z i : ℝ) + 1 ≤ z' i := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  simp only [latticeFace, mem_ofPred_eq] at hx
  by_cases hA : i ∈ range α
  · obtain ⟨h1, h2⟩ := (hx i).1 hA
    obtain ⟨h3, h4⟩ := (hxL i).1 hA
    rcases hzi with h | h <;> nlinarith
  · have h1 := (hx i).2 hA
    have h3 := abs_le.1 ((hxL i).2 hA)
    rw [h1] at h3
    rcases hzi with h | h <;> nlinarith

/-- A mass-admissible test form isolating one lattice face: for `ρ > 0`, `0 < δ < 1/4` and the
face `F₀ = ρ(z + F_α)`, the form `ω = φ dx^α` (`φ` the cut-off of `F₀`) has `[[F]](ω) = 0` for every
other face `F` (`dx^α` kills the faces of other directions, `φ` those of direction `α`), and
`[[F₀]](ω) = ∫_{F₀} φ dHⁿ ≥ Hⁿ(K) = (ρ(1 − 2δ))^n`, `K` the shrunken face where `φ = 1`. -/
theorem Submission.isoperimetric_lattice_face_isolating_form :
    ∀ (n N : ℕ) (ρ δ : ℝ) (F₀ : LatticeFaceIndex n N), 0 < ρ → 0 < δ → δ < 1 / 4 →
      ∃ ω : TestFormOn (univ : Set (Eucl N)) n, ω ∈ massAdmissibleOn (univ : Set (Eucl N)) n univ ∧
        (∀ F : LatticeFaceIndex n N, F ≠ F₀ →
          latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧
        (ρ * (1 - 2 * δ)) ^ n ≤ latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ δ F₀ hρ hδ hδ'
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the coordinate covector `η = dx^α` and the cut-off `φ` of the face `(z, α)`.
  obtain ⟨hηα, hηne, hηnorm⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ δ z α hρ hδ
  -- Step 2: the test form `ω = φ • η`, smooth with compact support.
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ x, (ω : DifferentialForm (Eucl N) n) x = φ x • η :=
    ⟨⟨fun x => φ x • η, ⟨hφs.smul contDiff_const, hφc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ x (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) x v = φ x * η v :=
    fun x v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ⟨subset_univ _, fun x => ?_⟩, ?_, ?_⟩
  -- Step 3: admissibility, `|ω(x)| = |φ(x)| ≤ 1`.
  · rw [hωx, hηnorm, abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- Step 4: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · -- same direction: `z' ≠ z`, and `φ = 0` on the face `(z', α)`.
      have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [hωv, hφ0 z' hz x (by rwa [hα] at hx), zero_mul]
    · -- other direction: `η(e_{α'}) = 0`.
      simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Steps 5–8: the face `F₀`.
  · set K : Set (Eucl N) := {x | ∀ i : Fin N,
      (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
      (i ∉ range α → x i = ρ * (z i : ℝ))} with hK
    -- Step 6: both `F₀` and `K` are coordinate boxes with base point `c_i = ρ z_i`.
    have hFmeas : (μHE[n] : Measure (Eucl N)) (latticeFace ρ ((z, α) : LatticeFaceIndex n N)) =
        ENNReal.ofReal (ρ ^ n) := by
      convert Submission.isoperimetric_coord_box_measure n N α (fun i => ρ * (z i : ℝ)) 0 ρ
        hρ.le using 2
      · ext x
        simp only [latticeFace, mem_ofPred_eq, add_zero, mul_add, mul_one]
      · rw [sub_zero]
    have hKmeas : (μHE[n] : Measure (Eucl N)) K = ENNReal.ofReal ((ρ * (1 - 2 * δ)) ^ n) := by
      convert Submission.isoperimetric_coord_box_measure n N α (fun i => ρ * (z i : ℝ)) (ρ * δ)
        (ρ * (1 - δ)) (by nlinarith) using 2
      · ext x
        simp only [hK, mem_ofPred_eq, mul_add, mul_sub, mul_one, add_sub_assoc]
      · ring
    -- Step 7: `K ⊆ F₀`, `K` is closed, and `φ` is integrable on `F₀`.
    have hKsub : K ⊆ latticeFace ρ ((z, α) : LatticeFaceIndex n N) := by
      intro x hx i
      refine ⟨fun hi => ?_, (hx i).2⟩
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    have hc : ∀ i : Fin N, Continuous fun x : Eucl N => x i := fun i => PiLp.continuous_apply 2 _ i
    have hKc : IsClosed K := by
      rw [hK, ofPred_forall]
      refine isClosed_iInter fun i => ?_
      by_cases hi : i ∈ range α
      · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
        exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
      · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
        exact isClosed_eq (hc i) continuous_const
    have hint : IntegrableOn φ (latticeFace ρ ((z, α) : LatticeFaceIndex n N))
        (μHE[n] : Measure (Eucl N)) :=
      Measure.integrableOn_of_bounded (M := 1) (by rw [hFmeas]; exact ENNReal.ofReal_ne_top)
        hφs.continuous.aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 x).1]; exact (hφ01 x).2)
    -- Step 8: `(ρ(1 − 2δ))^n = Hⁿ(K) = ∫_K φ ≤ ∫_{F₀} φ = [[F₀]](ω)`.
    calc (ρ * (1 - 2 * δ)) ^ n
        = ((μHE[n] : Measure (Eucl N)) K).toReal := by
          rw [hKmeas, ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg hρ.le (by linarith)) n)]
      _ = ∫ _ in K, (1 : ℝ) ∂(μHE[n] : Measure (Eucl N)) := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = ∫ x in K, φ x ∂(μHE[n] : Measure (Eucl N)) :=
          setIntegral_congr_fun hKc.measurableSet fun x hx => (hφ1 x hx).symm
      _ ≤ ∫ x in latticeFace ρ ((z, α) : LatticeFaceIndex n N), φ x ∂(μHE[n] : Measure (Eucl N)) :=
          setIntegral_mono_set hint (ae_of_all _ fun x => (hφ01 x).1)
            (Filter.EventuallySubset.of_subset hKsub)
      _ = latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N)
            (ω : DifferentialForm (Eucl N) n) := by
          simp only [latticeFaceAction, hωv, hηα, mul_one]

/-- Simon Ch. 6, proof of 6.1, (1) (p. 169): a lattice chain `Pc = ∑_F β_F [[F]]` in `ℝ^N` has
mass at least `|β_F| ρ^{m+1}` for every face `F` (`H^{m+1}(F) = ρ^{m+1}`).  For `0 < δ < 1/4`
the isolating form `ω` of `F` kills every other face, so testing `Pc` with `±ω` gives
`M(Pc) ≥ |β_F| [[F]](ω) ≥ |β_F| (ρ (1 - 2δ))^{m+1}`; then let `δ → 0⁺`. -/
theorem Submission.isoperimetric_lattice_chain_mass_ge :
    ∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ)
      (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc →
      ∀ F : LatticeFaceIndex (m + 1) N, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass := by
  intro m N ρ β Pc hρ hPc F₀
  -- Step 1: for `0 < δ < 1/4`, the bound with `ρ` replaced by `ρ (1 - 2δ)`.
  have hδ_bound : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
      ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)) ≤ Pc.mass := by
    intro δ hδ hδ'
    obtain ⟨ω, hadm, hoff, hlb⟩ :=
      Submission.isoperimetric_lattice_face_isolating_form (m + 1) N ρ δ F₀ hρ hδ hδ'
    -- Only `F₀` contributes to the lattice sum.
    have hPcω :
        Pc ω = β F₀ * latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) (m + 1)) := by
      rw [hPc ω, tsum_eq_single F₀ fun F hF => by rw [hoff F hF, mul_zero]]
    -- `-ω` is admissible as well, and `Pc(-ω) = -Pc(ω)`.
    have hadm' : -ω ∈ massAdmissibleOn (univ : Set (Eucl N)) (m + 1) univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
      exact hadm.2 x
    have hPcneg : Pc (-ω) = -Pc ω := map_neg Pc.toCurrent ω
    -- Test with `ω` if `β F₀ ≥ 0` and with `-ω` otherwise.
    rcases le_or_gt 0 (β F₀) with hβ | hβ
    · calc ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1))
          ≤ ENNReal.ofReal (Pc ω) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hPcω, abs_of_nonneg hβ]
            exact mul_le_mul_of_nonneg_left hlb hβ
        _ ≤ Pc.mass := Pc.le_massOn hadm
    · calc ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1))
          ≤ ENNReal.ofReal (Pc (-ω)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hPcneg, hPcω, abs_of_neg hβ, ← neg_mul]
            exact mul_le_mul_of_nonneg_left hlb (neg_nonneg.2 hβ.le)
        _ ≤ Pc.mass := Pc.le_massOn hadm'
  -- Step 2: let `δ → 0⁺`; the left-hand side is continuous in `δ`.
  have hc : Continuous fun δ : ℝ => ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (|β F₀| * ρ ^ (m + 1)))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
    fun δ hδ => hδ_bound δ hδ.1 hδ.2)
/-- Integrals over a lattice face as integrals over the parameter cube: for every `g`,
`∫_{latticeFace ρ G} g dHᵈ = ∫_{[0,ρ]^d} g(∑_l ρ w_l e_l + ∑_j s_j e_{γ(j)}) ds`, `G = (w, γ)`.
The map `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` is an isometry (`(e_{γ(j)})_j` is orthonormal)
whose range contains the face, so `L_* Hᵈ = Hᵈ ⌞ range L` and the integral is pulled back along
`L` and then along the volume-preserving `toLp : (Fin d → ℝ) → ℝᵈ`; the face pulls back to
`[0,ρ]^d`. -/
theorem Submission.br_latticeFace_setIntegral_eq_cube :
    ∀ (P d : ℕ) (ρ : ℝ) (G : LatticeFaceIndex d P) (g : Eucl P → ℝ),
      ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P)) =
        ∫ s in Set.Icc (0 : Fin d → ℝ) (fun _ => ρ),
          g (∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (G.2 j) (1 : ℝ)) := by
  intro P d ρ G g
  -- The parametrization `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` of the face.
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin d) → Eucl P, ∀ t, L t =
      ∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
        ∑ j, t j • EuclideanSpace.single (G.2 j) (1 : ℝ) := ⟨_, fun _ => rfl⟩
  -- Coordinates: `L(t)_{γ(j)} = ρ w_{γ(j)} + t_j` and `L(t)_l = ρ w_l` for `l ∉ range γ`.
  have hcoord : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P),
      L t l = ρ * (G.1 l : ℝ) + ∑ j, if l = G.2 j then t j else 0 := by
    intro t l
    rw [hL]
    simp [Pi.single_apply]
  have hcoord₁ : ∀ (t : EuclideanSpace ℝ (Fin d)) (j : Fin d),
      L t (G.2 j) = ρ * (G.1 (G.2 j) : ℝ) + t j := by
    intro t j
    rw [hcoord]
    simp
  have hcoord₂ : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P), l ∉ Set.range G.2 →
      L t l = ρ * (G.1 l : ℝ) := by
    intro t l hl
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hl ⟨j, h.symm⟩
  -- `L` is an isometry because `(e_{γ(j)})_j` is orthonormal.
  have hv : Orthonormal ℝ (fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).comp _ G.2.injective
  have hiso : Isometry L := by
    refine Isometry.of_dist_eq fun t t' => ?_
    have hdiff : L t - L t' = ∑ j, (t j - t' j) • EuclideanSpace.single (G.2 j) (1 : ℝ) := by
      rw [hL, hL]
      simp [sub_smul, Finset.sum_sub_distrib]
    have h2 : ‖L t - L t'‖ ^ 2 = ‖t - t'‖ ^ 2 := by
      rw [hdiff, ← real_inner_self_eq_norm_sq, hv.inner_sum, EuclideanSpace.norm_sq_eq]
      simp [sq]
    rw [dist_eq_norm, dist_eq_norm]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  -- The face lies in the range of `L`.
  have hrange : latticeFace ρ G ⊆ Set.range L := by
    intro x hx
    refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), PiLp.ext fun l => ?_⟩
    by_cases hl : l ∈ Set.range G.2
    · obtain ⟨j, rfl⟩ := hl
      rw [hcoord₁]
      simp
    · rw [hcoord₂ _ _ hl]
      exact ((hx l).2 hl).symm
  -- The face pulls back to the cube `[0,ρ]^d` of parameters.
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      (L ⁻¹' latticeFace ρ G) = Set.Icc 0 (fun _ => ρ) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).1
        rw [hcoord₁] at this
        simp only [Pi.zero_apply]
        linarith
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).2
        rw [hcoord₁] at this
        linarith
    · rintro ⟨h0, h1⟩ i
      refine ⟨?_, hcoord₂ _ i⟩
      rintro ⟨j, rfl⟩
      rw [hcoord₁]
      have h0j := h0 j
      have h1j := h1 j
      simp only [Pi.zero_apply] at h0j
      constructor <;> nlinarith
  -- `L_* Hᵈ = Hᵈ ⌞ range L`; change variables along `L`, then along `toLp`.
  calc ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P))
      = ∫ x in latticeFace ρ G, g x
          ∂((μHE[d] : Measure (EuclideanSpace ℝ (Fin d))).map L) := by
        rw [hiso.map_euclideanHausdorffMeasure, Measure.restrict_restrict_of_subset hrange]
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t)
          ∂(μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) :=
        hiso.isClosedEmbedding.setIntegral_map _
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    _ = ∫ s in (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
          (L ⁻¹' latticeFace ρ G), g (L (WithLp.toLp 2 s)) :=
        ((PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
          (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
          (fun t => g (L t)) (L ⁻¹' latticeFace ρ G)).symm
    _ = _ := by
        rw [hpre]
        simp only [hL]

/-- A continuous `g ≥ 0` that is positive at a relative-interior point `p` of the face
`latticeFace ρ F` (`ρ > 0`) has positive integral over the face: by
`br_latticeFace_setIntegral_eq_cube` the integral is `∫_{[0,ρ]^n} g(ι(s)) ds`, the point
`s₀ = (p_{α(j)} − ρ z_{α(j)})_j` lies in the open cube `(0,ρ)^n` with `ι(s₀) = p`, and
`support (g ∘ ι) ∩ (0,ρ)^n` is open and nonempty, hence of positive Lebesgue measure. -/
theorem Submission.fiw_tb_lcc_face_integral_pos : ∀ (n N : ℕ) (ρ : ℝ) (F : LatticeFaceIndex n N) (g : Eucl N → ℝ) (p : Eucl N), 0 < ρ → Continuous g → (∀ x, 0 ≤ g x) → 0 < g p → (∀ i : Fin N, (i ∈ range F.2 → ρ * (F.1 i : ℝ) < p i ∧ p i < ρ * ((F.1 i : ℝ) + 1)) ∧ (i ∉ range F.2 → p i = ρ * (F.1 i : ℝ))) → 0 < ∫ x in latticeFace ρ F, g x ∂(μHE[n] : Measure (Eucl N)) := by
  intro n N ρ F g p hρ hg hg0 hgp hp
  rw [Submission.br_latticeFace_setIntegral_eq_cube N n ρ F g]
  -- the affine parametrization of the face
  set ι : (Fin n → ℝ) → Eucl N := fun s =>
    ∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
      ∑ j, s j • EuclideanSpace.single (F.2 j) (1 : ℝ) with hι
  have hιc : Continuous ι := by
    rw [hι]
    fun_prop
  have hcoord : ∀ (s : Fin n → ℝ) (l : Fin N),
      ι s l = ρ * (F.1 l : ℝ) + ∑ j, if l = F.2 j then s j else 0 := by
    intro s l
    simp [hι, Pi.single_apply]
  set s₀ : Fin n → ℝ := fun j => p (F.2 j) - ρ * (F.1 (F.2 j) : ℝ) with hs₀
  have hιs₀ : ι s₀ = p := by
    ext l
    rw [hcoord]
    by_cases hl : l ∈ range F.2
    · obtain ⟨j, rfl⟩ := hl
      simp [hs₀, F.2.injective.eq_iff]
    · have hne : ∀ j, l ≠ F.2 j := fun j h => hl ⟨j, h.symm⟩
      simp [hne, (hp l).2 hl]
  have hs₀mem : s₀ ∈ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ) := by
    intro j _
    obtain ⟨h1, h2⟩ := (hp (F.2 j)).1 ⟨j, rfl⟩
    constructor <;> simp only [hs₀] <;> linarith
  have hh : Continuous fun s => g (ι s) := hg.comp hιc
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun s => hg0 _)
    (hh.continuousOn.integrableOn_compact isCompact_Icc)]
  have hopen : IsOpen (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
    hh.isOpen_support.inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hne : (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)).Nonempty :=
    ⟨s₀, by simp only [Function.mem_support, hιs₀]; exact hgp.ne', hs₀mem⟩
  calc (0 : ℝ≥0∞) < volume (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
        hopen.measure_pos volume hne
    _ ≤ volume (Function.support (fun s => g (ι s)) ∩ Icc (0 : Fin n → ℝ) (fun _ => ρ)) := by
        refine measure_mono (inter_subset_inter_right _ fun s hs => ⟨fun j => ?_, fun j => ?_⟩)
        · exact (hs j (mem_univ j)).1.le
        · exact (hs j (mem_univ j)).2.le

/-- Local isolating form for a lattice face: near any point `x` of the face `F₀ = ρ (z + F_α)`
and inside any open `W ∋ x` there is a test form `ω = (ψ φ) • dx^α` on `ℝ^N` with
`tsupport ω ⊆ W`, `[[F]](ω) = 0` for every other face `F ≠ F₀` and `[[F₀]](ω) > 0`. -/
theorem Submission.fiw_tb_lcc_local_isolating_form : ∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ F₀ x W hρ hx hW hxW
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the centre `c` of the face.
  set c : Eucl N := WithLp.toLp 2 (fun i => if i ∈ range α then ρ * ((z i : ℝ) + 1 / 2)
    else ρ * (z i : ℝ)) with hc
  -- Step 2: a point `p = x + t (c - x)`, `0 < t ≤ 1`, of `W`.
  have hcont : Continuous fun t : ℝ => x + t • (c - x) := by fun_prop
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x + t • (c - x)) ⁻¹' W := by simpa using hxW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW.preimage hcont) 0 h0
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set p : Eucl N := x + t • (c - x) with hp
  have hpW : p ∈ W :=
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε)
  have hpcoord : ∀ i, p i = x i + t * (c i - x i) := fun i => by simp [hp]
  -- Step 3: `p` lies in the shrunken face `K_{t/2}`, hence in the open face.
  have hpK : ∀ i : Fin N, (i ∈ range α → ρ * ((z i : ℝ) + t / 2) ≤ p i ∧
      p i ≤ ρ * ((z i : ℝ) + 1 - t / 2)) ∧ (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    constructor
    · intro hi
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      have hci : c i = ρ * ((z i : ℝ) + 1 / 2) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci]
      constructor <;> nlinarith
    · intro hi
      have hci : c i = ρ * (z i : ℝ) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci, (hx i).2 hi]
      ring
  have hpopen : ∀ i : Fin N, (i ∈ range α → ρ * (z i : ℝ) < p i ∧ p i < ρ * ((z i : ℝ) + 1)) ∧
      (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    refine ⟨fun hi => ?_, (hpK i).2⟩
    obtain ⟨h1, h2⟩ := (hpK i).1 hi
    constructor <;> nlinarith
  -- Step 4: a bump `ψ` at `p` supported in `W`, the cut-off `φ` of the face, `dx^α`.
  obtain ⟨ψ, hψW, hψc, hψs, hψr, hψp⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hW.mem_nhds hpW)
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ (t / 2) z α hρ (half_pos ht0)
  obtain ⟨hηα, hηne, -⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  -- Step 5: the test form `ω = (ψ φ) • dx^α`.
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y * φ y) := hψs.mul hφs
  have hgc : HasCompactSupport (fun y => ψ y * φ y) := hψc.mul_right
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ y, (ω : DifferentialForm (Eucl N) n) y = (ψ y * φ y) • η :=
    ⟨⟨fun y => (ψ y * φ y) • η, ⟨hgs.smul contDiff_const, hgc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ y (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) y v = ψ y * φ y * η v :=
    fun y v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ?_, ?_, ?_⟩
  -- Step 6: `tsupport ω ⊆ tsupport ψ ⊆ W`.
  · have hω : (ω : DifferentialForm (Eucl N) n) = fun y => (ψ y * φ y) • η := funext hωx
    rw [hω]
    exact (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hψW)
  -- Step 7: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hωv, hφ0 z' hz y (by rwa [hα] at hy), mul_zero, zero_mul]
    · simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Step 8: `[[F₀]](ω) = ∫_{F₀} ψ φ dHⁿ > 0`.
  · have hval : latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N)
          (ω : DifferentialForm (Eucl N) n) =
        ∫ y in latticeFace ρ ((z, α) : LatticeFaceIndex n N), ψ y * φ y
          ∂(μHE[n] : Measure (Eucl N)) := by
      simp only [latticeFaceAction, hωv, hηα, mul_one]
    rw [hval]
    refine Submission.fiw_tb_lcc_face_integral_pos n N ρ (z, α) (fun y => ψ y * φ y) p hρ
      hgs.continuous (fun y => mul_nonneg (hψr ⟨y, rfl⟩).1 (hφ01 y).1) ?_ hpopen
    rw [hψp, hφ1 p hpK, one_mul]
    exact one_pos

/-- Simon Ch. 6, proof of 7.2, (2) (p. 171): every face `F` of a lattice chain
`Pc = ∑_F β_F [[F]]` in `ℝ^N` with `β_F ≠ 0` lies in `spt Pc`, and `|β_F| ρ^{m+1} ≤ M(Pc)`.  If a
point `x ∈ F` were outside `spt Pc`, then `Pc` would vanish on some open `W ∋ x`; the isolating
form `ω` of `F` localized at `x` (`tsupport ω ⊆ W`, `[[G]](ω) = 0` for `G ≠ F`, `[[F]](ω) > 0`)
would give `0 = Pc(ω) = β_F [[F]](ω) ≠ 0`.  The mass bound is
`isoperimetric_lattice_chain_mass_ge`. -/
theorem Submission.fiw_tb_lattice_chain_coeff : ∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ) (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc → ∀ F : LatticeFaceIndex (m + 1) N, β F ≠ 0 → latticeFace ρ F ⊆ Pc.support ∧ ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass := by
  intro m N ρ β Pc hρ hPc F hF
  refine ⟨fun x hx => ?_, Submission.isoperimetric_lattice_chain_mass_ge m N ρ β Pc hρ hPc F⟩
  -- Otherwise `x` lies in the zero region: some open `W ∋ x` on which `Pc` vanishes.
  by_contra hxs
  have hxz : x ∈ Pc.zeroRegion := by
    by_contra h
    exact hxs ⟨mem_univ x, h⟩
  obtain ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩ := hxz
  -- The isolating form of `F` localized at `x` is supported in `W`, so `Pc` kills it.
  obtain ⟨ω, hωW, hoff, hpos⟩ :=
    Submission.fiw_tb_lcc_local_isolating_form (m + 1) N ρ F x W hρ hx hWo hxW
  have h1 : Pc ω = 0 := hWv ω hωW
  -- Only `F` contributes to the lattice sum, so `Pc ω = β_F [[F]](ω) ≠ 0`.
  have h2 : Pc ω = β F * latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) (m + 1)) := by
    rw [hPc ω, tsum_eq_single F fun G hG => by rw [hoff G hG, mul_zero]]
  exact mul_ne_zero hF hpos.ne' (h2 ▸ h1)
/-- Simon Ch. 6, proof of 7.2 (p. 171, "only finitely many currents `P` as in (2)"): for `ρ > 0`,
a bounded `Y ⊆ ℝ^N` and `A ∈ ℝ`, only finitely many integer coefficient families `β` have the
face `F` inside `Y` and `|β_F| ≤ A` whenever `β_F ≠ 0`. -/
theorem Submission.fiw_tb_lattice_coeff_finite :
    ∀ (n N : ℕ) (ρ : ℝ), 0 < ρ → ∀ (Y : Set (Eucl N)), Bornology.IsBounded Y → ∀ A : ℝ,
      {β : LatticeFaceIndex n N → ℝ | (∀ F, ∃ k : ℤ, β F = k) ∧
        ∀ F, β F ≠ 0 → latticeFace ρ F ⊆ Y ∧ |β F| ≤ A}.Finite := by
  intro n N ρ hρ Y hY A
  -- Faces inside `Y`: the vertex `ρ z` of the face `(z, α)` lies in `Y ⊆ closedBall 0 R`, so
  -- `z` lies in a finite box, and `α` ranges over a finite type.
  obtain ⟨R, hR⟩ := hY.subset_closedBall 0
  have hS : {F : LatticeFaceIndex n N | latticeFace ρ F ⊆ Y}.Finite := by
    refine ((Set.Finite.pi fun _ : Fin N => Set.finite_Icc (-⌈R / ρ⌉) ⌈R / ρ⌉).prod
      Set.finite_univ).subset ?_
    rintro ⟨z, α⟩ hF
    refine ⟨fun i _ => ?_, Set.mem_univ _⟩
    have hv : (WithLp.toLp 2 fun i => ρ * (z i : ℝ) : Eucl N) ∈ latticeFace ρ (z, α) :=
      fun j => ⟨fun _ => ⟨le_rfl, mul_le_mul_of_nonneg_left (by linarith) hρ.le⟩, fun _ => rfl⟩
    have hi := (PiLp.norm_apply_le _ i).trans (mem_closedBall_zero_iff.mp (hR (hF hv)))
    rw [PiLp.toLp_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hρ] at hi
    have hz : |(z i : ℝ)| ≤ R / ρ := by
      rw [le_div_iff₀ hρ]
      linarith
    have hc := Int.le_ceil (R / ρ)
    obtain ⟨h1, h2⟩ := abs_le.mp hz
    constructor
    · have : ((-⌈R / ρ⌉ : ℤ) : ℝ) ≤ z i := by push_cast; linarith
      exact_mod_cast this
    · have : (z i : ℝ) ≤ ((⌈R / ρ⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  -- Admissible values: integers of absolute value at most `|A|` (this includes `0`).
  have hV : {x : ℝ | (∃ k : ℤ, x = k) ∧ |x| ≤ |A|}.Finite := by
    refine ((Set.finite_Icc (-⌈|A|⌉) ⌈|A|⌉).image fun k : ℤ => (k : ℝ)).subset ?_
    rintro x ⟨⟨k, rfl⟩, hx⟩
    have hc := Int.le_ceil |A|
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · have : ((-⌈|A|⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
      exact_mod_cast this
    · have : (k : ℝ) ≤ ((⌈|A|⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  -- Restriction to the faces inside `Y` maps the set into the finite set of maps into the
  -- admissible values, and is injective on it since every `β` in it vanishes off these faces.
  have := hS.to_subtype
  refine Set.Finite.of_finite_image
    (f := fun β (F : {F : LatticeFaceIndex n N | latticeFace ρ F ⊆ Y}) => β F) ?_ ?_
  · refine (Set.Finite.pi' fun _ => hV).subset ?_
    rintro _ ⟨β, ⟨hint, hsupp⟩, rfl⟩ F
    dsimp only
    refine ⟨hint F, ?_⟩
    by_cases h : β F = 0
    · rw [h, abs_zero]
      exact abs_nonneg A
    · exact (hsupp F h).2.trans (le_abs_self A)
  · rintro β ⟨-, hsupp⟩ β' ⟨-, hsupp'⟩ h
    funext F
    by_cases hF : latticeFace ρ F ⊆ Y
    · exact congrFun h ⟨F, hF⟩
    · have h0 : β F = 0 := by
        by_contra h'
        exact hF (hsupp F h').1
      have h0' : β' F = 0 := by
        by_contra h'
        exact hF (hsupp' F h').1
      rw [h0, h0']
/-- Difference of two integral flat decompositions (Simon Ch. 6, proof of 7.2): `R := R₁ − R₂` and
`S := S₁ − S₂` are integer multiplicity (by the linear-combination hypothesis with `a = 1`,
`b = −1`), `∂R + S = (∂R₁ + S₁) − (∂R₂ + S₂)`, and `M(R) + M(S) ≤ (M(R₁) + M(S₁)) + (M(R₂) + M(S₂))`
by subadditivity of mass. -/
theorem Submission.fiw_tb_flat_sub :
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ),
      IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ →
      (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) →
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (R₁ R₂ : GeometricCurrentOn U (n + 1)) (S₁ S₂ : GeometricCurrentOn U n),
      IsIntegerMultiplicity R₁ → IsIntegerMultiplicity R₂ → IsIntegerMultiplicity S₁ →
      IsIntegerMultiplicity S₂ →
      ∃ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n),
        IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
        (∀ ω, R.boundary ω + S ω = (R₁.boundary ω + S₁ ω) - (R₂.boundary ω + S₂ ω)) ∧
        R.mass + S.mass ≤ (R₁.mass + S₁.mass) + (R₂.mass + S₂.mass) := by
  intro hLC P n U hU R₁ R₂ S₁ S₂ hR₁ hR₂ hS₁ hS₂
  -- The difference `Z₁ − Z₂` of two currents is a current (sequential continuity by `Tendsto.sub`).
  have hdiff : ∀ (k : ℕ) (Z₁ Z₂ : GeometricCurrentOn U k), ∃ Z : GeometricCurrentOn U k,
      ∀ ω, Z ω = Z₁ ω - Z₂ ω := fun k Z₁ Z₂ =>
    ⟨{ toCurrent := Z₁.toCurrent - Z₂.toCurrent
       continuous' := fun ωs h => by
         simpa using (Z₁.continuous' ωs h).sub (Z₂.continuous' ωs h) }, fun ω => rfl⟩
  -- `M(Z₁ − Z₂) ≤ M(Z₁) + M(Z₂)`: if `ω` is mass-admissible then so is `−ω`, and `Z₂(−ω) = −Z₂(ω)`.
  have hmass : ∀ (k : ℕ) (Z₁ Z₂ Z : GeometricCurrentOn U k), (∀ ω, Z ω = Z₁ ω - Z₂ ω) →
      Z.mass ≤ Z₁.mass + Z₂.mass := by
    intro k Z₁ Z₂ Z hZ
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    have hneg : -ω ∈ massAdmissibleOn U k U := by
      refine ⟨(-ω).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (-(ω : DifferentialForm (Eucl P) k) x) ≤ 1
      rw [covectorEuclideanNorm_neg]
      exact hω.2 x
    have hZ₂ : Z₂ (-ω) = -Z₂ ω := map_neg Z₂.toCurrent ω
    calc ENNReal.ofReal (Z ω) = ENNReal.ofReal (Z₁ ω + Z₂ (-ω)) := by
          rw [hZ ω, hZ₂, sub_eq_add_neg]
      _ ≤ ENNReal.ofReal (Z₁ ω) + ENNReal.ofReal (Z₂ (-ω)) := ENNReal.ofReal_add_le
      _ ≤ Z₁.mass + Z₂.mass := add_le_add (Z₁.le_massOn hω) (Z₂.le_massOn hneg)
  obtain ⟨R, hR⟩ := hdiff (n + 1) R₁ R₂
  obtain ⟨S, hS⟩ := hdiff n S₁ S₂
  refine ⟨R, S, hLC P (n + 1) U hU R₁ R₂ R 1 (-1) hR₁ hR₂ fun ω => ?_,
    hLC P n U hU S₁ S₂ S 1 (-1) hS₁ hS₂ fun ω => ?_, fun ω => ?_, ?_⟩
  · rw [hR ω]
    push_cast
    ring
  · rw [hS ω]
    push_cast
    ring
  · rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply,
      GeometricCurrentOn.boundary_apply, hR, hS]
    ring
  · calc R.mass + S.mass ≤ (R₁.mass + R₂.mass) + (S₁.mass + S₂.mass) :=
          add_le_add (hmass _ R₁ R₂ R hR) (hmass _ S₁ S₂ S hS)
      _ = (R₁.mass + S₁.mass) + (R₂.mass + S₂.mass) := add_add_add_comm _ _ _ _

/-- **Continuity criterion on `𝒟ⁿ(U)`** (the topology of Simon Ch. 6, §1, p. 134, and the
continuity required in 2.1): if for each compact `K ⊆ U` there is `A` with `|L(ω)| ≤ A·C`
whenever `spt ω ⊆ K` and `|ω(x)| ≤ C` for all `x` (the Euclidean coefficient norm of 1.15), then
`L(ω_q) → 0` for every null sequence `ω_q → 0` of test forms.  By
`fiw_ims_sc_converges_zero_small` all `spt ω_q` lie in one compact `K ⊆ U` and
`sup_x |ω_q(x)| → 0`; for `ε > 0` and `δ = ε / (|A| + 1)`, eventually
`|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.  Neither linearity of `L` nor a sign of `A` is used. -/
theorem Submission.fiw_ims_sc_continuous_of_bound : ∀ (P n : ℕ) (U : Set (Eucl P)) (L : TestFormOn U n → ℝ), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ A : ℝ, ∀ (ω : TestFormOn U n) (C : ℝ), 0 < C → tsupport ((ω : DifferentialForm (Eucl P) n)) ⊆ K → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) → |L ω| ≤ A * C) → ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 → Tendsto (fun q => L (ωs q)) atTop (𝓝 0) := by
  intro P n U L hL ωs hωs
  -- One compact `K ⊆ U` carries every `spt ω_q`, and `sup_x |ω_q(x)| → 0`.
  obtain ⟨K, hK, hKU, hsupp, hsmall⟩ :=
    Submission.fiw_ims_sc_converges_zero_small P n U ωs hωs
  -- The hypothesis on `K`: `|L(ω)| ≤ A·C` whenever `spt ω ⊆ K` and `|ω| ≤ C`.
  obtain ⟨A, hA⟩ := hL K hK hKU
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA1 : 0 < |A| + 1 := by positivity
  have hδ : 0 < ε / (|A| + 1) := div_pos hε hA1
  -- Eventually `|ω_q| ≤ δ = ε / (|A| + 1)`, hence `|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.
  filter_upwards [hsmall _ hδ] with q hq
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs q)| ≤ A * (ε / (|A| + 1)) := hA (ωs q) _ hδ (hsupp q) hq
    _ ≤ |A| * (ε / (|A| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self A) hδ.le
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hA1]
      nlinarith [abs_nonneg A]
/-- **Integer-weighted series estimate** (behind the `M`-absolutely convergent integer series
`∑_r c_r T_r` of currents, Simon Ch. 6, 3.13, pp. 149–150, used in the proof of 7.2).  If
`ofReal |a_r| ≤ m_r · ofReal C` for every `r` and `∑' r, |c_r| m_r < ∞` in `[0, ∞]`, then
`r ↦ c_r a_r` is summable and `ofReal |∑' r, c_r a_r| ≤ ofReal C · ∑' r, |c_r| m_r`.
Termwise `ofReal |c_r a_r| = |c_r| · ofReal |a_r| ≤ ofReal C · (|c_r| m_r)`, so
`∑' r, ofReal |c_r a_r|` is finite; this gives absolute summability, and the estimate follows
from `|∑' r, x_r| ≤ ∑' r, |x_r|`. -/
theorem Submission.fiw_ims_sc_series_bound : ∀ (a : ℕ → ℝ) (c : ℕ → ℤ) (m : ℕ → ℝ≥0∞) (C : ℝ), (∀ r, ENNReal.ofReal |a r| ≤ m r * ENNReal.ofReal C) → (∑' r, ((c r).natAbs : ℝ≥0∞) * m r) < ∞ → Summable (fun r => (c r : ℝ) * a r) ∧ ENNReal.ofReal |∑' r, (c r : ℝ) * a r| ≤ ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r := by
  intro a c m C ha hsum
  -- `ofReal |(c_r : ℝ)| = |c_r|` in `[0, ∞]`.
  have hc : ∀ r, ENNReal.ofReal |(c r : ℝ)| = ((c r).natAbs : ℝ≥0∞) := fun r => by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, ENNReal.ofReal_natCast]
  -- Termwise bound `ofReal |c_r a_r| ≤ ofReal C · (|c_r| m_r)`.
  have hterm : ∀ r, ENNReal.ofReal |(c r : ℝ) * a r| ≤
      ENNReal.ofReal C * (((c r).natAbs : ℝ≥0∞) * m r) := fun r => by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), hc]
    calc ((c r).natAbs : ℝ≥0∞) * ENNReal.ofReal |a r|
        ≤ ((c r).natAbs : ℝ≥0∞) * (m r * ENNReal.ofReal C) := by gcongr; exact ha r
      _ = ENNReal.ofReal C * (((c r).natAbs : ℝ≥0∞) * m r) := by ring
  -- Summing: `∑' ofReal |c_r a_r| ≤ ofReal C · ∑' |c_r| m_r < ∞`.
  have hle : ∑' r, ENNReal.ofReal |(c r : ℝ) * a r| ≤
      ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hterm
  have hfin : ∑' r, ENNReal.ofReal |(c r : ℝ) * a r| ≠ ∞ :=
    (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum)).ne
  -- Absolute summability, hence summability.
  have habs : Summable fun r => |(c r : ℝ) * a r| :=
    (ENNReal.summable_toReal hfin).congr fun r => ENNReal.toReal_ofReal (abs_nonneg _)
  refine ⟨habs.of_abs, ?_⟩
  -- `|∑' x_r| ≤ ∑' |x_r|`, and `ofReal` commutes with the nonnegative sum.
  have hnorm : Summable fun r => ‖(c r : ℝ) * a r‖ := by simpa only [Real.norm_eq_abs] using habs
  have htri : |∑' r, (c r : ℝ) * a r| ≤ ∑' r, |(c r : ℝ) * a r| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  calc ENNReal.ofReal |∑' r, (c r : ℝ) * a r|
      ≤ ENNReal.ofReal (∑' r, |(c r : ℝ) * a r|) := ENNReal.ofReal_le_ofReal htri
    _ = ∑' r, ENNReal.ofReal |(c r : ℝ) * a r| :=
        ENNReal.ofReal_tsum_of_nonneg (fun r => abs_nonneg _) habs
    _ ≤ ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r := hle
/-- Mass bound: if `η` is supported in `V` and `|η(x)| ≤ C` everywhere (Euclidean covector
norm) with `C > 0`, then `|X(η)| ≤ M_V(X) · C` in `[0, ∞]`. -/
theorem Submission.fiw_ims_mass_bound :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U k) (V : Set (Eucl P))
      (η : TestFormOn U k) (C : ℝ), 0 < C → tsupport (η : DifferentialForm (Eucl P) k) ⊆ V →
      (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) k) x) ≤ C) →
      ENNReal.ofReal |X η| ≤ X.massOn V * ENNReal.ofReal C := by
  intro P k U X V η C hC hV hη
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
  -- A sign `s = ±C⁻¹` with `s X(η) = C⁻¹ |X(η)|`.
  obtain ⟨s, hs, hsX⟩ : ∃ s : ℝ, |s| = C⁻¹ ∧ s * X η = C⁻¹ * |X η| := by
    rcases le_or_gt 0 (X η) with h | h
    · exact ⟨C⁻¹, abs_of_pos (inv_pos.mpr hC), by rw [abs_of_nonneg h]⟩
    · exact ⟨-C⁻¹, by rw [abs_neg, abs_of_pos (inv_pos.mpr hC)], by rw [abs_of_neg h]; ring⟩
  -- `s η` is mass-admissible for `V`: supported in `V`, pointwise norm `≤ C⁻¹ C = 1`.
  have hadm : s • η ∈ massAdmissibleOn U k V := by
    refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hV, fun x => ?_⟩
    change covectorEuclideanNorm (s • (η : DifferentialForm (Eucl P) k) x) ≤ 1
    rw [hsmul, hs, inv_mul_le_iff₀ hC, mul_one]
    exact hη x
  -- Definition of mass and linearity of `X`: `ofReal (C⁻¹ |X(η)|) ≤ M_V(X)`.
  have hle := X.le_massOn hadm
  rw [map_smul, smul_eq_mul, hsX] at hle
  -- Undo the scaling by `C⁻¹`.
  calc ENNReal.ofReal |X η| = ENNReal.ofReal (C⁻¹ * |X η| * C) := by
        rw [mul_comm C⁻¹, mul_assoc, inv_mul_cancel₀ hC.ne', mul_one]
    _ = ENNReal.ofReal (C⁻¹ * |X η|) * ENNReal.ofReal C :=
        ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hC.le) (abs_nonneg _))
    _ ≤ X.massOn V * ENNReal.ofReal C := by gcongr

/-- Series of currents: if `∑' r, |c_r| M_W(T_r) < ∞` for every `W ⊂⊂ U`, then `∑ c_r T_r`
converges unconditionally on every test form to a current `S` with
`M_W(S) ≤ ∑' r, |c_r| M_W(T_r)` for every set `W`. -/
theorem Submission.fiw_ims_series_current :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : ℕ → GeometricCurrentOn U n) (c : ℕ → ℤ),
      (∀ W, CompactlyContainedOpen W U →
        (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W) < ∞) →
      ∃ S : GeometricCurrentOn U n, (∀ ω, HasSum (fun r => (c r : ℝ) * T r ω) (S ω)) ∧
        ∀ W, S.massOn W ≤ ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W := by
  intro P n U hU T c hT
  -- Every compact `K ⊆ U` lies in some `W ⊂⊂ U`.
  have hW : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      ∃ W, CompactlyContainedOpen W U ∧ K ⊆ W := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨W, ⟨hWo, hWc, hWU⟩, hKW⟩
  -- Core estimate: for `ω` supported in `V` with `|ω| ≤ C`, the series converges and
  -- `|∑' r, c_r T_r(ω)| ≤ C ∑' r, |c_r| M_V(T_r)` in `[0, ∞]`.
  have hcore : ∀ (V : Set (Eucl P)) (ω : TestFormOn U n) (C : ℝ), 0 < C →
      tsupport (ω : DifferentialForm (Eucl P) n) ⊆ V →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn V) < ∞ →
      Summable (fun r => (c r : ℝ) * T r ω) ∧
        ENNReal.ofReal |∑' r, (c r : ℝ) * T r ω| ≤
          ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn V :=
    fun V ω C hC hV hω hfin =>
      Submission.fiw_ims_sc_series_bound (fun r => T r ω) c (fun r => (T r).massOn V) C
        (fun r => Submission.fiw_ims_mass_bound P n U (T r) V ω C hC hV hω) hfin
  -- The series converges on every test form: `tsupport ω` is a compact subset of `U`.
  have hsum : ∀ ω : TestFormOn U n, Summable (fun r => (c r : ℝ) * T r ω) := by
    intro ω
    obtain ⟨C, hC, hω⟩ := Submission.fiw_ims_sc_testForm_bounded P n U ω
    obtain ⟨W, hWU, hKW⟩ := hW (tsupport (ω : DifferentialForm (Eucl P) n))
      ω.property.1.2 ω.property.2
    exact (hcore W ω C hC hKW hω (hT W hWU)).1
  -- The sum `S₀(ω) = ∑' r, c_r T_r(ω)` is linear in `ω`.
  let S₀ : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑' r, (c r : ℝ) * T r ω
      map_add' := fun ω η => by
        simp only [map_add, mul_add]
        exact (hsum ω).tsum_add (hsum η)
      map_smul' := fun a ω => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun r => mul_left_comm _ _ _ }
  -- Sequential continuity: on forms supported in a compact `K ⊆ U` with `|ω| ≤ C`,
  -- `|S₀(ω)| ≤ A C` with `A = ∑' r, |c_r| M_W(T_r)` for some `W ⊂⊂ U` containing `K`.
  have hcont : ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 →
      Tendsto (fun q => S₀ (ωs q)) atTop (𝓝 0) := by
    refine Submission.fiw_ims_sc_continuous_of_bound P n U S₀ fun K hK hKU => ?_
    obtain ⟨W, hWU, hKW⟩ := hW K hK hKU
    have hA := hT W hWU
    refine ⟨(∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W).toReal,
      fun ω C hC hω hωC => ?_⟩
    have h : ENNReal.ofReal |S₀ ω| ≤
        ENNReal.ofReal (C * (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W).toReal) := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hA.ne]
      exact (hcore W ω C hC (hω.trans hKW) hωC hA).2
    rw [mul_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le ENNReal.toReal_nonneg)).1 h
  refine ⟨⟨S₀, hcont⟩, fun ω => (hsum ω).hasSum, fun W => ?_⟩
  -- Mass bound: test the admissible forms of `M_W` with `C = 1`.
  rcases eq_top_or_lt_top (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W) with hA | hA
  · rw [hA]
    exact le_top
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (S₀ ω) ≤ ENNReal.ofReal |S₀ ω| := ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal 1 * ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W :=
      (hcore W ω 1 one_pos hω.1 hω.2 hA).2
    _ = ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W := by
      rw [ENNReal.ofReal_one, one_mul]
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
/-- Local finiteness for an integer series of currents `∑ c_r τ(M_r, θ_r, ξ_r)` (Simon Ch. 6, 3.13,
used for `R^(ℓ)`, `S^(ℓ)` in the proof of 7.2): with `Θ = ∑' r, |c_r| 1_{M_r} θ_r` and
`∑' r, |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞` for each `W ⊂⊂ U`, `Θ` is locally `Hⁿ`-integrable in `U`
and `Hⁿ`-a.e. `x` lies in `M_r` for only finitely many `r` with `c_r ≠ 0`.  Termwise integration
(`lintegral_tsum`) gives `∫_W Θ dHⁿ < ∞` on each `W ⊂⊂ U`, so `Θ < ∞` a.e. near each point of
`U`, hence a.e. on `U` (`ℝ^P` is second countable); at such `x` each such `r` adds at least `1`
to `Θ(x)`, and off `U` no `M_r` contains `x`. -/
theorem Submission.fiw_ims_overlap_finite :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (c : ℕ → ℤ), (∀ r, M r ⊆ U) →
        (∀ r, NullMeasurableSet (M r) (μHE[n] : Measure (Eucl P))) →
        (∀ r, ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
          IntegrableOn (θ r) (M r ∩ K) (μHE[n] : Measure (Eucl P))) →
        (∀ r, ∀ x ∈ M r, 1 ≤ θ r x) →
        (∀ W, CompactlyContainedOpen W U →
          (∑' r, ((c r).natAbs : ℝ≥0∞) *
            ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) →
        (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
          (∫⁻ x in K, ∑' r, ((c r).natAbs : ℝ≥0∞) *
            (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x
              ∂(μHE[n] : Measure (Eucl P))) < ∞) ∧
        ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), {r | c r ≠ 0 ∧ x ∈ M r}.Finite := by
  intro P n U hU M θ c hMU hMnull hint hθ1 hsum
  set H : Measure (Eucl P) := (μHE[n] : Measure (Eucl P))
  -- `g r = |c_r| 1_{M_r} θ_r` and `Θ = ∑' r, g r`.
  set g : ℕ → Eucl P → ℝ≥0∞ := fun r x =>
    ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x with hg
  set Θ : Eucl P → ℝ≥0∞ := fun x => ∑' r, g r x with hΘ
  -- Steps 1–2: on `W ⊂⊂ U` every `g r` is a.e.-measurable (`θ_r` is integrable on
  -- `M_r ∩ closure W`), so `∫_W Θ = ∑' r, |c_r| ∫_{M_r ∩ W} θ_r < ∞`.
  have hW : ∀ W, CompactlyContainedOpen W U →
      AEMeasurable Θ (H.restrict W) ∧ ∫⁻ x in W, Θ x ∂H < ∞ := by
    intro W hWcc
    obtain ⟨hWo, hWc, hWU⟩ := hWcc
    have hnull : ∀ r, NullMeasurableSet (M r) (H.restrict W) := fun r =>
      (hMnull r).mono Measure.restrict_le_self
    have hterm : ∀ r, AEMeasurable (g r) (H.restrict W) := by
      intro r
      have hi : IntegrableOn (θ r) (M r ∩ W) H :=
        (hint r _ hWc hWU).mono_set (inter_subset_inter_right _ subset_closure)
      have hmeas : AEMeasurable (fun y => ENNReal.ofReal (θ r y))
          ((H.restrict W).restrict (M r)) := by
        rw [Measure.restrict_restrict' hWo.measurableSet]
        exact hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      exact ((aemeasurable_indicator_iff₀ (hnull r)).2 hmeas).const_mul _
    refine ⟨AEMeasurable.tsum hterm, ?_⟩
    have hEq : ∫⁻ x in W, Θ x ∂H =
        ∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂H := by
      rw [hΘ, lintegral_tsum hterm]
      refine tsum_congr fun r => ?_
      rw [hg, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_indicator₀ (hnull r),
        Measure.restrict_restrict' hWo.measurableSet]
    rw [hEq]
    exact hsum W ⟨hWo, hWc, hWU⟩
  -- Every compact `K ⊆ U` lies in some `W ⊂⊂ U`.
  have hcover : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      ∃ W, CompactlyContainedOpen W U ∧ K ⊆ W := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨W, ⟨hWo, hWc, hWU⟩, hKW⟩
  -- Step 3: conclusion (a), as `∫_K Θ ≤ ∫_W Θ` for `K ⊆ W ⊂⊂ U`.
  refine ⟨fun K hK hKU => ?_, ?_⟩
  · obtain ⟨W, hWcc, hKW⟩ := hcover K hK hKU
    exact (lintegral_mono_set hKW).trans_lt (hW W hWcc).2
  -- Step 4: `N = {x ∈ U | Θ x = ∞}` is null: each `x ∈ U` has a neighbourhood `W ⊂⊂ U` on which
  -- `Θ < ∞` a.e., and `ℝ^P` is second countable.
  set N : Set (Eucl P) := {x | x ∈ U ∧ Θ x = ∞}
  have hN0 : H N = 0 := by
    refine measure_null_of_locally_null N fun x hx => ?_
    obtain ⟨W, hWcc, hxW⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx.1)
    obtain ⟨hmeas, hfin⟩ := hW W hWcc
    have hae : ∀ᵐ y ∂H, y ∈ W → Θ y < ∞ :=
      (ae_restrict_iff' hWcc.1.measurableSet).1 (ae_lt_top' hmeas hfin.ne)
    refine ⟨N ∩ W, inter_mem_nhdsWithin N (hWcc.1.mem_nhds (hxW rfl)), ?_⟩
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    simp only [mem_ofPred_eq, not_imp, not_lt, top_le_iff]
    exact ⟨hy.2, hy.1.2⟩
  -- Step 5: conclusion (b).  For `x ∈ U \ N`, every `r` with `c_r ≠ 0` and `x ∈ M_r` has
  -- `g r x ≥ 1` while `∑' r, g r x < ∞`; for `x ∉ U` no `M_r` contains `x`.
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with x hxN
  by_cases hxU : x ∈ U
  · have hΘx : Θ x ≠ ∞ := fun h => hxN ⟨hxU, h⟩
    refine (ENNReal.finite_const_le_of_tsum_ne_top hΘx one_ne_zero).subset ?_
    rintro r ⟨hc, hxM⟩
    have h1 : (1 : ℝ≥0∞) ≤ ((c r).natAbs : ℝ≥0∞) := by
      exact_mod_cast Int.natAbs_pos.2 hc
    have h2 : (1 : ℝ≥0∞) ≤ (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x := by
      rw [indicator_of_mem hxM]
      simpa using ENNReal.ofReal_le_ofReal (hθ1 r x hxM)
    simpa [hg] using mul_le_mul' h1 h2
  · exact finite_empty.subset fun r hr => hxU (hMU r hr.2)
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

/-- One term of Simon Ch. 6, 3.1 (‡): for a rectifiable triple `(M, θ, ξ)` in `U`, an open
`W ⊂⊂ U` and a continuous `n`-form `ω` with `tsupport ω ⊆ W` and `‖ω(x)‖ ≤ B`, the integrand
`1_M θ ⟨ω, ξ⟩` is `Hⁿ`-a.e. strongly measurable and `∫ |1_M θ ⟨ω, ξ⟩| dHⁿ ≤ B ∫_{M ∩ W} θ dHⁿ`,
since `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖` for `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` (`Submission.fiw_ims_tt_unit_bound`). -/
theorem Submission.fiw_ims_tt_term_bound :
    ∀ (P n : ℕ) (U W M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
      (ω : Eucl P → Covector (Eucl P) n) (B : ℝ), IsRectifiableTriple U n M θ ξ →
      CompactlyContainedOpen W U → Continuous ω → tsupport ω ⊆ W → (∀ x, ‖ω x‖ ≤ B) →
      AEStronglyMeasurable (M.indicator fun x => θ x * ξ x (ω x)) (μHE[n] : Measure (Eucl P)) ∧
      ∫⁻ x, ‖M.indicator (fun y => θ y * ξ y (ω y)) x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤
        ENNReal.ofReal B * ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U W M θ ξ ω B htri hW hω hωW hB
  obtain ⟨hWo, hLc, hLU⟩ := hW
  set g : Eucl P → ℝ := fun x => θ x * ξ x (ω x)
  -- `g` vanishes off `tsupport ω ⊆ W`.
  have hg0 : ∀ x, x ∉ W → g x = 0 := by
    intro x hx
    have hωx : ω x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hωW h)
    show θ x * ξ x (ω x) = 0
    rw [hωx, map_zero, mul_zero]
  have hML : NullMeasurableSet (M ∩ closure W) (μHE[n] : Measure (Eucl P)) :=
    htri.nullMeasurableSet.inter isClosed_closure.measurableSet.nullMeasurableSet
  have hMW : NullMeasurableSet (M ∩ W) (μHE[n] : Measure (Eucl P)) :=
    htri.nullMeasurableSet.inter hWo.measurableSet.nullMeasurableSet
  -- Hence `1_M g = 1_{M ∩ closure W} g`.
  have hG : M.indicator g = (M ∩ closure W).indicator g := by
    funext x
    by_cases hxL : x ∈ closure W
    · by_cases hxM : x ∈ M <;> simp [Set.indicator, hxL, hxM]
    · simp [Set.indicator, hxL, hg0 x fun hxW => hxL (subset_closure hxW)]
  refine ⟨?_, ?_⟩
  · -- On `M ∩ closure W`: `θ` is integrable (`closure W` is a compact subset of `U`), `ξ` is
    -- measurable (restricted from `M`), `ω` is continuous, and `(v, α) ↦ v α` is continuous.
    have hθ : AEStronglyMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict (M ∩ closure W)) :=
      (htri.integrableOn (closure W) hLc hLU).aestronglyMeasurable
    have hξ : AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict (M ∩ closure W)) :=
      htri.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have hev : Continuous fun p : NVector (Eucl P) n × Covector (Eucl P) n => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    rw [hG, aestronglyMeasurable_indicator_iff₀ hML]
    exact hθ.mul (hev.comp_aestronglyMeasurable (hξ.prodMk hω.aestronglyMeasurable))
  · -- `Hⁿ`-a.e. `|1_M g| ≤ 1_{M ∩ W} B θ`: on `M ∩ W`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ`
    -- orthonormal, so `|ξ(x)(ω(x))| ≤ ‖ω(x)‖ ≤ B`; elsewhere `1_M g` vanishes.
    have hae : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ‖M.indicator g x‖ₑ ≤
        (M ∩ W).indicator (fun y => ENNReal.ofReal B * ENNReal.ofReal (θ y)) x := by
      filter_upwards [(ae_restrict_iff'₀ htri.nullMeasurableSet).1 htri.orients] with x hx
      by_cases hxM : x ∈ M
      · by_cases hxW : x ∈ W
        · obtain ⟨τ, hτ, -, hξx⟩ := hx hxM
          have hθx : 0 < θ x := htri.pos x hxM
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
          have hub : |ξ x (ω x)| ≤ B :=
            (Submission.fiw_ims_tt_unit_bound P n τ (ξ x) hτ hξx (ω x)).trans (hB x)
          rw [Set.indicator_of_mem hxM, Set.indicator_of_mem (show x ∈ M ∩ W from ⟨hxM, hxW⟩)]
          show ‖θ x * ξ x (ω x)‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (θ x)
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hB0, abs_mul, abs_of_pos hθx,
            mul_comm B]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hub hθx.le)
        · simp [Set.indicator_of_mem hxM, hg0 x hxW]
      · simp [Set.indicator_of_notMem hxM]
    calc ∫⁻ x, ‖M.indicator g x‖ₑ ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ x, (M ∩ W).indicator (fun y => ENNReal.ofReal B * ENNReal.ofReal (θ y)) x
            ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hae
      _ = ∫⁻ x in M ∩ W, ENNReal.ofReal B * ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_indicator₀ hMW _
      _ = ENNReal.ofReal B * ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Termwise integration of an integer series of rectifiable triples** (Simon Ch. 6, 3.1 (‡)
for the `M`-absolutely convergent series of 3.13 and the proof of 7.2).
Let `(M_r, θ_r, ξ_r)` be rectifiable triples in `U` and `c_r ∈ ℤ` with
`∑_r |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞` for every `W ⊂⊂ U`.  Then for every `ω ∈ 𝒟ⁿ(U)`, with
`F_r := 1_{M_r} c_r θ_r ⟨ω, ξ_r⟩`, the series `∑_r c_r τ(M_r, θ_r, ξ_r)(ω)` has sum
`∫ ∑_r F_r dHⁿ`.  Choose an open `W ⊂⊂ U` with `tsupport ω ⊆ W` and a bound `‖ω(x)‖ ≤ B`;
`Submission.fiw_ims_tt_term_bound` makes each `F_r` a.e. strongly measurable with
`∫ |F_r| dHⁿ ≤ |c_r| B ∫_{M_r ∩ W} θ_r dHⁿ`, so `∑_r ∫ |F_r| dHⁿ < ∞` and the series can be
integrated termwise (`hasSum_integral_of_summable_integral_norm`); finally
`∫ F_r dHⁿ = c_r ∫_{M_r} θ_r ⟨ω, ξ_r⟩ dHⁿ = c_r τ(M_r, θ_r, ξ_r)(ω)`. -/
theorem Submission.fiw_ims_tsum_tau :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ)
      (ξ : ℕ → Eucl P → NVector (Eucl P) n) (c : ℕ → ℤ),
      (∀ r, IsRectifiableTriple U n (M r) (θ r) (ξ r)) →
      (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) →
      ∀ ω : TestFormOn U n, HasSum (fun r => (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω)
        (∫ x, ∑' r, (M r).indicator (fun y => (c r : ℝ) * (θ r y * ξ r y
          ((ω : DifferentialForm (Eucl P) n) y))) x ∂(μHE[n] : Measure (Eucl P))) := by
  intro P n U hU M θ ξ c htri hsum ω
  -- `ω` is smooth (hence continuous) with compact support `tsupport ω ⊆ U`.
  have hωc : Continuous (ω : DifferentialForm (Eucl P) n) := ω.2.1.1.continuous
  have hωK : HasCompactSupport (ω : DifferentialForm (Eucl P) n) := ω.2.1.2
  -- Localization: an open `W ⊂⊂ U` with `tsupport ω ⊆ W`, and `‖ω(x)‖ ≤ B` for all `x`.
  obtain ⟨W, hWo, hKW, hLU, hLc⟩ :=
    exists_open_between_and_isCompact_closure hωK.isCompact hU ω.2.2
  have hW : CompactlyContainedOpen W U := ⟨hWo, hLc, hLU⟩
  obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support hωK
  -- `F r = c_r G r`, where `G r := 1_{M_r} θ_r ⟨ω, ξ_r⟩` is controlled by the child lemma.
  let G : ℕ → Eucl P → ℝ := fun r =>
    (M r).indicator fun y => θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y)
  let F : ℕ → Eucl P → ℝ := fun r =>
    (M r).indicator fun y => (c r : ℝ) * (θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y))
  have hFG : ∀ r x, F r x = (c r : ℝ) * G r x := by
    intro r x
    by_cases hx : x ∈ M r <;> simp [F, G, hx]
  have hG : ∀ r, AEStronglyMeasurable (G r) (μHE[n] : Measure (Eucl P)) ∧
      ∫⁻ x, ‖G r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal B *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P)) := fun r =>
    Submission.fiw_ims_tt_term_bound P n U W (M r) (θ r) (ξ r) (ω : DifferentialForm (Eucl P) n)
      B (htri r) hW hωc hKW hB
  -- `‖(c_r : ℝ)‖ₑ = |c_r|`.
  have hc : ∀ r, ‖(c r : ℝ)‖ₑ = ((c r).natAbs : ℝ≥0∞) := fun r => by
    rw [Real.enorm_eq_ofReal_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
  have hFm : ∀ r, AEStronglyMeasurable (F r) (μHE[n] : Measure (Eucl P)) := fun r => by
    have : F r = fun x => (c r : ℝ) * G r x := funext (hFG r)
    rw [this]
    exact (hG r).1.const_mul _
  -- `∫ |F_r| dHⁿ ≤ |c_r| B ∫_{M_r ∩ W} θ_r dHⁿ`.
  have hFle : ∀ r, ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal B *
      (((c r).natAbs : ℝ≥0∞) *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) := fun r =>
    calc ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P))
        = ∫⁻ x, ((c r).natAbs : ℝ≥0∞) * ‖G r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
          simp_rw [hFG r, enorm_mul, hc]
      _ = ((c r).natAbs : ℝ≥0∞) * ∫⁻ x, ‖G r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
      _ ≤ ((c r).natAbs : ℝ≥0∞) * (ENNReal.ofReal B *
            ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) := by
          gcongr
          exact (hG r).2
      _ = _ := mul_left_comm _ _ _
  -- Hence `∑_r ∫ |F_r| dHⁿ ≤ B ∑_r |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞`.
  have hFsum : ∑' r, ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B))
      (hsum W hW).ne) ?_
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hFle
  have hFi : ∀ r, Integrable (F r) (μHE[n] : Measure (Eucl P)) := fun r =>
    ⟨hFm r, (ENNReal.le_tsum (f := fun r => ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P))) r).trans_lt
      (lt_top_iff_ne_top.2 hFsum)⟩
  have hFs : Summable fun r => ∫ x, ‖F r x‖ ∂(μHE[n] : Measure (Eucl P)) :=
    (ENNReal.summable_toReal hFsum).congr fun r => (integral_norm_eq_lintegral_enorm (hFm r)).symm
  -- Termwise integration, and `∫ F_r dHⁿ = c_r τ(M_r, θ_r, ξ_r)(ω)`.
  have hint : ∀ r, ∫ x, F r x ∂(μHE[n] : Measure (Eucl P)) =
      (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω := fun r => by
    simp only [F]
    rw [integral_indicator₀ (htri r).nullMeasurableSet, integral_const_mul]
    rfl
  have hS := hasSum_integral_of_summable_integral_norm hFi hFs
  simp only [hint] at hS
  exact hS

/-- **Series of integer multiplicity currents, Simon Ch. 6, 3.13 (p. 149), as used in the proof
of 7.2 (p. 170).**  Under tangent locality in `U`, an `M`-absolutely convergent series
`∑ c_r τ(M_r, θ_r, ξ_r)` with `c_r ∈ ℤ` and integer `θ_r` is one integer multiplicity current
`τ(M', θ', ξ')`.  Off an `Hⁿ`-null set, only finitely many `M_r` with `c_r ≠ 0` contain `x`,
each `ξ_r` orients `M_r` at `x`, and `ξ_r(x) = ±ξ_{r'}(x)` whenever `x ∈ M_r ∩ M_{r'}`.  With
`ξ̂ = ξ_{r(x)}` for the first index `r(x)` of an `M_r ∋ x` and `ξ_r = σ_r ξ̂` (`σ_r = ±1`),
`θ̂ = ∑' r, 1_{M_r} c_r σ_r θ_r` is an integer-valued finite sum bounded by
`∑' r, |c_r| 1_{M_r} θ_r`; then `M' = {θ̂ ≠ 0}`, `θ' = |θ̂|`, `ξ' = (θ̂/|θ̂|) ξ̂` give the sum of
the series. -/
theorem Submission.fiw_ims_combine : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → (∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) → (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q) → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) n) (c : ℕ → ℤ), (∀ r, IsRectifiableTriple U n (M r) (θ r) (ξ r)) → (∀ r, ∀ x ∈ M r, ∃ k : ℕ, θ r x = k) → (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) → ∃ (M' : Set (Eucl P)) (θ' : Eucl P → ℝ) (ξ' : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M' θ' ξ' ∧ (∀ x ∈ M', ∃ k : ℕ, θ' x = k) ∧ ∀ ω : TestFormOn U n, HasSum (fun r => (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω) (tauAction n M' θ' ξ' ω) := by
  intro P n U hU hTL M θ ξ c hT hθN hsum
  classical
  -- `NVector (Eucl P) n` is a normed space, but instance search does not find its
  -- pseudometrizability; the operator-norm uniformity provides it.
  have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) n) := by
    let u : UniformSpace (NVector (Eucl P) n) := PseudoMetricSpace.toUniformSpace
    have : (uniformity (NVector (Eucl P) n)).IsCountablyGenerated :=
      @EMetric.instIsCountablyGeneratedUniformity _ PseudoMetricSpace.toPseudoEMetricSpace
    exact @UniformSpace.pseudoMetrizableSpace _ u this
  /- Step 1: the exceptional null sets.  Off a null set, only finitely many `M r` with
  `c r ≠ 0` contain `x`, every `M r ∋ x` is oriented at `x` by `ξ r`, and the orientations of
  any two `M r, M r' ∋ x` agree up to sign. -/
  have hθ1 : ∀ r, ∀ x ∈ M r, 1 ≤ θ r x := by
    intro r x hx
    obtain ⟨k, hk⟩ := hθN r x hx
    have hpos := (hT r).pos x hx
    rw [hk] at hpos ⊢
    have hk0 : 0 < k := by exact_mod_cast hpos
    exact_mod_cast hk0
  obtain ⟨hΘ, hfin⟩ := Submission.fiw_ims_overlap_finite P n U hU M θ c
    (fun r => (hT r).subset) (fun r => (hT r).nullMeasurableSet) (fun r => (hT r).integrableOn)
    hθ1 hsum
  have horient : ∀ r, ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ M r →
      ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt n (M r) (θ r) x (Submodule.span ℝ (range τ)) ∧
        (ξ r x = simpleNVector τ ∨ ξ r x = -simpleNVector τ) := fun r =>
    (ae_restrict_iff'₀ (hT r).nullMeasurableSet).1 (hT r).orients
  have hsign : ∀ r r', ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ M r → x ∈ M r' →
      (ξ r x = ξ r' x ∨ ξ r x = -ξ r' x) := by
    intro r r'
    have h := Submission.fiw_ims_orientation_sign P n U (M r) (M r') (θ r) (θ r') (ξ r) (ξ r')
      (hT r) (hT r') (hTL (M r) (M r') (θ r) (θ r') (hT r).subset (hT r').subset
        (hT r).nullMeasurableSet (hT r').nullMeasurableSet (hT r).pos (hT r').pos
        (hT r).integrableOn (hT r').integrableOn)
    rw [ae_restrict_iff'₀ ((hT r).nullMeasurableSet.inter (hT r').nullMeasurableSet)] at h
    filter_upwards [h] with x hx h1 h2 using hx ⟨h1, h2⟩
  set G : Set (Eucl P) := {x | {r | c r ≠ 0 ∧ x ∈ M r}.Finite ∧
    (∀ r, x ∈ M r → ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt n (M r) (θ r) x (Submodule.span ℝ (range τ)) ∧
        (ξ r x = simpleNVector τ ∨ ξ r x = -simpleNVector τ)) ∧
    ∀ r r', x ∈ M r → x ∈ M r' → (ξ r x = ξ r' x ∨ ξ r x = -ξ r' x)}
  have hGae : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ G := by
    have h3 : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ∀ r r', x ∈ M r → x ∈ M r' →
        (ξ r x = ξ r' x ∨ ξ r x = -ξ r' x) :=
      ae_all_iff.2 fun r => ae_all_iff.2 (hsign r)
    filter_upwards [hfin, ae_all_iff.2 horient, h3] with x h1 h2 h3 using ⟨h1, h2, h3⟩
  have hGnm : NullMeasurableSet G (μHE[n] : Measure (Eucl P)) :=
    (NullMeasurableSet.of_null (ae_iff.1 hGae)).of_compl
  /- Step 2: the first index `rf x` of a set `M r` containing `x`, and the sets `A r` on which
  it equals `r`. -/
  let rf : Eucl P → ℕ := fun x => if h : ∃ r, x ∈ M r then Nat.find h else 0
  have hrf : ∀ r, ∀ x ∈ M r, x ∈ M (rf x) := by
    intro r x hx
    have h : ∃ r, x ∈ M r := ⟨r, hx⟩
    simp only [rf, dite_eq_left h]
    exact Nat.find_spec h
  have hrfA : ∀ r x, x ∈ M r → (∀ r' < r, x ∉ M r') → rf x = r := by
    intro r x hx hlt
    have h : ∃ r, x ∈ M r := ⟨r, hx⟩
    simp only [rf, dite_eq_left h]
    exact (Nat.find_eq_iff h).2 ⟨hx, hlt⟩
  have hMA : (⋃ r, M r) = ⋃ r, M r ∩ ⋂ r' ∈ {r' | r' < r}, (M r')ᶜ := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨r, hr⟩
      have h : ∃ r, x ∈ M r := ⟨r, hr⟩
      exact ⟨Nat.find h, Nat.find_spec h, fun r' hr' => Nat.find_min h hr'⟩
    · rintro ⟨r, hr, -⟩
      exact ⟨r, hr⟩
  /- Step 3: the reference orientation `ξh x = ξ (rf x) x`, a.e.-strongly measurable on
  `⋃ r, M r` because it agrees with `ξ r` on `A r`. -/
  let ξh : Eucl P → NVector (Eucl P) n := fun x => ξ (rf x) x
  have hξh : AEStronglyMeasurable ξh
      ((μHE[n] : Measure (Eucl P)).restrict (⋃ r, M r)) := by
    rw [hMA, aestronglyMeasurable_iUnion_iff]
    intro r
    have hAnm : NullMeasurableSet (M r ∩ ⋂ r' ∈ {r' | r' < r}, (M r')ᶜ)
        (μHE[n] : Measure (Eucl P)) :=
      (hT r).nullMeasurableSet.inter
        (NullMeasurableSet.iInter fun r' => NullMeasurableSet.iInter fun _ =>
          (hT r').nullMeasurableSet.compl)
    refine ((hT r).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)).congr ?_
    filter_upwards [ae_restrict_mem₀ hAnm] with x hx
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hx
    simp only [ξh, hrfA r x hx.1 hx.2]
  /- Step 4: the signs `σ r x = ±1` with `ξ r x = σ r x • ξh x` on `G ∩ M r`. -/
  let σ : ℕ → Eucl P → ℝ := fun r x => if ξ r x = ξh x then 1 else -1
  have hσ : ∀ r, AEStronglyMeasurable (σ r) ((μHE[n] : Measure (Eucl P)).restrict (M r)) := by
    intro r
    have hE : NullMeasurableSet {x | ξ r x = ξh x}
        ((μHE[n] : Measure (Eucl P)).restrict (M r)) :=
      (hT r).aestronglyMeasurable.nullMeasurableSet_eq_fun
        (hξh.mono_measure (Measure.restrict_mono (subset_iUnion M r) le_rfl))
    have h := AEStronglyMeasurable.piecewise (f := fun _ => (1 : ℝ)) (g := fun _ => (-1 : ℝ))
      hE aestronglyMeasurable_const aestronglyMeasurable_const
    convert h using 1
    funext x
    simp only [σ, Set.piecewise, mem_ofPred_eq]
  /- Step 5: `θ r` is a.e.-strongly measurable on `M r` (local integrability). -/
  have hθm : ∀ r, AEStronglyMeasurable (θ r) ((μHE[n] : Measure (Eucl P)).restrict (M r)) := by
    intro r
    apply LocallyIntegrableOn.aestronglyMeasurable
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x ((hT r).subset hx)
    refine ⟨M r ∩ closedBall x (ε / 2),
      inter_mem_nhdsWithin _ (closedBall_mem_nhds x (half_pos hε)), ?_⟩
    exact (hT r).integrableOn _ (isCompact_closedBall x (ε / 2))
      ((closedBall_subset_ball (half_lt_self hε)).trans hball)
  /- Step 6: the integer multiplicity `θh = ∑' r, t r`, `t r = 1_{M r} c r σ r θ r`. -/
  let t : ℕ → Eucl P → ℝ := fun r => (M r).indicator fun y => (c r : ℝ) * (σ r y * θ r y)
  have ht : ∀ r, AEStronglyMeasurable (t r) (μHE[n] : Measure (Eucl P)) := fun r =>
    (aestronglyMeasurable_indicator_iff₀ (hT r).nullMeasurableSet).2
      (((hσ r).mul (hθm r)).const_mul _)
  have ht0 : ∀ x r, ¬(c r ≠ 0 ∧ x ∈ M r) → t r x = 0 := by
    intro x r h
    by_cases hx : x ∈ M r
    · have hc : c r = 0 := by
        by_contra hc
        exact h ⟨hc, hx⟩
      simp [t, hx, hc]
    · simp [t, hx]
  let θh : Eucl P → ℝ := fun x => ∑' r, t r x
  have hθh_sum : ∀ x (hx : x ∈ G), θh x = ∑ r ∈ hx.1.toFinset, t r x := by
    intro x hx
    refine tsum_eq_sum fun r hr => ht0 x r ?_
    rwa [Set.Finite.mem_toFinset] at hr
  have hθh_hasSum : ∀ x ∈ G, HasSum (fun r => t r x) (θh x) := by
    intro x hx
    refine (summable_of_ne_finset_zero (s := hx.1.toFinset) fun r hr => ht0 x r ?_).hasSum
    rwa [Set.Finite.mem_toFinset] at hr
  have hθh : AEStronglyMeasurable θh (μHE[n] : Measure (Eucl P)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N x => ∑ r ∈ Finset.range N, t r x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun r _ => ht r) ?_
    filter_upwards [hGae] with x hx
    exact (hθh_hasSum x hx).tendsto_sum_nat
  -- `ofReal |t r x| = |c r| 1_{M r} ofReal (θ r x)`, so `ofReal |θh| ≤ Θ` on `G`.
  have hterm : ∀ x r, ENNReal.ofReal |t r x| =
      ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x := by
    intro x r
    by_cases hxr : x ∈ M r
    · have hσabs : |σ r x| = 1 := by
        simp only [σ]
        split_ifs <;> simp
      have htx : t r x = (c r : ℝ) * (σ r x * θ r x) := indicator_of_mem hxr _
      rw [indicator_of_mem hxr, htx, abs_mul, abs_mul, hσabs, one_mul,
        abs_of_pos ((hT r).pos x hxr), ENNReal.ofReal_mul (abs_nonneg _), ← Int.cast_abs,
        ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
    · simp [t, hxr]
  have hΘx : ∀ x ∈ G, ENNReal.ofReal |θh x| ≤
      ∑' r, ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x := by
    intro x hx
    rw [hθh_sum x hx]
    calc ENNReal.ofReal |∑ r ∈ hx.1.toFinset, t r x|
        ≤ ENNReal.ofReal (∑ r ∈ hx.1.toFinset, |t r x|) :=
          ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ r ∈ hx.1.toFinset, ENNReal.ofReal |t r x| :=
          ENNReal.ofReal_sum_of_nonneg fun r _ => abs_nonneg _
      _ = ∑ r ∈ hx.1.toFinset,
            ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x :=
          Finset.sum_congr rfl fun r _ => hterm x r
      _ ≤ _ := ENNReal.sum_le_tsum _
  /- Step 7: the new triple. -/
  set M' : Set (Eucl P) := {x | x ∈ G ∧ θh x ≠ 0} with hM'
  set θ' : Eucl P → ℝ := fun x => |θh x| with hθ'
  set ξ' : Eucl P → NVector (Eucl P) n := fun x => (θh x / |θh x|) • ξh x
  have hM'sub : M' ⊆ ⋃ r, M r := by
    intro x hx
    by_contra hcon
    simp only [mem_iUnion, not_exists] at hcon
    apply hx.2
    have h0 : ∀ r, t r x = 0 := fun r => by simp [t, hcon r]
    simp only [θh, h0, tsum_zero]
  have hM'U : M' ⊆ U := hM'sub.trans (iUnion_subset fun r => (hT r).subset)
  have hM'nm : NullMeasurableSet M' (μHE[n] : Measure (Eucl P)) := by
    have hM'eq : M' = G ∩ θh ⁻¹' {0}ᶜ := by
      ext x
      simp only [hM', mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff,
        mem_singleton_iff]
    rw [hM'eq]
    exact hGnm.inter (hθh.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl)
  have hθ'pos : ∀ x ∈ M', 0 < θ' x := fun x hx => abs_pos.2 hx.2
  have hθ'N : ∀ x ∈ M', ∃ k : ℕ, θ' x = k := by
    intro x hx
    have hint : ∀ r, ∃ z : ℤ, t r x = z := by
      intro r
      by_cases hxr : x ∈ M r
      · obtain ⟨k, hk⟩ := hθN r x hxr
        have htx : t r x = (c r : ℝ) * (σ r x * θ r x) := indicator_of_mem hxr _
        refine ⟨c r * ((if ξ r x = ξh x then 1 else -1) * k), ?_⟩
        rw [htx, hk]
        simp only [σ]
        split_ifs <;> push_cast <;> ring
      · exact ⟨0, by simp [t, hxr]⟩
    obtain ⟨z, hz⟩ : ∃ z : ℤ, θh x = z := by
      rw [hθh_sum x hx.1]
      exact Finset.sum_induction (fun r => t r x) (fun a : ℝ => ∃ z : ℤ, a = z)
        (fun a b ⟨za, ha⟩ ⟨zb, hb⟩ => ⟨za + zb, by rw [ha, hb, Int.cast_add]⟩)
        ⟨0, by rw [Int.cast_zero]⟩ fun r _ => hint r
    refine ⟨z.natAbs, ?_⟩
    simp only [hθ', hz, Nat.cast_natAbs, Int.cast_abs]
  have hθ'int : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      IntegrableOn θ' (M' ∩ K) (μHE[n] : Measure (Eucl P)) := by
    intro K hK hKU
    refine ⟨(continuous_abs.comp_aestronglyMeasurable hθh).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ x in M' ∩ K, ‖θ' x‖ₑ ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ x in M' ∩ K, ∑' r, ((c r).natAbs : ℝ≥0∞) *
            (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x ∂(μHE[n] : Measure (Eucl P)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀
            (hM'nm.inter hK.isClosed.measurableSet.nullMeasurableSet)] with x hx
          rw [Real.enorm_eq_ofReal_abs, hθ', abs_abs]
          exact hΘx x hx.1.1
      _ ≤ ∫⁻ x in K, ∑' r, ((c r).natAbs : ℝ≥0∞) *
            (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_mono_set inter_subset_right
      _ < ∞ := hΘ K hK hKU
  have hξ'meas : AEStronglyMeasurable ξ' ((μHE[n] : Measure (Eucl P)).restrict M') := by
    have h1 : AEStronglyMeasurable (fun x => θh x / |θh x|) (μHE[n] : Measure (Eucl P)) :=
      (hθh.aemeasurable.div
        (continuous_abs.measurable.comp_aemeasurable hθh.aemeasurable)).aestronglyMeasurable
    exact h1.restrict.smul (hξh.mono_measure (Measure.restrict_mono hM'sub le_rfl))
  /- Step 10 (vii): orientation of `M'`, by tangent locality for `(M r, θ r)` and `(M', θ')`. -/
  have hloc : ∀ r, ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ M r ∩ M' →
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n (M r) (θ r) x Q →
        HasWeightedApproximateTangentSpaceAt n M' θ' x Q := fun r =>
    (ae_restrict_iff'₀ ((hT r).nullMeasurableSet.inter hM'nm)).1
      (hTL (M r) M' (θ r) θ' (hT r).subset hM'U (hT r).nullMeasurableSet hM'nm (hT r).pos
        hθ'pos (hT r).integrableOn hθ'int)
  have horient' : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M'),
      ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt n M' θ' x (Submodule.span ℝ (range τ)) ∧
        (ξ' x = simpleNVector τ ∨ ξ' x = -simpleNVector τ) := by
    rw [ae_restrict_iff'₀ hM'nm]
    filter_upwards [ae_all_iff.2 hloc] with x hlocx hxM'
    obtain ⟨r0, hr0⟩ := mem_iUnion.1 (hM'sub hxM')
    have hxr : x ∈ M (rf x) := hrf r0 x hr0
    obtain ⟨τ, hτ, hTx, hξτ⟩ := hxM'.1.2.1 (rf x) hxr
    refine ⟨τ, hτ, hlocx (rf x) ⟨hxr, hxM'⟩ _ hTx, ?_⟩
    have hsgn : θh x / |θh x| = 1 ∨ θh x / |θh x| = -1 := by
      rcases lt_or_gt_of_ne hxM'.2 with h | h
      · right
        rw [abs_of_neg h, div_neg, div_self hxM'.2]
      · left
        rw [abs_of_pos h, div_self hxM'.2]
    change (θh x / |θh x|) • ξ (rf x) x = simpleNVector τ ∨
      (θh x / |θh x|) • ξ (rf x) x = -simpleNVector τ
    rcases hsgn with h | h <;> rw [h] <;> rcases hξτ with h' | h' <;> rw [h']
    · exact Or.inl (one_smul ℝ _)
    · exact Or.inr (one_smul ℝ _)
    · exact Or.inr (ContinuousLinearMap.ext fun α => by
        simp only [smul_apply, neg_apply, smul_eq_mul, neg_one_mul])
    · exact Or.inl (ContinuousLinearMap.ext fun α => by
        simp only [smul_apply, neg_apply, smul_eq_mul, neg_one_mul, neg_neg])
  refine ⟨M', θ', ξ', ⟨hM'U, hM'nm,
    (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion M
      fun r => (hT r).countablyRectifiable).mono hM'sub,
    hθ'pos, hθ'int, hξ'meas, horient'⟩, hθ'N, ?_⟩
  /- Steps 8–9: `∑' r, 1_{M r} c r θ r ⟨ω, ξ r⟩ = 1_{M'} θ' ⟨ω, ξ'⟩` a.e., and `tsum_tau`. -/
  intro ω
  have h := Submission.fiw_ims_tsum_tau P n U hU M θ ξ c hT hsum ω
  convert h using 1
  unfold tauAction
  rw [← integral_indicator₀ hM'nm]
  refine integral_congr_ae ?_
  filter_upwards [hGae] with x hx
  have hterm' : ∀ r, (M r).indicator (fun y => (c r : ℝ) *
      (θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y))) x =
        t r x * ξh x ((ω : DifferentialForm (Eucl P) n) x) := by
    intro r
    by_cases hxr : x ∈ M r
    · have htx : t r x = (c r : ℝ) * (σ r x * θ r x) := indicator_of_mem hxr _
      rw [indicator_of_mem hxr, htx]
      have hs := hx.2.2 r (rf x) hxr (hrf r x hxr)
      simp only [σ]
      split_ifs with heq
      · rw [heq]
        ring
      · rcases hs with hs | hs
        · exact absurd hs heq
        · change (c r : ℝ) * (θ r x * ξ r x _) = (c r : ℝ) * (-1 * θ r x) * ξ (rf x) x _
          rw [hs, neg_apply]
          ring
    · simp [t, hxr]
  rw [tsum_congr hterm', tsum_mul_right]
  change _ = θh x * ξh x ((ω : DifferentialForm (Eucl P) n) x)
  by_cases hxM' : x ∈ M'
  · rw [indicator_of_mem hxM']
    have hne : |θh x| ≠ 0 := abs_ne_zero.2 hxM'.2
    simp only [θ', ξ', smul_apply, smul_eq_mul]
    field_simp
  · rw [indicator_of_notMem hxM']
    have h0 : θh x = 0 := by
      by_contra hne
      exact hxM' ⟨hx, hne⟩
    change (0 : ℝ) = θh x * _
    rw [h0, zero_mul]
/-- `L¹` comparison of two weighted integrals against a bounded continuous test weight `φ`
vanishing off `B̄_s(x)`, `s ≤ ρ`: with `h = 1_{M₂} θ₂ - c 1_{M₁} θ₁`,
`‖∫_{M₂} φ θ₂ - c ∫_{M₁} φ θ₁‖ₑ ≤ K · ∫⁻_{B̄_s(x)} ‖h‖ₑ`.
Both integrals are integrals of `φ · 1_{M_i} θ_i = φ · 1_{M_i ∩ B̄_ρ(x)} θ_i`, which are
integrable, so the difference is `∫ φ h`, and `‖φ h‖ₑ ≤ 1_{B̄_s(x)} K ‖h‖ₑ` pointwise. -/
theorem Submission.fiw_tl_tr_weighted_diff_bound :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ φ : Eucl P → ℝ) (x : Eucl P) (c ρ s K : ℝ),
      NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) →
      IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
      IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
      Continuous φ → (∀ z, ‖φ z‖ ≤ K) → (∀ z, z ∉ closedBall x s → φ z = 0) → s ≤ ρ →
      ‖(∫ z in M₂, φ z * θ₂ z ∂(μHE[n] : Measure (Eucl P))) -
          c * ∫ z in M₁, φ z * θ₁ z ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal K * ∫⁻ z in closedBall x s,
          ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n M₁ M₂ θ₁ θ₂ φ x c ρ s K hM₁ hM₂ hθ₁ hθ₂ hφ hφK hφs hsρ
  set μ : Measure (Eucl P) := μHE[n]
  -- `φ` vanishes off `B̄_ρ(x) ⊇ B̄_s(x)`.
  have hφρ : ∀ z, z ∉ closedBall x ρ → φ z = 0 := fun z hz =>
    hφs z fun hzs => hz (closedBall_subset_closedBall hsρ hzs)
  -- `∫_M φ θ = ∫ φ · 1_M θ`, and `φ · 1_M θ = φ · 1_{M ∩ B̄_ρ(x)} θ` is integrable.
  have key : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ), NullMeasurableSet M μ →
      IntegrableOn θ (M ∩ closedBall x ρ) μ →
      (∫ z in M, φ z * θ z ∂μ) = ∫ z, φ z * M.indicator θ z ∂μ ∧
        Integrable (fun z => φ z * M.indicator θ z) μ := by
    intro M θ hM hθ
    refine ⟨?_, ?_⟩
    · rw [← integral_indicator₀ hM]
      congr 1
      funext z
      exact indicator_mul_right M φ θ
    · have hint : Integrable ((M ∩ closedBall x ρ).indicator θ) μ :=
        hθ.integrable_indicator₀ (hM.inter measurableSet_closedBall.nullMeasurableSet)
      refine (hint.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hφK)).congr
        (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ closedBall x ρ
      · by_cases hzM : z ∈ M
        · simp [indicator_of_mem hzM, indicator_of_mem (mem_inter hzM hz)]
        · simp [indicator_of_notMem hzM, indicator_of_notMem fun h : z ∈ M ∩ _ => hzM h.1]
      · simp [hφρ z hz]
  obtain ⟨h₁eq, h₁int⟩ := key M₁ θ₁ hM₁ hθ₁
  obtain ⟨h₂eq, h₂int⟩ := key M₂ θ₂ hM₂ hθ₂
  -- Linearity: the difference is `∫ φ · (1_{M₂} θ₂ - c 1_{M₁} θ₁)`.
  have hlin : (∫ z in M₂, φ z * θ₂ z ∂μ) - c * ∫ z in M₁, φ z * θ₁ z ∂μ =
      ∫ z, φ z * (M₂.indicator θ₂ z - c * M₁.indicator θ₁ z) ∂μ := by
    rw [h₁eq, h₂eq, ← integral_const_mul, ← integral_sub h₂int (h₁int.const_mul c)]
    congr 1
    funext z
    ring
  rw [hlin]
  calc ‖∫ z, φ z * (M₂.indicator θ₂ z - c * M₁.indicator θ₁ z) ∂μ‖ₑ
      ≤ ∫⁻ z, ‖φ z * (M₂.indicator θ₂ z - c * M₁.indicator θ₁ z)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z, (closedBall x s).indicator
          (fun z => ENNReal.ofReal K * ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ) z ∂μ := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall x s
        · rw [indicator_of_mem hz, enorm_mul]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hφK z)
        · simp [hφs z hz]
    _ = ∫⁻ z in closedBall x s,
          ENNReal.ofReal K * ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂μ :=
        lintegral_indicator measurableSet_closedBall _
    _ = ENNReal.ofReal K *
          ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
/-- Little-o scaling limit (step 7 of the proof of `fiw_tl_transfer`): if `R > 0`, `E = o(G)`
and `G(s) ≤ C sⁿ` as `s → 0⁺`, and `‖D(r)‖ₑ ≤ (rⁿ)⁻¹ · K · E(R r)` for small `r > 0`, then
`D(r) → 0` as `r → 0⁺`.  With `K₁ = max(K, 0)`, `C₁ = max(C, 0)`, `A = K₁ C₁ Rⁿ` and
`ε' = ε / (2(A + 1))`, for small `r > 0`:
`|D(r)| ≤ (rⁿ)⁻¹ · K₁ · ε' · C₁ (R r)ⁿ = A ε' < ε`. -/
theorem Submission.fiw_tl_tr_scaling_limit :
    ∀ (n : ℕ) (D : ℝ → ℝ) (E G : ℝ → ℝ≥0∞) (R K C : ℝ), 0 < R →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), E s ≤ ENNReal.ofReal ε * G s) →
      (∀ᶠ s in 𝓝[>] (0 : ℝ), G s ≤ ENNReal.ofReal (C * s ^ n)) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ),
        ‖D r‖ₑ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K * E (R * r)) →
      Tendsto D (𝓝[>] 0) (𝓝 0) := by
  intro n D E G R K C hR hE hG hD
  -- `r ↦ R r` maps `𝓝[>] 0` to `𝓝[>] 0`, so (a) and (b) hold at `s = R r` for small `r > 0`.
  have hscale : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hR hr
  -- Nonnegative constants `K₁ ≥ K`, `C₁ ≥ C`, and `ε'` with `A ε' < ε` for `A = K₁ C₁ Rⁿ`.
  obtain ⟨K₁, hKK₁, hK₁⟩ : ∃ K₁ : ℝ, K ≤ K₁ ∧ 0 ≤ K₁ :=
    ⟨max K 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨C₁, hCC₁, hC₁⟩ : ∃ C₁ : ℝ, C ≤ C₁ ∧ 0 ≤ C₁ :=
    ⟨max C 0, le_max_left _ _, le_max_right _ _⟩
  have hA : 0 ≤ K₁ * C₁ * R ^ n := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ K₁ * C₁ * R ^ n * ε' < ε := by
    refine ⟨ε / (2 * (K₁ * C₁ * R ^ n + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  filter_upwards [self_mem_nhdsWithin, hD, hscale.eventually (hE ε' hε'0), hscale.eventually hG]
    with r (hr : 0 < r) hDr hEr hGr
  have hrn : r ^ n ≠ 0 := (pow_pos hr n).ne'
  -- `‖D(r)‖ₑ ≤ ((rⁿ)⁻¹)⁺ K₁⁺ (ε'⁺ (C₁ (R r)ⁿ)⁺) = (A ε')⁺`, using `(R r)ⁿ = Rⁿ rⁿ`.
  have h1 : ‖D r‖ₑ ≤ ENNReal.ofReal (K₁ * C₁ * R ^ n * ε') := by
    calc ‖D r‖ₑ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K * E (R * r) := hDr
      _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K₁ *
          (ENNReal.ofReal ε' * ENNReal.ofReal (C₁ * (R * r) ^ n)) := by
        gcongr
        calc E (R * r) ≤ ENNReal.ofReal ε' * G (R * r) := hEr
          _ ≤ ENNReal.ofReal ε' * ENNReal.ofReal (C₁ * (R * r) ^ n) := by
            gcongr
            exact hGr.trans (ENNReal.ofReal_le_ofReal (by gcongr))
      _ = ENNReal.ofReal ((r ^ n)⁻¹ * K₁ * (ε' * (C₁ * (R * r) ^ n))) := by
        rw [ENNReal.ofReal_mul (p := (r ^ n)⁻¹ * K₁) (by positivity),
          ENNReal.ofReal_mul (p := (r ^ n)⁻¹) (by positivity),
          ENNReal.ofReal_mul (p := ε') hε'0.le]
      _ = ENNReal.ofReal (K₁ * C₁ * R ^ n * ε') := by
        congr 1
        calc (r ^ n)⁻¹ * K₁ * (ε' * (C₁ * (R * r) ^ n))
            = K₁ * C₁ * R ^ n * ε' * ((r ^ n)⁻¹ * r ^ n) := by ring
          _ = K₁ * C₁ * R ^ n * ε' := by rw [inv_mul_cancel₀ hrn, mul_one]
  -- Back to `ℝ`: `|D(r)| ≤ A ε' < ε`.
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  rw [dist_zero_right]
  exact h1.trans_lt hε'
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

/-- Simon Ch. 3, 1.7: if `M` has weighted approximate tangent space `Q` at `x` and `θ ≥ 0` is
`Hⁿ`-integrable on `M ∩ B̄_ρ(x)`, then `∫_{M ∩ B̄_s(x)} θ dHⁿ ≤ C sⁿ` for all small `s > 0`.
Test with the cut-off `f₀ = max 0 (min 1 (2 - ‖·‖))` (`= 1` on `B̄₁(0)`, `= 0` off `B₂(0)`): by
`fiw_tl_blowup_setIntegral` the tangent integrals equal `s⁻ⁿ ∫_M f₀(η_s z) θ(z) dHⁿ(z)`, which
dominate `s⁻ⁿ ∫_{M ∩ B̄_s(x)} θ dHⁿ` and converge as `s ↓ 0`. -/
theorem Submission.fiw_tl_growth_bound :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (ρ : ℝ)
      (Q : Submodule ℝ (Eucl P)), 0 < ρ → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) →
      (∀ y ∈ M, 0 ≤ θ y) → IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
      HasWeightedApproximateTangentSpaceAt n M θ x Q → ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂(μHE[n] : Measure (Eucl P)) ≤
          ENNReal.ofReal (C * s ^ n) := by
  intro P n M θ x ρ Q hρ hM hθ hθi hT
  -- Step 1: the cut-off `f₀ ∈ C_c(ℝ^P)`: `f₀ = 1` on `B̄₁(0)`, `f₀ = 0` off `B₂(0)`, `0 ≤ f₀ ≤ 1`.
  obtain ⟨f₀, hf₀0, hf₀1, hf₀nn, hf₀le⟩ : ∃ f₀ : CompactlySupportedContinuousMap (Eucl P) ℝ,
      (∀ y, 2 ≤ ‖y‖ → f₀ y = 0) ∧ (∀ y, ‖y‖ ≤ 1 → f₀ y = 1) ∧ (∀ y, 0 ≤ f₀ y) ∧
        ∀ y, f₀ y ≤ 1 := by
    have h0 : ∀ y : Eucl P, 2 ≤ ‖y‖ → max 0 (min 1 (2 - ‖y‖)) = 0 := fun y hy =>
      max_eq_left (min_le_of_right_le (by linarith))
    refine ⟨⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)),
        continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) fun y hy =>
        h0 y (not_le.1 fun h => hy (mem_closedBall_zero_iff.2 h)).le⟩, h0, fun y hy => ?_,
      fun y => le_max_left _ _, fun y => max_le zero_le_one (min_le_left _ _)⟩
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 2: `I(s) → L := θ(x) ∫_Q f₀ dHⁿ` as `s ↓ 0`, so `I(s) < C := |L| + 1` for small `s`.
  refine ⟨|θ x * ∫ y in (Q : Set (Eucl P)), f₀ y ∂(μHE[n] : Measure (Eucl P))| + 1, ?_⟩
  filter_upwards [(hT.2 f₀).eventually (gt_mem_nhds ((le_abs_self _).trans_lt (lt_add_one _))),
    Ioo_mem_nhdsGT (half_pos hρ)] with s hIs hs
  obtain ⟨hs0, hsρ⟩ := hs
  -- Step 3: `I(s) = s⁻ⁿ ∫_M F dHⁿ`, `F z = f₀(η_s z) θ(z)`, since `x + s η_s(z) = z`.
  have hη : ∀ z, Poincare.SimonGMT.Chapter03.blowUpMap x s z = s⁻¹ • (z - x) := fun z => rfl
  have hxη : ∀ z, x + s • Poincare.SimonGMT.Chapter03.blowUpMap x s z = z := fun z => by
    rw [hη, smul_inv_smul₀ hs0.ne', add_sub_cancel]
  have hcv := Submission.fiw_tl_blowup_setIntegral P n x s M (fun y => f₀ y * θ (x + s • y)) hs0
  simp only [hxη] at hcv
  -- Step 4: `F = 0` off `B̄_ρ(x)` (as `2s < ρ`) and `F = θ` on `B̄_s(x)`.
  have hnη : ∀ z, ‖Poincare.SimonGMT.Chapter03.blowUpMap x s z‖ = dist z x / s := fun z => by
    rw [hη, norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, dist_eq_norm, inv_mul_eq_div]
  have hF0 : ∀ z, z ∉ closedBall x ρ →
      f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z = 0 := fun z hz => by
    rw [mem_closedBall, not_le] at hz
    rw [hf₀0 _ (by rw [hnη, le_div_iff₀ hs0]; linarith), zero_mul]
  have hF1 : ∀ z ∈ closedBall x s,
      f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z = θ z := fun z hz => by
    rw [hf₀1 _ (by rw [hnη, div_le_one hs0]; exact hz), one_mul]
  -- Step 5: `F` is integrable on `M`: bounded continuous times `θ` on `M ∩ B̄_ρ(x)`, zero off it.
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x s) := by
    show Continuous fun z => s⁻¹ • (z - x)
    fun_prop
  have hFρ : IntegrableOn (fun z => f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z)
      (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) :=
    Integrable.bdd_mul (c := 1) hθi (f₀.continuous.comp hηc).aestronglyMeasurable
      (Eventually.of_forall fun z => (Real.norm_of_nonneg (hf₀nn _)).trans_le (hf₀le _))
  have hFi : IntegrableOn (fun z => f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z) M
      (μHE[n] : Measure (Eucl P)) :=
    hFρ.of_ae_sdiff_eq_zero hM (Eventually.of_forall fun z hz => hF0 z fun h => hz.2 ⟨hz.1, h⟩)
  -- Steps 6–7: `∫_{M ∩ B̄_s(x)} θ = ∫_{M ∩ B̄_s(x)} F ≤ ∫_M F = sⁿ I(s) ≤ C sⁿ`.
  have hMs : NullMeasurableSet (M ∩ closedBall x s) (μHE[n] : Measure (Eucl P)) :=
    hM.inter measurableSet_closedBall.nullMeasurableSet
  have hθs : IntegrableOn θ (M ∩ closedBall x s) (μHE[n] : Measure (Eucl P)) :=
    hθi.mono_set (inter_subset_inter_right _ (closedBall_subset_closedBall (by linarith)))
  rw [← ofReal_integral_eq_lintegral_ofReal hθs
    (by filter_upwards [ae_restrict_mem₀ hMs] with z hz using hθ z hz.1)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ z in M ∩ closedBall x s, θ z ∂(μHE[n] : Measure (Eucl P))
      = ∫ z in M ∩ closedBall x s, f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z
          ∂(μHE[n] : Measure (Eucl P)) :=
        setIntegral_congr_fun₀ hMs fun z hz => (hF1 z hz.2).symm
    _ ≤ ∫ z in M, f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z
          ∂(μHE[n] : Measure (Eucl P)) :=
        setIntegral_mono_set hFi (by
          filter_upwards [ae_restrict_mem₀ hM] with z hz using mul_nonneg (hf₀nn _) (hθ z hz))
          inter_subset_left.eventuallyLE
    _ = s ^ n * ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x s '' M, f₀ y * θ (x + s • y)
          ∂(μHE[n] : Measure (Eucl P)) := by
        rw [hcv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs0.ne'), one_mul]
    _ ≤ s ^ n * (|θ x * ∫ y in (Q : Set (Eucl P)), f₀ y ∂(μHE[n] : Measure (Eucl P))| + 1) :=
        mul_le_mul_of_nonneg_left hIs.le (pow_nonneg hs0.le _)
    _ = _ := mul_comm _ _

/-- Simon Ch. 3, Remarks 1.5(2), 1.8(1): pointwise transfer of a weighted approximate tangent
space.  If `θ₂(x) = c θ₁(x)` and `h = 1_{M₂}θ₂ − c 1_{M₁}θ₁` is `o(∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ)` in
`L¹(B̄_s(x))` as `s ↓ 0`, then every tangent space `Q` of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.
For `f ∈ C_c(ℝ^P)` (`f = 0` off `B_R(0)`, `|f| ≤ K`) the tangent integrals are
`I_i(r) = r⁻ⁿ ∫_{M_i} f(η_r z) θ_i(z) dHⁿ(z)` by `fiw_tl_blowup_setIntegral`, so
`|I₂(r) − c I₁(r)| ≤ r⁻ⁿ K ∫_{B̄_{Rr}(x)} |h| dHⁿ` (`fiw_tl_tr_weighted_diff_bound`), which tends
to `0` by `fiw_tl_growth_bound` and `fiw_tl_tr_scaling_limit`.  Hence
`I₂(r) → c θ₁(x) ∫_Q f dHⁿ = θ₂(x) ∫_Q f dHⁿ`. -/
theorem Submission.fiw_tl_transfer :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (x : Eucl P) (c ρ : ℝ), 0 < ρ → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M₁, 0 ≤ θ₁ y) → IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → θ₂ x = c * θ₁ x → (∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal ε * ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q := by
  intro P n M₁ M₂ θ₁ θ₂ x c ρ hρ hM₁ hM₂ hθ₁ hθ₁i hθ₂i hx hsmall Q hT
  -- Step 2: `∫⁻_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ ≤ C₀ sⁿ` for all small `s > 0`.
  obtain ⟨C₀, hC₀⟩ := Submission.fiw_tl_growth_bound P n M₁ θ₁ x ρ Q hρ hM₁ hθ₁ hθ₁i hT
  -- Step 1: `finrank Q = n` is inherited; fix `f ∈ C_c(ℝ^P)`.
  refine ⟨hT.1, fun f => ?_⟩
  -- Step 3: `f = 0` off `B_R(0)` and `‖f‖ ≤ K`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨K, hK⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  -- Steps 4–7: `D(r) := I₂(r) − c I₁(r) → 0` as `r ↓ 0`.
  have hD : Tendsto (fun r : ℝ =>
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M₂, f y * θ₂ (x + r • y)
        ∂(μHE[n] : Measure (Eucl P))) -
      c * ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M₁, f y * θ₁ (x + r • y)
        ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
    refine Submission.fiw_tl_tr_scaling_limit n _
      (fun s => ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ
        ∂(μHE[n] : Measure (Eucl P)))
      (fun s => ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P)))
      R K C₀ hR hsmall hC₀ ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    obtain ⟨hr0, hrρ⟩ := hr
    have hRr : R * r ≤ ρ := by
      rw [lt_div_iff₀ hR, mul_comm] at hrρ
      exact hrρ.le
    -- `η_r(z) = r⁻¹(z − x)`: `x + r η_r(z) = z` and `‖η_r(z)‖ = |z − x| / r`.
    have hη : ∀ z, Poincare.SimonGMT.Chapter03.blowUpMap x r z = r⁻¹ • (z - x) := fun z => rfl
    have hxη : ∀ z, x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r z = z := fun z => by
      rw [hη, smul_inv_smul₀ hr0.ne', add_sub_cancel]
    have hnη : ∀ z, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = dist z x / r := fun z => by
      rw [hη, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le, dist_eq_norm, inv_mul_eq_div]
    have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
      show Continuous fun z => r⁻¹ • (z - x)
      fun_prop
    -- Step 4: `I_i(r) = r⁻ⁿ ∫_{M_i} f(η_r z) θ_i(z) dHⁿ(z)`.
    have hcv₁ := Submission.fiw_tl_blowup_setIntegral P n x r M₁
      (fun y => f y * θ₁ (x + r • y)) hr0
    have hcv₂ := Submission.fiw_tl_blowup_setIntegral P n x r M₂
      (fun y => f y * θ₂ (x + r • y)) hr0
    simp only [hxη] at hcv₁ hcv₂
    -- Steps 5–6: the weight `f ∘ η_r` is continuous, bounded by `K` and `0` off `B̄_{Rr}(x)`.
    have hA := Submission.fiw_tl_tr_weighted_diff_bound P n M₁ M₂ θ₁ θ₂
      (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) x c ρ (R * r) K hM₁ hM₂ hθ₁i
      hθ₂i (f.continuous.comp hηc) (fun z => hK _) (fun z hz => hfR _ (by
        rw [mem_closedBall, not_le] at hz
        rw [hnη, le_div_iff₀ hr0]
        exact hz.le)) hRr
    rw [hcv₁, hcv₂, mul_left_comm c, ← mul_sub, enorm_mul,
      Real.enorm_eq_ofReal (inv_nonneg.2 (pow_nonneg hr0.le n)), mul_assoc]
    exact mul_le_mul_of_nonneg_left hA zero_le
  -- Step 8: `c I₁(r) → c θ₁(x) ∫_Q f dHⁿ = θ₂(x) ∫_Q f dHⁿ`, so `I₂(r) = D(r) + c I₁(r)` converges.
  have h := hD.add ((hT.2 f).const_mul c)
  rw [zero_add, ← mul_assoc, ← hx] at h
  exact h.congr fun r => sub_add_cancel _ _
/-- Reduction of an almost-everywhere property to balls: if `Φ` holds `μ ⌞ (A ∩ B_r(y))`-a.e.
for every ball with `B̄_r(y) ⊆ U`, then `Φ` holds `μ ⌞ A`-a.e. for `A ⊆ U`, `U` open.  Countably
many such balls cover `A` (`ℝ^P` is second countable), and `μ ⌞ A`-a.e. is checked on the
pieces of a countable cover without any measurability assumption. -/
theorem Submission.fiw_tl_ald_ball_reduction :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (U A : Set (Eucl P)) (Φ : Eucl P → Prop), IsOpen U →
      A ⊆ U → (∀ (y : Eucl P) (r : ℝ), closedBall y r ⊆ U →
        ∀ᵐ x ∂(μ.restrict (A ∩ ball y r)), Φ x) → ∀ᵐ x ∂(μ.restrict A), Φ x := by
  intro P μ U A Φ hU hAU hball
  -- The balls `B_r(y)` with `B̄_r(y) ⊆ U`, indexed by `ι`; a countable subfamily `T` has the
  -- same union.
  let ι := {p : Eucl P × ℝ // closedBall p.1 p.2 ⊆ U}
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : ι => ball i.1.1 i.1.2) fun i => isOpen_ball
  -- `A = ⋃_{i ∈ T} (A ∩ B_i)`: each `x ∈ A ⊆ U` lies in `B_{δ/2}(x)`, and
  -- `B̄_{δ/2}(x) ⊆ B_δ(x) ⊆ U`.
  have hA : A = ⋃ i ∈ T, A ∩ ball i.1.1 i.1.2 := by
    rw [← inter_iUnion₂, hT, eq_comm, inter_eq_left]
    intro x hx
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x (hAU hx)
    exact mem_iUnion.2 ⟨⟨(x, δ / 2), (closedBall_subset_ball (half_lt_self hδ)).trans hδU⟩,
      mem_ball_self (half_pos hδ)⟩
  rw [hA, ae_restrict_biUnion_iff _ hTc]
  exact fun i _ => hball i.1.1 i.1.2 i.2
/-- Weighted Lebesgue points (for the locality of weighted approximate tangent spaces, Simon
Ch. 3, 1.5(2), 1.8(1)).  Let `M ⊆ ℝ^P` be `μ`-null-measurable, `θ > 0` on `M`, and `θ`, `θ f`
`μ`-integrable on `M ∩ B̄_r(y)`.  Then for `μ`-a.e. `x ∈ M ∩ B_r(y)`,
`∫_{M ∩ B̄_s(x)} θ |f - f(x)| dμ / ∫_{M ∩ B̄_s(x)} θ dμ → 0` as `s ↓ 0`.  The measure
`ν = θ⁺ μ ⌞ (M ∩ B̄_r(y))` is finite, `μ ⌞ (M ∩ B̄_r(y)) ≪ ν` as `θ > 0` on `M`, and `f ∈ L¹(ν)`
as `θ f ∈ L¹(μ ⌞ (M ∩ B̄_r(y)))`.  So the Lebesgue differentiation theorem for `ν` along closed
balls (Simon Ch. 1, 3.17; `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` for
`Besicovitch.vitaliFamily ν`) holds `μ ⌞ (M ∩ B_r(y))`-a.e.; for `0 < s < r - |x - y|`,
`B̄_s(x) ⊆ B̄_r(y)`, so the two `ν`-integrals over `B̄_s(x)` are the two integrals above. -/
theorem Submission.fiw_tl_ald_ld_weighted_lebesgue_point :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (M : Set (Eucl P)) (θ f : Eucl P → ℝ) (y : Eucl P) (r : ℝ),
      NullMeasurableSet M μ → (∀ z ∈ M, 0 < θ z) → IntegrableOn θ (M ∩ closedBall y r) μ →
      IntegrableOn (fun z => θ z * f z) (M ∩ closedBall y r) μ →
      ∀ᵐ x ∂(μ.restrict (M ∩ ball y r)),
        Tendsto (fun s : ℝ =>
          (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) * ‖f z - f x‖ₑ ∂μ) /
            (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ)) (𝓝[>] 0) (𝓝 0) := by
  intro P μ M θ f y r hM hpos hθ hθf
  -- Step 1: `S = M ∩ B̄_r(y)` and `M ∩ B_r(y)` are `μ`-null-measurable.
  have hS : NullMeasurableSet (M ∩ closedBall y r) μ :=
    hM.inter measurableSet_closedBall.nullMeasurableSet
  have hMB : NullMeasurableSet (M ∩ ball y r) μ :=
    hM.inter measurableSet_ball.nullMeasurableSet
  set μS := μ.restrict (M ∩ closedBall y r) with hμS
  set ν := μS.withDensity (fun z => ENNReal.ofReal (θ z)) with hν
  -- Step 2: `ν = (μ ⌞ S).withDensity θ⁺` is finite, since `θ` is integrable on `S`.
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hθ.2
  -- Step 3: `μ ⌞ S ≪ ν`, since `θ > 0` on `M`.
  have hθm : AEMeasurable (fun z => ENNReal.ofReal (θ z)) μS :=
    hθ.1.aemeasurable.ennreal_ofReal
  have hmemS : ∀ᵐ z ∂μS, z ∈ M ∩ closedBall y r := ae_restrict_mem₀ hS
  have hac : μS ≪ ν := by
    refine withDensity_absolutelyContinuous' hθm ?_
    filter_upwards [hmemS] with z hz
    exact (ENNReal.ofReal_pos.2 (hpos z hz.1)).ne'
  -- Step 4: `f ∈ L¹(ν)`, since `θ.toNNReal • f = θ f` on `S`; hence `f` is `μ ⌞ S`-measurable.
  have hfν : Integrable f ν := by
    have hnn : AEMeasurable (fun z => (θ z).toNNReal) μS :=
      hθ.1.aemeasurable.real_toNNReal
    have hνeq : ν = μS.withDensity (fun z => ((θ z).toNNReal : ℝ≥0∞)) := rfl
    rw [hνeq, integrable_withDensity_iff_integrable_smul₀ hnn]
    refine hθf.congr ?_
    filter_upwards [hmemS] with z hz
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hpos z hz.1).le, smul_eq_mul]
  have hfS : AEStronglyMeasurable f μS := hfν.1.mono_ac hac
  -- Step 5: Lebesgue differentiation for `ν` along closed balls.
  have hLeb : ∀ᵐ x ∂ν, Tendsto (fun s : ℝ =>
      (∫⁻ z in closedBall x s, ‖f z - f x‖ₑ ∂ν) / ν (closedBall x s)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_lintegral_enorm_sub_div
      hfν.locallyIntegrable] with x hx
    exact hx.comp (Besicovitch.tendsto_filterAt ν x)
  -- Step 6: transfer to `μ ⌞ (M ∩ B_r(y)) ≤ μ ⌞ S ≪ ν`.
  have hlam : μ.restrict (M ∩ ball y r) ≪ ν :=
    (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (inter_subset_inter_right M ball_subset_closedBall) le_rfl)).trans hac
  filter_upwards [hlam.ae_le hLeb, ae_restrict_mem₀ hMB] with x hx hxmem
  -- Step 7: for `0 < s < r - dist x y`, `B̄_s(x) ⊆ B̄_r(y)` and the two quotients agree.
  refine hx.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (mem_ball.1 hxmem.2))] with s hs
  have hsub : closedBall x s ⊆ closedBall y r :=
    closedBall_subset_closedBall' (by linarith [hs.2])
  have hinter : closedBall x s ∩ (M ∩ closedBall y r) = M ∩ closedBall x s := by
    ext z
    exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hsub hz.2⟩⟩
  have hgm : AEMeasurable (fun z => ‖f z - f x‖ₑ) μS :=
    (hfS.sub aestronglyMeasurable_const).enorm
  have hnum : ∫⁻ z in closedBall x s, ‖f z - f x‖ₑ ∂ν =
      ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) * ‖f z - f x‖ₑ ∂μ := by
    rw [hν, setLIntegral_withDensity_eq_lintegral_mul₀ hθm hgm measurableSet_closedBall,
      hμS, Measure.restrict_restrict measurableSet_closedBall, hinter]
    rfl
  have hden : ν (closedBall x s) = ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ := by
    rw [hν, withDensity_apply _ measurableSet_closedBall, hμS,
      Measure.restrict_restrict measurableSet_closedBall, hinter]
  rw [hnum, hden]
/-- Weighted density points (for the locality of weighted approximate tangent spaces, Simon
Ch. 3, 1.5(2), 1.8(1)).  Let `M, E ⊆ ℝ^P` be `μ`-null-measurable with `E ⊆ M`, `θ > 0` on `M` and
`θ` `μ`-integrable on `M ∩ B̄_r(y)`.  Then for `μ`-a.e. `x ∈ E ∩ B_r(y)`,
`∫_{E ∩ B̄_s(x)} θ dμ / ∫_{M ∩ B̄_s(x)} θ dμ → 1` as `s ↓ 0`.  The measure
`ν = θ⁺ μ ⌞ (M ∩ B̄_r(y))` is finite and `μ ⌞ (M ∩ B̄_r(y)) ≪ ν` as `θ > 0` on `M`, so
`μ ⌞ (E ∩ B_r(y)) ≪ ν ⌞ E` and the Besicovitch density theorem for `ν` and `E`
(`Besicovitch.ae_tendsto_measure_inter_div`) applies; for `0 < s < r - |x - y|`,
`B̄_s(x) ⊆ B̄_r(y)`, so `ν(E ∩ B̄_s(x))` and `ν(B̄_s(x))` are the two integrals. -/
theorem Submission.fiw_tl_ald_ld_weighted_density_point :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (M E : Set (Eucl P)) (θ : Eucl P → ℝ) (y : Eucl P) (r : ℝ),
      NullMeasurableSet M μ → NullMeasurableSet E μ → E ⊆ M → (∀ z ∈ M, 0 < θ z) →
      IntegrableOn θ (M ∩ closedBall y r) μ →
      ∀ᵐ x ∂(μ.restrict (E ∩ ball y r)),
        Tendsto (fun s : ℝ => (∫⁻ z in E ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ) /
          (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ)) (𝓝[>] 0) (𝓝 1) := by
  intro P μ M E θ y r hM hE hEM hθ hint
  -- Step 1: null-measurability of `S = M ∩ B̄_r(y)` and of `E` for `μ ⌞ S`.
  have hS : NullMeasurableSet (M ∩ closedBall y r) μ :=
    hM.inter measurableSet_closedBall.nullMeasurableSet
  have hES : NullMeasurableSet E (μ.restrict (M ∩ closedBall y r)) :=
    hE.mono Measure.restrict_le_self
  -- Step 2: `ν = (μ ⌞ S).withDensity θ⁺` is finite, since `θ` is integrable on `S`.
  have : IsFiniteMeasure ((μ.restrict (M ∩ closedBall y r)).withDensity
      fun z => ENNReal.ofReal (θ z)) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  -- Step 3: `μ ⌞ S ≪ ν`, since `θ > 0` on `M`.
  have hac : μ.restrict (M ∩ closedBall y r) ≪ (μ.restrict (M ∩ closedBall y r)).withDensity
      fun z => ENNReal.ofReal (θ z) := by
    refine withDensity_absolutelyContinuous' hint.1.aemeasurable.ennreal_ofReal ?_
    filter_upwards [ae_restrict_mem₀ hS] with z hz
    exact (ENNReal.ofReal_pos.2 (hθ z hz.1)).ne'
  -- Step 4: `μ ⌞ (E ∩ B_r(y)) ≤ (μ ⌞ S) ⌞ E ≪ ν ⌞ E`.
  have hle : μ.restrict (E ∩ ball y r) ≤ (μ.restrict (M ∩ closedBall y r)).restrict E := by
    rw [Measure.restrict_restrict₀ hES]
    refine Measure.restrict_mono ?_ le_rfl
    intro z hz
    exact ⟨hz.1, hEM hz.1, ball_subset_closedBall hz.2⟩
  have hlam : μ.restrict (E ∩ ball y r) ≪ ((μ.restrict (M ∩ closedBall y r)).withDensity
      fun z => ENNReal.ofReal (θ z)).restrict E :=
    (Measure.absolutelyContinuous_of_le hle).trans (hac.restrict E)
  -- Step 5: the Besicovitch density theorem for `ν` and `E`, transferred to `μ ⌞ (E ∩ B_r(y))`.
  filter_upwards [hlam.ae_le (Besicovitch.ae_tendsto_measure_inter_div _ E),
    ae_restrict_mem₀ (hE.inter measurableSet_ball.nullMeasurableSet)] with x hx hxE
  -- Step 6: for `0 < s < r - dist x y`, `B̄_s(x) ⊆ B̄_r(y)` and the two quotients agree.
  refine hx.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (mem_ball.1 hxE.2))] with s hs
  have hsub : closedBall x s ⊆ closedBall y r :=
    closedBall_subset_closedBall' (by linarith [hs.2])
  have hEs : NullMeasurableSet (E ∩ closedBall x s) (μ.restrict (M ∩ closedBall y r)) :=
    hES.inter measurableSet_closedBall.nullMeasurableSet
  have hE' : E ∩ closedBall x s ∩ (M ∩ closedBall y r) = E ∩ closedBall x s :=
    inter_eq_left.2 fun z hz => ⟨hEM hz.1, hsub hz.2⟩
  have hM' : closedBall x s ∩ (M ∩ closedBall y r) = M ∩ closedBall x s := by
    ext z
    exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hsub hz.2⟩⟩
  rw [withDensity_apply₀ _ hEs, Measure.restrict_restrict₀ hEs, hE',
    withDensity_apply _ measurableSet_closedBall,
    Measure.restrict_restrict measurableSet_closedBall, hM']
/-- Lebesgue differentiation along closed balls: for a finite measure `ν` on `ℝ^P` and
`g ∈ L¹(ν)`, `ν`-a.e. `x` satisfies `⨍_{B̄_s(x)} |g - g(x)| dν → 0` as `s → 0⁺`.  The closed balls
`B̄_s(x)` form the Besicovitch Vitali family of `ν` (`ℝ^P` has the Besicovitch covering property),
along which every locally integrable function has Lebesgue points `ν`-a.e. -/
theorem Submission.fiw_tl_ald_closedBall_lebesgue_point :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) [IsFiniteMeasure ν] (g : Eucl P → ℝ), Integrable g ν →
      ∀ᵐ x ∂ν, Tendsto (fun s : ℝ => (∫⁻ z in closedBall x s, ‖g z - g x‖ₑ ∂ν) /
        ν (closedBall x s)) (𝓝[>] 0) (𝓝 0) := by
  intro P ν _ g hg
  filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_lintegral_enorm_sub_div
    hg.locallyIntegrable] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt ν x)

/-- Local differentiation on a ball: let `θᵢ > 0` on `Mᵢ` be `Hⁿ`-integrable on `Mᵢ ∩ B̄_r(y)` and
`g = 1_{M₁ ∩ M₂} θ₂/θ₁`.  For `Hⁿ ⌞ (M₁ ∩ M₂ ∩ B_r(y))`-a.e. `x`, as `s → 0⁺`, `x` is a Lebesgue
point of `g` for `θ₁ Hⁿ ⌞ M₁` and `M₁ ∩ M₂` has density `1` at `x` for `θ₂ Hⁿ ⌞ M₂`, both along
the closed balls `B̄_s(x)`.  Since `θ₁ g = 1_{M₁ ∩ M₂} θ₂` is integrable on `M₁ ∩ B̄_r(y)`, these
are the weighted Lebesgue-point lemma for `(M₁, θ₁, g)`, with `g(x) = θ₂(x)/θ₁(x)` on `M₁ ∩ M₂`,
and the weighted density lemma for `M₁ ∩ M₂ ⊆ M₂`. -/
theorem Submission.fiw_tl_ald_local_differentiation :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (y : Eucl P) (r : ℝ),
      NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ z ∈ M₁, 0 < θ₁ z) →
      (∀ z ∈ M₂, 0 < θ₂ z) → IntegrableOn θ₁ (M₁ ∩ closedBall y r) (μHE[n] : Measure (Eucl P)) →
      IntegrableOn θ₂ (M₂ ∩ closedBall y r) (μHE[n] : Measure (Eucl P)) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂ ∩ ball y r)),
        Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) *
            ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - θ₂ x / θ₁ x‖ₑ
              ∂(μHE[n] : Measure (Eucl P))) /
          (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))))
          (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z)
            ∂(μHE[n] : Measure (Eucl P))) /
          (∫⁻ z in M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z) ∂(μHE[n] : Measure (Eucl P))))
          (𝓝[>] 0) (𝓝 1) := by
  intro P n M₁ M₂ θ₁ θ₂ y r hM₁ hM₂ hθ₁ hθ₂ hθ₁i hθ₂i
  -- `θ₁ g = 1_{M₁ ∩ M₂} θ₂` (as `θ₁ > 0` on `M₁`), which is integrable on `M₁ ∩ B̄_r(y)` because
  -- `θ₂` is integrable on `M₂ ∩ B̄_r(y)`.
  have hθ₁g : IntegrableOn (fun z => θ₁ z * (M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z)
      (M₁ ∩ closedBall y r) (μHE[n] : Measure (Eucl P)) := by
    have h : (fun z => θ₁ z * (M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z) =
        (M₁ ∩ M₂).indicator θ₂ := by
      funext z
      by_cases hz : z ∈ M₁ ∩ M₂
      · rw [indicator_of_mem hz, indicator_of_mem hz, mul_div_cancel₀ _ (hθ₁ z hz.1).ne']
      · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]
    rw [h, integrableOn_indicator_iff (hM₁.inter hM₂)]
    exact hθ₂i.mono_set fun z hz => ⟨hz.1.2, hz.2.2⟩
  -- (L) holds a.e. on `M₁ ∩ B_r(y) ⊇ M₁ ∩ M₂ ∩ B_r(y)` and (D) a.e. on `M₁ ∩ M₂ ∩ B_r(y)`.
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun z hz => ⟨hz.1.1, hz.2⟩ : M₁ ∩ M₂ ∩ ball y r ⊆ M₁ ∩ ball y r)
      (Submission.fiw_tl_ald_ld_weighted_lebesgue_point P (μHE[n] : Measure (Eucl P)) M₁ θ₁
        ((M₁ ∩ M₂).indicator fun w => θ₂ w / θ₁ w) y r hM₁ hθ₁ hθ₁i hθ₁g),
    Submission.fiw_tl_ald_ld_weighted_density_point P (μHE[n] : Measure (Eucl P)) M₂ (M₁ ∩ M₂)
      θ₂ y r hM₂ (hM₁.inter hM₂) inter_subset_right hθ₂ hθ₂i,
    ae_restrict_mem₀ ((hM₁.inter hM₂).inter measurableSet_ball.nullMeasurableSet)]
    with x hL hD hx
  -- At `x ∈ M₁ ∩ M₂`, `g(x) = θ₂(x)/θ₁(x)`.
  have hgx : (M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) x = θ₂ x / θ₁ x :=
    indicator_of_mem hx.1 _
  rw [hgx] at hL
  exact ⟨hL, hD⟩
/-- Relative `L¹` estimate at a point.  Let `θᵢ > 0` on `Mᵢ` be `Hⁿ`-integrable on
`Mᵢ ∩ B̄_ρ(x)`, `x ∈ M₁ ∩ M₂`, `c = θ₂(x)/θ₁(x)` and `g = 1_{M₁ ∩ M₂} θ₂/θ₁`.  If, as `s ↓ 0`,
(L) `∫_{M₁ ∩ B̄_s(x)} θ₁ |g − c| dHⁿ / ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ → 0` and
(D) `∫_{M₁ ∩ M₂ ∩ B̄_s(x)} θ₂ dHⁿ / ∫_{M₂ ∩ B̄_s(x)} θ₂ dHⁿ → 1`, then for every `ε > 0` and all
small `s > 0`, `∫_{B̄_s(x)} |1_{M₂} θ₂ − c 1_{M₁} θ₁| dHⁿ ≤ ε ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ`.
Pointwise `|1_{M₂} θ₂ − c 1_{M₁} θ₁| = 1_{M₁} θ₁ |g − c| + 1_{M₂ ∖ M₁} θ₂`.  With
`bᵢ = ∫_{Mᵢ ∩ B̄_s(x)} θᵢ dHⁿ`, (L) bounds the first part by `δ b₁` and (D) bounds the second by
`δ b₂ ≤ 2δ(c + δ) b₁`. -/
theorem Submission.fiw_tl_ald_pointwise_estimate :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (x : Eucl P),
      NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) →
      (∀ z ∈ M₁, 0 < θ₁ z) → (∀ z ∈ M₂, 0 < θ₂ z) → x ∈ M₁ ∩ M₂ →
      (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧
        IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) →
      Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) *
          ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - θ₂ x / θ₁ x‖ₑ
            ∂(μHE[n] : Measure (Eucl P))) /
        (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))))
        (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z)
            ∂(μHE[n] : Measure (Eucl P))) /
        (∫⁻ z in M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z) ∂(μHE[n] : Measure (Eucl P))))
        (𝓝[>] 0) (𝓝 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - θ₂ x / θ₁ x * M₁.indicator θ₁ z‖ₑ
            ∂(μHE[n] : Measure (Eucl P)) ≤
          ENNReal.ofReal ε *
            ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n M₁ M₂ θ₁ θ₂ x hM₁ hM₂ hθ₁ hθ₂ hx hint hL hD ε hε
  obtain ⟨ρ, hρ, hi₁, hi₂⟩ := hint
  generalize (μHE[n] : Measure (Eucl P)) = H at hM₁ hM₂ hi₁ hi₂ hL hD ⊢
  have hc : 0 < θ₂ x / θ₁ x := div_pos (hθ₂ x hx.2) (hθ₁ x hx.1)
  generalize θ₂ x / θ₁ x = c at hc hL ⊢
  -- `δ = min(1/2, ε/(3c+3))`: `0 < δ ≤ 1/2` and `δ(3c+3) ≤ ε`.
  obtain ⟨δ, hδ, hδ2, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ * (3 * c + 3) ≤ ε :=
    ⟨min (1 / 2) (ε / (3 * c + 3)), lt_min (by norm_num) (div_pos hε (by linarith)),
      min_le_left _ _, (le_div_iff₀ (by linarith)).1 (min_le_right _ _)⟩
  -- Eventually `s < ρ`, `a₂/b₂ > 1 − δ` (by (D)) and `I/b₁ < δ` (by (L)).
  filter_upwards [Ioo_mem_nhdsGT hρ,
    (tendsto_order.1 hD).1 (ENNReal.ofReal (1 - δ)) (ENNReal.ofReal_lt_one.2 (by linarith)),
    (tendsto_order.1 hL).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)] with s hs hs2 hs3
  have hBρ : closedBall x s ⊆ closedBall x ρ := closedBall_subset_closedBall hs.2.le
  have hi₁s : IntegrableOn θ₁ (M₁ ∩ closedBall x s) H :=
    hi₁.mono_set (inter_subset_inter_right _ hBρ)
  have hi₂s : IntegrableOn θ₂ (M₂ ∩ closedBall x s) H :=
    hi₂.mono_set (inter_subset_inter_right _ hBρ)
  have hBm : MeasurableSet (closedBall x s) := measurableSet_closedBall
  set B := closedBall x s with hB_def
  set b₁ := ∫⁻ z in M₁ ∩ B, ENNReal.ofReal (θ₁ z) ∂H with hb₁_def
  set I := ∫⁻ z in M₁ ∩ B, ENNReal.ofReal (θ₁ z) *
    ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ ∂H with hI_def
  set a₂ := ∫⁻ z in M₁ ∩ M₂ ∩ B, ENNReal.ofReal (θ₂ z) ∂H with ha₂_def
  set b₂ := ∫⁻ z in M₂ ∩ B, ENNReal.ofReal (θ₂ z) ∂H with hb₂_def
  set d₂ := ∫⁻ z in (M₂ \ M₁) ∩ B, ENNReal.ofReal (θ₂ z) ∂H with hd₂_def
  have hb₁ : b₁ ≠ ∞ := hi₁s.setLIntegral_lt_top.ne
  have hb₂ : b₂ ≠ ∞ := hi₂s.setLIntegral_lt_top.ne
  -- `b₂ = a₂ + d₂`: split `M₂ ∩ B` along `M₁`.
  have hsplit : b₂ = a₂ + d₂ := by
    have e : M₁ ∩ M₂ ∩ B = M₂ ∩ B ∩ M₁ := by
      ext z; simp only [mem_inter_iff]; tauto
    rw [hb₂_def, ha₂_def, hd₂_def, e, sdiff_inter_right_comm, ← lintegral_add_measure,
      Measure.restrict_inter_add_sdiff₀ _ hM₁]
  have ha₂ : a₂ ≠ ∞ := ne_top_of_le_ne_top hb₂ (by rw [hsplit]; exact le_self_add)
  have hd₂ : d₂ ≠ ∞ := ne_top_of_le_ne_top hb₂ (by rw [hsplit]; exact le_add_self)
  -- `(1 − δ) b₂ ≤ a₂` and `I ≤ δ b₁`.
  have h2 : ENNReal.ofReal (1 - δ) * b₂ ≤ a₂ :=
    ((ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.ofReal_ne_top) (Or.inl hb₂)).1 hs2).le
  have h3 : I ≤ ENNReal.ofReal δ * b₁ := by
    rcases eq_or_ne I 0 with h0 | h0
    · rw [h0]; exact zero_le
    · exact ((ENNReal.div_lt_iff (Or.inr h0) (Or.inl hb₁)).1 hs3).le
  have hI : I ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁) h3
  -- `a₂ ≤ c b₁ + I`, since `θ₂ ≤ c θ₁ + θ₁ |g − c|` on `M₁ ∩ M₂`.
  have h4 : a₂ ≤ ENNReal.ofReal c * b₁ + I := by
    have hA : NullMeasurableSet (M₁ ∩ M₂ ∩ B) H := (hM₁.inter hM₂).inter hBm.nullMeasurableSet
    have hm : AEMeasurable (fun z => ENNReal.ofReal c * ENNReal.ofReal (θ₁ z))
        (H.restrict (M₁ ∩ B)) :=
      hi₁s.aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul _
    calc a₂ ≤ ∫⁻ z in M₁ ∩ M₂ ∩ B, (ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) +
          ENNReal.ofReal (θ₁ z) * ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) ∂H := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hA] with z hz
          have h1z : 0 < θ₁ z := hθ₁ z hz.1.1
          have e : θ₁ z * (θ₂ z / θ₁ z) = θ₂ z := mul_div_cancel₀ _ h1z.ne'
          rw [indicator_of_mem hz.1]
          calc ENNReal.ofReal (θ₂ z)
              = ENNReal.ofReal (c * θ₁ z + θ₁ z * (θ₂ z / θ₁ z - c)) := by
                congr 1; rw [mul_sub, e]; ring
            _ ≤ ENNReal.ofReal (c * θ₁ z) + ENNReal.ofReal (θ₁ z * (θ₂ z / θ₁ z - c)) :=
                ENNReal.ofReal_add_le
            _ ≤ ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) + ‖θ₁ z * (θ₂ z / θ₁ z - c)‖ₑ := by
                rw [ENNReal.ofReal_mul hc.le]; gcongr; exact Real.ofReal_le_enorm _
            _ = ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) +
                ENNReal.ofReal (θ₁ z) * ‖θ₂ z / θ₁ z - c‖ₑ := by
                rw [enorm_mul, Real.enorm_of_nonneg h1z.le]
      _ ≤ ∫⁻ z in M₁ ∩ B, (ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) +
          ENNReal.ofReal (θ₁ z) * ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) ∂H :=
          lintegral_mono_set fun z hz => ⟨hz.1.1, hz.2⟩
      _ = ENNReal.ofReal c * b₁ + I := by
          rw [lintegral_add_left' hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Pointwise, `|1_{M₂} θ₂ − c 1_{M₁} θ₁| = 1_{M₁} θ₁ |g − c| + 1_{M₂ ∖ M₁} θ₂`.
  have hpt : ∀ z, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ≤
      M₁.indicator (fun z => ENNReal.ofReal (θ₁ z) *
        ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) z +
      (M₂ \ M₁).indicator (fun z => ENNReal.ofReal (θ₂ z)) z := by
    intro z
    by_cases h1 : z ∈ M₁ <;> by_cases h2 : z ∈ M₂
    · have h1z : 0 < θ₁ z := hθ₁ z h1
      have e : θ₁ z * (θ₂ z / θ₁ z) = θ₂ z := mul_div_cancel₀ _ h1z.ne'
      have hn : z ∉ M₂ \ M₁ := fun h => h.2 h1
      simp only [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (mem_inter h1 h2),
        indicator_of_notMem hn, add_zero]
      refine le_of_eq ?_
      rw [show θ₂ z - c * θ₁ z = θ₁ z * (θ₂ z / θ₁ z - c) by rw [mul_sub, e]; ring, enorm_mul,
        Real.enorm_of_nonneg h1z.le]
    · have h1z : 0 < θ₁ z := hθ₁ z h1
      have hn : z ∉ M₂ \ M₁ := fun h => h.2 h1
      have hn' : z ∉ M₁ ∩ M₂ := fun h => h2 h.2
      simp only [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_notMem hn',
        indicator_of_notMem hn, add_zero]
      refine le_of_eq ?_
      rw [show (0 : ℝ) - c * θ₁ z = θ₁ z * (0 - c) by ring, enorm_mul,
        Real.enorm_of_nonneg h1z.le]
    · have h2z : 0 < θ₂ z := hθ₂ z h2
      simp only [indicator_of_notMem h1, indicator_of_mem h2,
        indicator_of_mem (show z ∈ M₂ \ M₁ from ⟨h2, h1⟩), mul_zero, sub_zero, zero_add]
      exact (Real.enorm_of_nonneg h2z.le).le
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2,
        indicator_of_notMem (show z ∉ M₂ \ M₁ from fun h => h2 h.1), mul_zero, sub_zero,
        enorm_zero, add_zero, le_refl]
  -- Hence `∫_B |1_{M₂} θ₂ − c 1_{M₁} θ₁| dH ≤ I + d₂`.
  have h5 : ∫⁻ z in B, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂H ≤ I + d₂ := by
    have hGm : AEMeasurable ((M₂ \ M₁).indicator fun z => ENNReal.ofReal (θ₂ z))
        (H.restrict B) := by
      rw [aemeasurable_indicator_iff₀ ((hM₂.diff hM₁).mono Measure.restrict_le_self),
        Measure.restrict_restrict' hBm]
      exact hi₂s.aestronglyMeasurable.aemeasurable.ennreal_ofReal.mono_set
        (inter_subset_inter_left _ sdiff_subset)
    calc ∫⁻ z in B, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂H
        ≤ ∫⁻ z in B, (M₁.indicator (fun z => ENNReal.ofReal (θ₁ z) *
            ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) z +
          (M₂ \ M₁).indicator (fun z => ENNReal.ofReal (θ₂ z)) z) ∂H := lintegral_mono hpt
      _ = I + d₂ := by
        rw [lintegral_add_right' _ hGm,
          setLIntegral_indicator₀ _ (hM₁.mono Measure.restrict_le_self),
          setLIntegral_indicator₀ _ ((hM₂.diff hM₁).mono Measure.restrict_le_self)]
  -- Real arithmetic: `I + d₂ ≤ δ b₁ + δ b₂ ≤ δ (1 + 2c + 2δ) b₁ ≤ ε b₁`.
  have hfin : I + d₂ ≤ ENNReal.ofReal ε * b₁ := by
    have hcb : ENNReal.ofReal c * b₁ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁
    have r1 : b₂.toReal = a₂.toReal + d₂.toReal := by rw [hsplit, ENNReal.toReal_add ha₂ hd₂]
    have r2 : (1 - δ) * b₂.toReal ≤ a₂.toReal := by
      have := ENNReal.toReal_mono ha₂ h2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have r3 : I.toReal ≤ δ * b₁.toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁) h3
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
    have r4 : a₂.toReal ≤ c * b₁.toReal + I.toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hcb, hI⟩) h4
      rwa [ENNReal.toReal_add hcb hI, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at this
    have hB₁ : 0 ≤ b₁.toReal := ENNReal.toReal_nonneg
    have hB₂ : 0 ≤ b₂.toReal := ENNReal.toReal_nonneg
    have e1 : 0 ≤ (1 / 2 - δ) * b₂.toReal := mul_nonneg (by linarith) hB₂
    have hB2 : b₂.toReal ≤ 2 * (c + δ) * b₁.toReal := by linarith
    have e2 : δ * b₂.toReal ≤ δ * (2 * (c + δ) * b₁.toReal) :=
      mul_le_mul_of_nonneg_left hB2 hδ.le
    have e3 : δ * (3 * c + 3) * b₁.toReal ≤ ε * b₁.toReal := mul_le_mul_of_nonneg_right hδε hB₁
    have e4 : 0 ≤ δ * b₁.toReal * (c + 2 - 2 * δ) :=
      mul_nonneg (mul_nonneg hδ.le hB₁) (by linarith)
    rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hI, hd₂⟩)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁), ENNReal.toReal_add hI hd₂,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]
    linarith
  exact h5.trans hfin

/-- Relative `L¹` density of the weighted measures `θᵢ Hⁿ ⌞ Mᵢ`, as used for the locality of
approximate tangent spaces (Simon Ch. 3, Remark 1.8(1)): for `Hⁿ ⌞ (M₁ ∩ M₂)`-a.e. `x` and every
`ε > 0`, `∫_{B̄_s(x)} |1_{M₂} θ₂ − (θ₂(x)/θ₁(x)) 1_{M₁} θ₁| dHⁿ ≤ ε ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ` for
all small `s > 0`.  Cover `U` by balls `B_r(y)` with `B̄_r(y) ⊆ U`.  On each, `θᵢ` is integrable
on the compact `Mᵢ ∩ B̄_r(y)`, so the weighted Lebesgue-point and Besicovitch density limits hold
a.e. on `M₁ ∩ M₂ ∩ B_r(y)`; at such `x` they give the estimate, with `ρ = r − dist(x, y)`. -/
theorem Submission.fiw_tl_ae_l1_density :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ),
      M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) →
      (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ ε : ℝ, 0 < ε →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in closedBall x s,
          ‖M₂.indicator θ₂ z - θ₂ x / θ₁ x * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤
            ENNReal.ofReal ε * ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z)
              ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U hU M₁ M₂ θ₁ θ₂ hM₁U _hM₂U hM₁ hM₂ hθ₁ hθ₂ hθ₁i hθ₂i
  -- Step 1: it suffices to prove the claim a.e. on `M₁ ∩ M₂ ∩ B_r(y)` whenever `B̄_r(y) ⊆ U`.
  refine Submission.fiw_tl_ald_ball_reduction P _ U (M₁ ∩ M₂) _ hU
    (inter_subset_left.trans hM₁U) fun y r hyr => ?_
  -- Steps 2–4: `θᵢ` is integrable on the compact `Mᵢ ∩ B̄_r(y)`, so the weighted Lebesgue-point
  -- and density limits at `x` hold a.e. on `M₁ ∩ M₂ ∩ B_r(y)`.
  filter_upwards [Submission.fiw_tl_ald_local_differentiation P n M₁ M₂ θ₁ θ₂ y r hM₁ hM₂ hθ₁ hθ₂
      (hθ₁i _ (isCompact_closedBall y r) hyr) (hθ₂i _ (isCompact_closedBall y r) hyr),
    ae_restrict_mem₀ ((hM₁.inter hM₂).inter measurableSet_ball.nullMeasurableSet)]
    with x ⟨hL, hD⟩ hx
  -- Steps 5–8: the estimate at `x`, using `B̄_ρ(x) ⊆ B̄_r(y) ⊆ U` for `ρ = r - dist x y > 0`.
  have hρU : closedBall x (r - dist x y) ⊆ U :=
    (closedBall_subset_closedBall' (sub_add_cancel r _).le).trans hyr
  exact Submission.fiw_tl_ald_pointwise_estimate P n M₁ M₂ θ₁ θ₂ x hM₁ hM₂ hθ₁ hθ₂ hx.1
    ⟨r - dist x y, sub_pos.2 (mem_ball.1 hx.2), hθ₁i _ (isCompact_closedBall x _) hρU,
      hθ₂i _ (isCompact_closedBall x _) hρU⟩ hL hD

/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, Remarks 1.5(2), 1.8(1); the
step `T_x M_C = T_x M_Q` of Ch. 6, 3.13): for `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂`, every weighted approximate
tangent space of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.  By `fiw_tl_ae_l1_density`, a.e.
`x ∈ M₁ ∩ M₂` has `∫_{B̄_s(x)} |1_{M₂} θ₂ − c 1_{M₁} θ₁| dHⁿ = o(∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ)` as
`s ↓ 0`, where `c = θ₂(x) / θ₁(x)`, so `θ₂(x) = c θ₁(x)`.  As `x ∈ U`, some compact `B̄_ρ(x)` lies
in `U`, so `θᵢ` is integrable on `Mᵢ ∩ B̄_ρ(x)`, and `fiw_tl_transfer` carries the tangent space
from `(M₁, θ₁)` to `(M₂, θ₂)`.  The exceptional null set does not depend on `Q`. -/
theorem Submission.fiw_tangent_locality :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) → (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q := by
  intro P n U hU M₁ M₂ θ₁ θ₂ hM₁U hM₂U hM₁ hM₂ hθ₁ hθ₂ hθ₁i hθ₂i
  -- Step 1: a.e. `x ∈ M₁ ∩ M₂` is an `L¹`-density point with ratio `c = θ₂(x) / θ₁(x)`.
  filter_upwards [Submission.fiw_tl_ae_l1_density P n U hU M₁ M₂ θ₁ θ₂ hM₁U hM₂U hM₁ hM₂ hθ₁ hθ₂
    hθ₁i hθ₂i, ae_restrict_mem₀ (hM₁.inter hM₂)] with x hdens hx Q hQ
  -- Step 2: `x ∈ U` is open, so `B̄_ρ(x) ⊆ U` for some `ρ > 0`.
  obtain ⟨ρ, hρ, hρU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hM₁U hx.1))
  -- Step 3: transfer the tangent space; `θ₂(x) = (θ₂(x) / θ₁(x)) θ₁(x)` as `θ₁(x) > 0`.
  exact Submission.fiw_tl_transfer P n M₁ M₂ θ₁ θ₂ x (θ₂ x / θ₁ x) ρ hρ hM₁ hM₂
    (fun y hy => (hθ₁ y hy).le) (hθ₁i _ (isCompact_closedBall x ρ) hρU)
    (hθ₂i _ (isCompact_closedBall x ρ) hρU) (div_mul_cancel₀ (θ₂ x) (hθ₁ x hx.1).ne').symm
    hdens Q hQ
/-- **Mass of `τ(M, θ, ξ)` (Simon Ch. 6, Remark 3.2(3), with 2.7–2.8).**  If `T = τ(M, θ, ξ)` for a
rectifiable triple in `U`, then `M_W(T) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  For `Hⁿ`-a.e.
`x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal; with `dx^β` the coordinate wedges, the
Cauchy–Binet identity `∑_β ξ(x)(dx^β)² = 1` (from the expansion `α = ∑_β α(e_β) dx^β` applied to
`⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τₙ, ·⟩`) gives `|ξ(x)(α)| ≤ |α|`, hence `≤`, and makes `b = (ξ(dx^β))_β` a unit
vector with `ξ(∑_β b_β dx^β) = 1`.  For `≥`, exhaust `W ∩ U` by compact sets `K`; approximate
`1_K b` in `L¹(θ Hⁿ ⌞ K')`, `K'` a compact neighbourhood of `K`, by a continuous compactly
supported map, cut it off near `K`, retract it radially onto the unit ball, mollify and rescale.
The resulting test form `ω`, with `|ω| ≤ 1` and `spt ω ⊆ W`, has `T(ω) ≥ ∫_{K ∩ M} θ dHⁿ - ε`. -/
theorem Submission.fiw_im_mass_formula : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U hU T M θ ξ hR hT W hW
  classical
  -- Generic analytic tools, stated for an arbitrary normed space of coefficients.
  -- (D) `L¹` density of continuous compactly supported functions for a finite measure: the proof
  -- of Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` (`p = 1`), whose file is not
  -- imported here.
  have hdense : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (Eucl P))
      [IsFiniteMeasure μ] (f : Eucl P → E), MemLp f 1 μ → ∀ {ε : ℝ≥0∞}, ε ≠ 0 →
      ∃ g : Eucl P → E, HasCompactSupport g ∧ eLpNorm (f - g) 1 μ ≤ ε ∧
        Continuous g ∧ MemLp g 1 μ := by
    intro E _ _ μ _ f hf ε hε
    -- Urysohn approximation of `c • 1_s` for closed `s ⊆ u` open (Mathlib's
    -- `exists_continuous_eLpNorm_sub_le_of_closed`).
    have hury : ∀ {s u : Set (Eucl P)}, IsClosed s → IsOpen u → s ⊆ u → μ s ≠ ∞ →
        ∀ (c : E) {ε : ℝ≥0∞}, ε ≠ 0 → ∃ f : Eucl P → E,
          Continuous f ∧ eLpNorm (fun x => f x - s.indicator (fun _y => c) x) 1 μ ≤ ε ∧
            (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f 1 μ := by
      intro s u s_closed u_open hsu hs c ε hε
      obtain ⟨η, η_pos, hη⟩ :
          ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Eucl P), μ s ≤ η → NullMeasurableSet s μ →
              eLpNorm (s.indicator fun _x => c) 1 μ ≤ ε :=
        exists_eLpNorm_indicator_le ENNReal.one_ne_top c hε
      have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
      obtain ⟨V, sV, V_open, h'V, hV⟩ :
          ∃ (V : Set (Eucl P)), V ⊇ s ∧ IsOpen V ∧ μ V < ∞ ∧ μ (V \ s) < η :=
        s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
      let v := u ∩ V
      have hsv : s ⊆ v := subset_inter hsu sV
      have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
      obtain ⟨g, hgv, hgs, hg_range⟩ :=
        exists_continuous_zero_one_of_isClosed (u_open.inter V_open).isClosed_compl s_closed
          (disjoint_compl_left_iff.2 hsv)
      have g_norm : ∀ x, ‖g x‖ = g x := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
      have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
        intro x
        simp only [norm_smul, g_norm x]
        apply mul_le_of_le_one_left (norm_nonneg _)
        exact (hg_range x).2
      have gc_bd :
          ∀ x, ‖g x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
        intro x
        by_cases hv : x ∈ v
        · rw [← Set.sdiff_union_of_subset hsv] at hv
          rcases hv with hsv | hs
          · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
              Set.indicator_of_mem] using gc_bd0 x
          · simp [hgs hs, hs]
        · simp [hgv hv, show x ∉ s from fun h => hv (hsv h)]
      have gc_support : (Function.support fun x : Eucl P => g x • c) ⊆ v := by
        refine Function.support_subset_iff'.2 fun x hx => ?_
        simp only [hgv hx, Pi.zero_apply, zero_smul]
      have gc_mem : MemLp (fun x => g x • c) 1 μ := by
        refine MemLp.smul ?_ (memLp_top_const (μ := μ) c) (p := 1) (q := ∞) (r := 1)
        have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
        have : eLpNorm (v.indicator fun _x => (1 : ℝ)) 1 μ < ∞ :=
          (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
            simp [lt_top_iff_ne_top, hμv.ne]
        refine (eLpNorm_mono g.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
        by_cases hx : x ∈ v
        · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
            indicator_of_mem, CStarRing.norm_one]
        · simp only [hgv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
      refine ⟨fun x ↦ g x • c, by fun_prop,
        (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator s_closed.measurableSet)) gc_bd).trans ?_, gc_bd0,
          gc_support.trans inter_subset_left, gc_mem⟩
      exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
        ((u_open.measurableSet.inter V_open.measurableSet).diff
          s_closed.measurableSet).nullMeasurableSet
    suffices hex : ∃ g : Eucl P → E,
        eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ MemLp g 1 μ ∧ HasCompactSupport g by
      rcases hex with ⟨g, hg, g_cont, g_mem, g_support⟩
      exact ⟨g, g_support, hg, g_cont, g_mem⟩
    apply hf.induction_dense ENNReal.one_ne_top _ _ _ hε
    rotate_left
    · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
      exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
    intro c t ht htμ ε hε
    rcases exists_Lp_half E μ 1 hε with ⟨δ, δpos, hδ⟩
    obtain ⟨η, ηpos, hη⟩ :
        ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Eucl P), μ s ≤ η → NullMeasurableSet s μ →
            eLpNorm (s.indicator fun _x => c) 1 μ ≤ δ :=
      exists_eLpNorm_indicator_le ENNReal.one_ne_top c δpos.ne'
    have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
    obtain ⟨s, st, s_compact, s_closed, μs⟩ :
        ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
      ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
    have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
    have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) 1 μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
      exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
    obtain ⟨k, k_compact, sk⟩ : ∃ k : Set (Eucl P), IsCompact k ∧ s ⊆ interior k :=
      exists_compact_superset s_compact
    rcases hury s_closed isOpen_interior sk hsμ.ne c δpos.ne'
      with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
    have I3 : eLpNorm (f - t.indicator fun _y => c) 1 μ ≤ ε := by
      convert (hδ _ _ I2 I1).le using 2
      ext x
      simp
    refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
    rw [← Function.notMem_support]
    contrapose hx
    exact interior_subset (f_support hx)
  -- (S) Smoothing: a continuous compactly supported map with `tsupport ⊆ O` (`O` open) is a
  -- uniform limit of smooth maps with compact `tsupport ⊆ O` (convolution with a normalized
  -- bump, then a smooth cutoff equal to `1` on the support).
  have hmoll : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (O : Set (Eucl P)) (u : Eucl P → E), IsOpen O → Continuous u → HasCompactSupport u →
      tsupport u ⊆ O → ∀ ε : ℝ, 0 < ε → ∃ v : Eucl P → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ tsupport v ⊆ O ∧ HasCompactSupport v ∧
          ∀ x, ‖u x - v x‖ ≤ ε := by
    intro E _ _ _ O u hO hu huc huO ε hε
    obtain ⟨O', hO'o, hKO', hO'O, hO'c⟩ :=
      exists_open_between_and_isCompact_closure huc.isCompact hO huO
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hO'o (isClosed_tsupport u) hKO'
    obtain ⟨δ, hδ, huδ⟩ :=
      Metric.uniformContinuous_iff.mp (huc.uniformContinuous_of_continuous hu) ε hε
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
    obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (u x) ≤ ε :=
      ⟨convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume,
        hψc.contDiff_convolution_left _ hψd hu.locallyIntegrable,
        fun x => dist_convolution_le hε.le hψs hψnn hψ1 hu.aestronglyMeasurable
          fun y hy => (huδ (mem_ball.mp hy)).le⟩
    have hv_supp : tsupport (fun x => χ x • g x) ⊆ closure O' := by
      refine (tsupport_smul_subset_left χ g).trans ?_
      rw [tsupport, hχs]
    refine ⟨fun x => χ x • g x, hχ.smul hg, hv_supp.trans hO'O,
      hO'c.of_isClosed_subset (isClosed_tsupport _) hv_supp, fun x => ?_⟩
    beta_reduce
    by_cases hx : x ∈ tsupport u
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  -- (R) The radial retraction `a ↦ a / max 1 ‖a‖` onto the closed unit ball is `2`-Lipschitz
  -- towards points of the ball.
  have hretr : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E), ‖b‖ ≤ 1 →
      ‖(max 1 ‖a‖)⁻¹ • a‖ ≤ 1 ∧ ‖(max 1 ‖a‖)⁻¹ • a - b‖ ≤ 2 * ‖a - b‖ := by
    intro E _ _ a b hb
    have hm : 0 < max 1 ‖a‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, inv_mul_le_iff₀ hm, mul_one]
      exact le_max_right _ _
    · rcases le_total ‖a‖ 1 with ha | ha
      · rw [max_eq_left ha, inv_one, one_smul]
        linarith [norm_nonneg (a - b)]
      · rw [max_eq_right ha]
        have ha0 : 0 < ‖a‖ := lt_of_lt_of_le one_pos ha
        have h1 : ‖‖a‖⁻¹ • a - a‖ = ‖a‖ - 1 := by
          have : ‖a‖⁻¹ • a - a = (‖a‖⁻¹ - 1) • a := by rw [sub_smul, one_smul]
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos, neg_sub, sub_mul,
            inv_mul_cancel₀ ha0.ne', one_mul]
          rw [sub_nonpos]
          exact inv_le_one_of_one_le₀ ha
        have h2 := norm_le_norm_sub_add a b
        calc ‖‖a‖⁻¹ • a - b‖ ≤ ‖‖a‖⁻¹ • a - a‖ + ‖a - b‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * ‖a - b‖ := by rw [h1]; linarith
  -- Linear algebra of `n`-covectors on `ℝ^P` (Simon 1.1–1.5) and Cauchy–Binet.
  set dx : SimonMultiIndex n P → Covector (Eucl P) n :=
    fun I => wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) with hdx
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1 with he
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P, dx β (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    simp only [hdx]
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
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
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [e, PiLp.single_apply, hi j]
  -- Coordinate expansion `α = ∑_β α(e_β) dx^β`.
  have hexp : ∀ α : Covector (Eucl P) n,
      α = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β • dx β := by
    intro α
    set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • dx β with hR
    have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
      intro γ
      rw [hR, ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
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
    symm
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousAlternatingMap.coe_toAlternatingMap]
    exact h2 v hv
  -- The Euclidean coefficient norm as a sum over increasing multi-indices.
  have hnorm : ∀ α : Covector (Eucl P) n, covectorEuclideanNorm α =
      Real.sqrt (∑ β : SimonMultiIndex n P, (euclideanCovectorCoordinate α β) ^ 2) := by
    intro α
    unfold covectorEuclideanNorm
    congr 1
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij (fun β : SimonMultiIndex n P => (β : Fin n → Fin P))
    · intro β _
      simpa using β.strictMono
    · intro β _ γ _ h
      exact DFunLike.coe_injective h
    · intro I hI
      have hI' : StrictMono I := (Finset.mem_filter.mp hI).2
      exact ⟨OrderEmbedding.ofStrictMono I hI', Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
    · intro β _
      simp [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]
  -- Cauchy–Binet: for an orthonormal frame `τ` and `ζ = ±τ₁ ∧ ⋯ ∧ τₙ`,
  -- `|ζ(α)| ≤ |α|` and `∑_β ζ(dx^β)² = 1`.
  have hALG : ∀ τ : Fin n → Eucl P, Orthonormal ℝ τ → ∀ ζ : NVector (Eucl P) n,
      (ζ = simpleNVector τ ∨ ζ = -simpleNVector τ) →
      (∀ α : Covector (Eucl P) n, |ζ α| ≤ covectorEuclideanNorm α) ∧
        ∑ β : SimonMultiIndex n P, (ζ (dx β)) ^ 2 = 1 := by
    intro τ hτ ζ hζ
    set α₀ : Covector (Eucl P) n := wedgeCovectors n (fun i => innerSL ℝ (τ i)) with hα₀
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀, wedgeCovectors_apply_det]
      have h1 : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp [innerSL_apply_apply, orthonormal_iff_ite.mp hτ, Matrix.one_apply]
      rw [h1, Matrix.det_one]
    have hα₀e : ∀ β : SimonMultiIndex n P, euclideanCovectorCoordinate α₀ β = dx β τ := by
      intro β
      simp only [euclideanCovectorCoordinate, hα₀, hdx, wedgeCovectors_apply_det]
      rw [← Matrix.det_transpose]
      congr 1
      ext i j
      simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    have heval : ∀ α : Covector (Eucl P) n,
        α τ = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β * dx β τ := by
      intro α
      conv_lhs => rw [hexp α]
      rw [ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hsum1 : ∑ β : SimonMultiIndex n P, (dx β τ) ^ 2 = 1 := by
      rw [← hα₀τ, heval α₀]
      simp only [hα₀e, sq]
    obtain ⟨s, hs, hζs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ∀ α : Covector (Eucl P) n, ζ α = s * α τ := by
      rcases hζ with rfl | rfl
      · exact ⟨1, Or.inl rfl, fun α => by simp⟩
      · exact ⟨-1, Or.inr rfl, fun α => by simp⟩
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    refine ⟨fun α => ?_, ?_⟩
    · rw [hζs, abs_mul, habs, one_mul, hnorm, heval]
      apply Real.abs_le_sqrt
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun β => euclideanCovectorCoordinate α β) (fun β => dx β τ)
      rwa [hsum1, mul_one] at this
    · simp only [hζs, mul_pow, hs2, one_mul, hsum1]
  -- Coordinates on `Λⁿ`: `L y = ∑_β y_β dx^β` for `y ∈ ℝ^{multi-indices}` (Euclidean norm), so
  -- `|L y| = ‖y‖`, and `Bv ζ = (ζ(dx^β))_β`.
  set H : Measure (Eucl P) := (μHE[n] : Measure (Eucl P)) with hH
  set L : EuclideanSpace ℝ (SimonMultiIndex n P) →L[ℝ] Covector (Eucl P) n :=
    ∑ β : SimonMultiIndex n P, (EuclideanSpace.proj β).smulRight (dx β) with hL
  have hLapp : ∀ y : EuclideanSpace ℝ (SimonMultiIndex n P),
      L y = ∑ β : SimonMultiIndex n P, y.ofLp β • dx β := by
    intro y
    rw [hL, sum_apply]
    rfl
  have hLnorm : ∀ y : EuclideanSpace ℝ (SimonMultiIndex n P),
      covectorEuclideanNorm (L y) = ‖y‖ := by
    intro y
    rw [hnorm, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hc : euclideanCovectorCoordinate (L y) γ = y.ofLp γ := by
      change (L y) (e γ) = y.ofLp γ
      rw [hLapp, ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc, Real.norm_eq_abs, sq_abs]
  have hLζ : ∀ (ζ : NVector (Eucl P) n) (y : EuclideanSpace ℝ (SimonMultiIndex n P)),
      ζ (L y) = ∑ β : SimonMultiIndex n P, y.ofLp β * ζ (dx β) := by
    intro ζ y
    rw [hLapp, map_sum]
    simp only [map_smul, smul_eq_mul]
  set Bv : NVector (Eucl P) n → EuclideanSpace ℝ (SimonMultiIndex n P) :=
    fun ζ => WithLp.toLp 2 (fun β => ζ (dx β)) with hBv
  have hBvc : Continuous Bv :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun β => continuous_id.clm_apply continuous_const)
  -- Pointwise consequences of the orientation condition, `Hⁿ`-a.e. on `M`.
  have hpt : ∀ᵐ x ∂(H.restrict M),
      (∀ α : Covector (Eucl P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ ‖Bv (ξ x)‖ = 1 ∧
        ξ x (L (Bv (ξ x))) = 1 := by
    filter_upwards [hR.orients] with x hx
    obtain ⟨τ, hτ, -, hξτ⟩ := hx
    obtain ⟨h1, h2⟩ := hALG τ hτ (ξ x) hξτ
    refine ⟨h1, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]
      simp only [hBv, Real.norm_eq_abs, sq_abs, h2, Real.sqrt_one]
    · rw [hLζ, ← h2]
      simp only [hBv, sq]
  -- `M_W(T) ≤ ∫_{M ∩ W} θ dHⁿ`: `|T(ω)| ≤ ∫_M θ |ξ(ω)| dHⁿ` and `|ξ(ω)| ≤ |ω| ≤ 1_W`.
  have hle : T.massOn W ≤ ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H := by
    apply sSup_le
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    change ENNReal.ofReal (T ω) ≤ _
    rw [hT ω]
    calc ENNReal.ofReal (tauAction n M θ ξ ω)
        ≤ ENNReal.ofReal ‖∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x) ∂H‖ :=
          ENNReal.ofReal_le_ofReal (Real.le_norm_self _)
      _ ≤ ENNReal.ofReal (∫⁻ x in M,
            ENNReal.ofReal ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)‖ ∂H).toReal :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)
      _ ≤ ∫⁻ x in M, ENNReal.ofReal ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)‖ ∂H :=
          ENNReal.ofReal_toReal_le
      _ ≤ ∫⁻ x in M, W.indicator (fun x => ENNReal.ofReal (θ x)) x ∂H := by
          apply lintegral_mono_ae
          filter_upwards [hpt, ae_restrict_mem₀ hR.nullMeasurableSet] with x hx hxM
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hR.pos x hxM)]
            exact mul_le_of_le_one_right (hR.pos x hxM).le ((hx.1 _).trans (hω1 x))
          · have h0 : (ω : DifferentialForm (Eucl P) n) x = 0 :=
              image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h)
            rw [h0, map_zero, mul_zero, norm_zero, ENNReal.ofReal_zero]
            exact bot_le
      _ = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H := by
          rw [lintegral_indicator hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
            inter_comm]
  -- `∫_{K ∩ M} θ dHⁿ ≤ M_W(T)` for compact `K ⊆ W ∩ U`.
  have hmain : ∀ K : Set (Eucl P), IsCompact K → K ⊆ W ∩ U →
      ∫⁻ x in K ∩ M, ENNReal.ofReal (θ x) ∂H ≤ T.massOn W := by
    intro K hK hKV
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hθK : IntegrableOn θ (K ∩ M) H := by
      rw [inter_comm]
      exact hR.integrableOn K hK (hKV.trans inter_subset_right)
    have hKMn : NullMeasurableSet (K ∩ M) H := hKm.nullMeasurableSet.inter hR.nullMeasurableSet
    rw [← ofReal_integral_eq_lintegral_ofReal hθK
      ((ae_restrict_mem₀ hKMn).mono fun x hx => (hR.pos x hx.2).le)]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨ω, hωad, hωT⟩ : ∃ ω ∈ massAdmissibleOn U n W,
        (∫ x in K ∩ M, θ x ∂H) - ε ≤ T ω := by
      -- Open sets `K ⊆ O₁ ⊆ closure O₁ ⊆ O₂ ⊆ closure O₂ = K' ⊆ W ∩ U`, `K'` compact.
      obtain ⟨O₂, hO₂o, hKO₂, hO₂V, hO₂c⟩ :=
        exists_open_between_and_isCompact_closure hK (hW.inter hU) hKV
      obtain ⟨O₁, hO₁o, hKO₁, hO₁O₂, hO₁c⟩ :=
        exists_open_between_and_isCompact_closure hK hO₂o hKO₂
      set K' := closure O₂ with hK'
      have hK'm : MeasurableSet K' := isClosed_closure.measurableSet
      have hK'U : K' ⊆ U := hO₂V.trans inter_subset_right
      have hKK' : K ⊆ K' := hKO₂.trans subset_closure
      have hθK' : IntegrableOn θ (K' ∩ M) H := by
        rw [inter_comm]
        exact hR.integrableOn K' hO₂c hK'U
      -- The finite measure `ν = θ Hⁿ ⌞ (K' ∩ M)`.
      set ν : Measure (Eucl P) :=
        (H.restrict (K' ∩ M)).withDensity (fun x => ENNReal.ofReal (θ x)) with hν
      have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hθK'.hasFiniteIntegral
      have hνac : ν ≪ H.restrict M :=
        (withDensity_absolutelyContinuous _ _).trans
          (Measure.absolutelyContinuous_of_le (Measure.restrict_mono inter_subset_right le_rfl))
      -- The target `f = 1_K (ζ(dx^β))_β`, `‖f‖ ≤ 1`.
      set f : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        K.indicator (fun x => Bv (ξ x)) with hf
      have hfM : AEStronglyMeasurable f (H.restrict M) :=
        (hBvc.comp_aestronglyMeasurable hR.aestronglyMeasurable).indicator hKm
      have hf1 : ∀ᵐ x ∂(H.restrict M), ‖f x‖ ≤ 1 := by
        filter_upwards [hpt] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK, hx.2.1]
        · rw [hf, indicator_of_notMem hxK, norm_zero]
          exact zero_le_one
      have hfmem : MemLp f 1 ν := MemLp.of_bound (hfM.mono_ac hνac) 1 (hνac.ae_le hf1)
      -- Tolerances.
      set C : ℝ := (ν univ).toReal with hC
      have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
      set ε₁ : ℝ := (ε : ℝ) / 4 with hε₁
      set ε₂ : ℝ := (ε : ℝ) / (4 * (C + 1)) with hε₂
      have hε₁0 : 0 < ε₁ := by positivity
      have hε₂0 : 0 < ε₂ := by positivity
      -- `L¹(ν)` approximation of `f` by a continuous compactly supported `γ₀`.
      obtain ⟨γ₀, -, hγ₀ε, hγ₀c, -⟩ :=
        hdense (EuclideanSpace ℝ (SimonMultiIndex n P)) ν f hfmem
          (ε := ENNReal.ofReal ε₁) (ENNReal.ofReal_pos.mpr hε₁0).ne'
      -- Cutoff `χ` (`= 1` on `K`, `= 0` off `O₁`), then the radial retraction.
      obtain ⟨χ, hχ0, hχ1, hχr⟩ := exists_continuous_zero_one_of_isClosed hO₁o.isClosed_compl
        hK.isClosed (disjoint_compl_left_iff_subset.mpr hKO₁)
      set γ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        fun x => (max 1 ‖χ x • γ₀ x‖)⁻¹ • (χ x • γ₀ x) with hγ
      have hγc : Continuous γ := by
        have h1 : Continuous fun x => χ x • γ₀ x := χ.continuous.smul hγ₀c
        exact ((continuous_const.max h1.norm).inv₀ fun x =>
          (lt_of_lt_of_le one_pos (le_max_left _ _)).ne').smul h1
      have hγs : Function.support γ ⊆ O₁ := by
        intro x hx
        by_contra hxO
        apply hx
        have h0 : χ x = 0 := hχ0 hxO
        simp only [hγ, h0, zero_smul, smul_zero]
      have hγts : tsupport γ ⊆ O₂ := (closure_mono hγs).trans hO₁O₂
      have hγcs : HasCompactSupport γ :=
        hO₁c.of_isClosed_subset (isClosed_tsupport _) (closure_mono hγs)
      have hγ1 : ∀ x, ‖γ x‖ ≤ 1 := fun x => (hretr _ (χ x • γ₀ x) 0 (by simp)).1
      have hγf : ∀ x, ‖f x‖ ≤ 1 → ‖γ x - f x‖ ≤ 2 * ‖γ₀ x - f x‖ := by
        intro x hx
        refine (hretr _ (χ x • γ₀ x) (f x) hx).2.trans ?_
        gcongr
        by_cases hxK : x ∈ K
        · rw [show χ x = 1 from hχ1 hxK, one_smul]
        · rw [hf, indicator_of_notMem hxK, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hχr x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχr x).2
      -- Smoothing and rescaling: `ψ = (1 + ε₂)⁻¹ φ`, `‖ψ‖ ≤ 1`, `‖ψ - γ‖ ≤ 2 ε₂`.
      obtain ⟨φ, hφd, hφO₂, hφc, hφε⟩ :=
        hmoll (EuclideanSpace ℝ (SimonMultiIndex n P)) O₂ γ hO₂o hγc hγcs hγts ε₂ hε₂0
      have hφ1 : ∀ x, ‖φ x‖ ≤ 1 + ε₂ := fun x => by
        have h1 := norm_le_norm_sub_add (φ x) (γ x)
        rw [norm_sub_rev] at h1
        linarith [hφε x, hγ1 x]
      set ψ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        fun x => (1 + ε₂)⁻¹ • φ x with hψ
      have hε₂1 : (0 : ℝ) < 1 + ε₂ := by linarith
      have hψ1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
        rw [hψ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε₂1, inv_mul_le_iff₀ hε₂1,
          mul_one]
        exact hφ1 x
      have hψγ : ∀ x, ‖ψ x - γ x‖ ≤ 2 * ε₂ := fun x => by
        have h1 : ‖ψ x - φ x‖ ≤ ε₂ := by
          have h2 : ψ x - φ x = ((1 + ε₂)⁻¹ - 1) • φ x := by rw [hψ, sub_smul, one_smul]
          have h3 : |(1 + ε₂)⁻¹ - 1| * (1 + ε₂) = ε₂ := by
            rw [abs_of_nonpos (by rw [sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith)),
              neg_sub, sub_mul, inv_mul_cancel₀ hε₂1.ne', one_mul]
            ring
          rw [h2, norm_smul, Real.norm_eq_abs]
          calc |(1 + ε₂)⁻¹ - 1| * ‖φ x‖ ≤ |(1 + ε₂)⁻¹ - 1| * (1 + ε₂) :=
                mul_le_mul_of_nonneg_left (hφ1 x) (abs_nonneg _)
            _ = ε₂ := h3
        calc ‖ψ x - γ x‖ ≤ ‖ψ x - φ x‖ + ‖φ x - γ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ε₂ + ε₂ := add_le_add h1 (by rw [norm_sub_rev]; exact hφε x)
          _ = 2 * ε₂ := by ring
      have hψc : Continuous ψ := by
        have hφcont : Continuous φ := hφd.continuous
        rw [hψ]
        fun_prop
      have hψts : tsupport ψ ⊆ O₂ :=
        (tsupport_comp_subset (g := fun y => (1 + ε₂)⁻¹ • y) (smul_zero _) φ).trans hφO₂
      have hψcs : HasCompactSupport ψ :=
        hφc.comp_left (g := fun y => (1 + ε₂)⁻¹ • y) (smul_zero _)
      -- The test form `ω' = L ∘ ψ`.
      set ω' : Eucl P → Covector (Eucl P) n := fun x => L (ψ x) with hω'
      have hω'd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω' :=
        L.contDiff.comp (hφd.const_smul ((1 + ε₂)⁻¹))
      have hω'ts : tsupport ω' ⊆ O₂ :=
        (tsupport_comp_subset (g := fun y => L y) (map_zero L) ψ).trans hψts
      have hω'c : HasCompactSupport ω' := hψcs.comp_left (g := fun y => L y) (map_zero L)
      have hω'cont : Continuous ω' := L.continuous.comp hψc
      have hO₂W : O₂ ⊆ W ∩ U := subset_closure.trans hO₂V
      refine ⟨⟨ω', ⟨hω'd, hω'c⟩, hω'ts.trans (hO₂W.trans inter_subset_right)⟩,
        ⟨hω'ts.trans (hO₂W.trans inter_subset_left), fun x => ?_⟩, ?_⟩
      · change covectorEuclideanNorm (L (ψ x)) ≤ 1
        rw [hLnorm]
        exact hψ1 x
      · -- `∫_{K ∩ M} θ - ε ≤ T ω`.
        rw [hT]
        change (∫ x in K ∩ M, θ x ∂H) - ε ≤ ∫ x in M, θ x * ξ x (ω' x) ∂H
        have hg₁ : Integrable (K.indicator θ) (H.restrict M) := by
          rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
          exact hθK
        have hξω : AEStronglyMeasurable (fun x => ξ x (ω' x)) (H.restrict M) :=
          (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
            (hR.aestronglyMeasurable.prodMk hω'cont.aestronglyMeasurable)
        have hξω1 : ∀ᵐ x ∂(H.restrict M), ‖ξ x (ω' x)‖ ≤ 1 := by
          filter_upwards [hpt] with x hx
          rw [Real.norm_eq_abs]
          exact (hx.1 _).trans ((hLnorm _).trans_le (hψ1 x))
        have hω'0 : ∀ x, x ∉ K' → ω' x = 0 := fun x hx =>
          image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hω'ts h))
        have hg₂ : Integrable (fun x => θ x * ξ x (ω' x)) (H.restrict M) := by
          have h1 : Integrable (K'.indicator θ) (H.restrict M) := by
            rw [integrable_indicator_iff hK'm, IntegrableOn, Measure.restrict_restrict hK'm]
            exact hθK'
          refine (h1.mul_bdd hξω hξω1).congr (Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ K'
          · simp only [indicator_of_mem hx]
          · simp only [indicator_of_notMem hx, hω'0 x hx, map_zero, mul_zero]
        have hint : (∫ x in K ∩ M, θ x ∂H) = ∫ x in M, K.indicator θ x ∂H := by
          rw [integral_indicator hKm, Measure.restrict_restrict hKm]
        have hkey : ∫⁻ x in M, ENNReal.ofReal ‖K.indicator θ x - θ x * ξ x (ω' x)‖ ∂H ≤
            ENNReal.ofReal ε := by
          have hθm : AEMeasurable (fun x => ENNReal.ofReal (θ x)) (H.restrict (K' ∩ M)) :=
            hθK'.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          have hfK' : AEStronglyMeasurable f (H.restrict (K' ∩ M)) :=
            hfM.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
          have hgm : AEMeasurable (fun x => ENNReal.ofReal ‖f x - ψ x‖) (H.restrict (K' ∩ M)) :=
            (hfK'.sub hψc.aestronglyMeasurable).norm.aemeasurable.ennreal_ofReal
          have hfγ₀ : AEStronglyMeasurable (f - γ₀) ν :=
            (hfM.mono_ac hνac).sub hγ₀c.aestronglyMeasurable
          have hγ₀ε' : ∫⁻ x, ‖f x - γ₀ x‖ₑ ∂ν ≤ ENNReal.ofReal ε₁ := by
            rw [eLpNorm_one_eq_lintegral_enorm hfγ₀] at hγ₀ε
            exact hγ₀ε
          calc ∫⁻ x in M, ENNReal.ofReal ‖K.indicator θ x - θ x * ξ x (ω' x)‖ ∂H
              ≤ ∫⁻ x in M, K'.indicator
                  (fun x => ENNReal.ofReal (θ x) * ENNReal.ofReal ‖f x - ψ x‖) x ∂H := by
                apply lintegral_mono_ae
                filter_upwards [hpt, ae_restrict_mem₀ hR.nullMeasurableSet] with x hx hxM
                have hθx := hR.pos x hxM
                have hid : K.indicator θ x - θ x * ξ x (ω' x) = θ x * ξ x (L (f x - ψ x)) := by
                  rw [map_sub L, map_sub (ξ x)]
                  by_cases hxK : x ∈ K
                  · rw [indicator_of_mem hxK, hf, indicator_of_mem hxK, hx.2.2]
                    ring
                  · rw [indicator_of_notMem hxK, hf, indicator_of_notMem hxK, map_zero, map_zero]
                    ring
                rw [hid]
                by_cases hxK' : x ∈ K'
                · rw [indicator_of_mem hxK', ← ENNReal.ofReal_mul hθx.le]
                  apply ENNReal.ofReal_le_ofReal
                  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθx]
                  exact mul_le_mul_of_nonneg_left ((hx.1 _).trans (hLnorm _).le) hθx.le
                · have hf0 : f x = 0 := indicator_of_notMem (fun h => hxK' (hKK' h)) _
                  have hψ0 : ψ x = 0 :=
                    image_eq_zero_of_notMem_tsupport fun h => hxK' (subset_closure (hψts h))
                  rw [indicator_of_notMem hxK', hf0, hψ0, sub_zero, map_zero, map_zero, mul_zero,
                    norm_zero, ENNReal.ofReal_zero]
            _ = ∫⁻ x, ENNReal.ofReal ‖f x - ψ x‖ ∂ν := by
                rw [lintegral_indicator hK'm, Measure.restrict_restrict hK'm]
                exact (lintegral_withDensity_eq_lintegral_mul₀ hθm hgm).symm
            _ ≤ ∫⁻ x, (2 * ‖f x - γ₀ x‖ₑ + ENNReal.ofReal (2 * ε₂)) ∂ν := by
                apply lintegral_mono_ae
                filter_upwards [hνac.ae_le hf1] with x hx
                have h1 : ‖f x - ψ x‖ ≤ 2 * ‖f x - γ₀ x‖ + 2 * ε₂ :=
                  calc ‖f x - ψ x‖ ≤ ‖f x - γ x‖ + ‖γ x - ψ x‖ :=
                        norm_sub_le_norm_sub_add_norm_sub _ _ _
                    _ ≤ 2 * ‖f x - γ₀ x‖ + 2 * ε₂ := by
                        rw [norm_sub_rev (f x) (γ x), norm_sub_rev (f x) (γ₀ x),
                          norm_sub_rev (γ x) (ψ x)]
                        exact add_le_add (hγf x hx) (hψγ x)
                calc ENNReal.ofReal ‖f x - ψ x‖ ≤ ENNReal.ofReal (2 * ‖f x - γ₀ x‖ + 2 * ε₂) :=
                      ENNReal.ofReal_le_ofReal h1
                  _ = 2 * ‖f x - γ₀ x‖ₑ + ENNReal.ofReal (2 * ε₂) := by
                      rw [ENNReal.ofReal_add (by positivity) (by positivity),
                        ENNReal.ofReal_mul (by norm_num), ofReal_norm, ENNReal.ofReal_ofNat]
            _ = 2 * ∫⁻ x, ‖f x - γ₀ x‖ₑ ∂ν + ENNReal.ofReal (2 * ε₂) * ν univ := by
                rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
                  lintegral_const]
            _ ≤ 2 * ENNReal.ofReal ε₁ + ENNReal.ofReal (2 * ε₂) * ENNReal.ofReal C := by
                rw [hC, ENNReal.ofReal_toReal (measure_ne_top ν univ)]
                gcongr
            _ = ENNReal.ofReal (2 * ε₁ + 2 * ε₂ * C) := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity),
                  ENNReal.ofReal_mul (p := 2 * ε₂) (q := C) (by positivity),
                  ENNReal.ofReal_mul (p := 2) (q := ε₁) (by norm_num), ENNReal.ofReal_ofNat]
            _ ≤ ENNReal.ofReal ε := by
                apply ENNReal.ofReal_le_ofReal
                have h1 : ε₂ * C + ε₂ = (ε : ℝ) / 4 := by
                  rw [hε₂]
                  field_simp
                rw [hε₁]
                linarith
        have h1 := norm_integral_le_lintegral_norm (μ := H.restrict M)
          (fun x => K.indicator θ x - θ x * ξ x (ω' x))
        rw [integral_sub hg₁ hg₂] at h1
        have h2 := (Real.le_norm_self _).trans
          (h1.trans (ENNReal.toReal_le_of_le_ofReal hε0.le hkey))
        rw [hint]
        linarith
    calc ENNReal.ofReal (∫ x in K ∩ M, θ x ∂H) ≤ ENNReal.ofReal (T ω + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (T ω) + ε := by rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ T.massOn W + ε := add_le_add_left (T.le_massOn hωad) _
  -- `∫_{M ∩ W} θ dHⁿ ≤ M_W(T)`: exhaust `W ∩ U` by compact sets.
  have hge : ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H ≤ T.massOn W := by
    have hVo : IsOpen (W ∩ U) := hW.inter hU
    obtain ⟨F, hFc, hFV, hFU, hFm⟩ := hVo.exists_iUnion_isClosed
    set Kk : ℕ → Set (Eucl P) := fun k => F k ∩ closedBall 0 k with hKk
    have hKkc : ∀ k, IsCompact (Kk k) := fun k =>
      (isCompact_closedBall (0 : Eucl P) (k : ℝ)).inter_left (hFc k)
    have hKkV : ∀ k, Kk k ⊆ W ∩ U := fun k => inter_subset_left.trans (hFV k)
    have hKkm : Monotone Kk := fun k l hkl =>
      inter_subset_inter (hFm hkl) (Metric.closedBall_subset_closedBall (by exact_mod_cast hkl))
    have hKkU : ⋃ k, Kk k = W ∩ U := by
      refine Subset.antisymm (iUnion_subset hKkV) fun x hx => ?_
      rw [← hFU] at hx
      obtain ⟨k₀, hk₀⟩ := mem_iUnion.mp hx
      obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.mpr ⟨max k₀ k₁, hFm (le_max_left _ _) hk₀, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact hk₁.trans (by exact_mod_cast le_max_right _ _)
    set ν₀ : Measure (Eucl P) := (H.restrict M).withDensity (fun x => ENNReal.ofReal (θ x))
      with hν₀
    have hν₀A : ∀ A : Set (Eucl P), MeasurableSet A →
        ν₀ A = ∫⁻ x in A ∩ M, ENNReal.ofReal (θ x) ∂H := by
      intro A hA
      rw [hν₀, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hMW : M ∩ W = (W ∩ U) ∩ M := by
      ext x
      constructor
      · rintro ⟨hxM, hxW⟩
        exact ⟨⟨hxW, hR.subset hxM⟩, hxM⟩
      · rintro ⟨⟨hxW, -⟩, hxM⟩
        exact ⟨hxM, hxW⟩
    rw [hMW, ← hν₀A _ hVo.measurableSet, ← hKkU, hKkm.measure_iUnion]
    refine iSup_le fun k => ?_
    rw [hν₀A _ (hKkc k).isClosed.measurableSet]
    exact hmain (Kk k) (hKkc k) (hKkV k)
  exact le_antisymm hle hge

/-- **Integer series of integer multiplicity currents (Simon Ch. 6, Lemma 3.13 for `M`-absolutely
convergent series, as used for `R^(ℓ)`, `S^(ℓ)` in the proof of 7.2; contains Remark 3.2(1)).**
If the `T_r` are integer multiplicity and `∑ |c_r| M_W(T_r) < ∞` for every `W ⊂⊂ U`, then
`S(ω) = ∑ c_r T_r(ω)` (unconditionally) defines an integer multiplicity current with
`M_W(S) ≤ ∑ |c_r| M_W(T_r)` for every `W`.  `Submission.fiw_ims_series_current` gives the current
`S` and the mass bound.  Writing `T_r = τ(M_r, θ_r, ξ_r)`, the mass formula 3.2(3)
(`Submission.fiw_im_mass_formula`) turns the hypothesis into `∑ |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞`, so
`Submission.fiw_ims_combine`, with tangent locality `Submission.fiw_tangent_locality`, gives an
integer rectifiable triple `(M', θ', ξ')` with `∑ c_r T_r(ω) = τ(M', θ', ξ')(ω)`.  By uniqueness of
sums `S = τ(M', θ', ξ')`. -/
theorem Submission.fiw_im_series : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : ℕ → GeometricCurrentOn U n) (c : ℕ → ℤ), (∀ r, IsIntegerMultiplicity (T r)) → (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W) < ∞) → ∃ S : GeometricCurrentOn U n, (∀ ω, HasSum (fun r => (c r : ℝ) * T r ω) (S ω)) ∧ (∀ W, S.massOn W ≤ ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W) ∧ IsIntegerMultiplicity S := by
  intro P n U hU T c hIM hmass
  -- Steps 1–4: `S(ω) = ∑ c_r T_r(ω)` is a current with `M_W(S) ≤ ∑ |c_r| M_W(T_r)`.
  obtain ⟨S, hS, hSmass⟩ := Submission.fiw_ims_series_current P n U hU T c hmass
  -- Step 5: representations `T_r = τ(M_r, θ_r, ξ_r)` with `θ_r` natural-valued on `M_r`.
  have hIM' : ∀ r, ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple U n M θ ξ ∧ (∀ x ∈ M, ∃ k : ℕ, θ x = k) ∧
        ∀ ω : TestFormOn U n, T r ω = tauAction n M θ ξ ω := hIM
  choose M θ ξ htri hnat hrep using hIM'
  -- The mass formula `M_W(T_r) = ∫_{M_r ∩ W} θ_r dHⁿ` (open `W`) rewrites the summability
  -- hypothesis in terms of the multiplicities.
  have hint : ∀ W, CompactlyContainedOpen W U →
      (∑' r, ((c r).natAbs : ℝ≥0∞) *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞ := by
    intro W hW
    have hEq : ∀ r, (T r).massOn W =
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P)) := fun r =>
      Submission.fiw_im_mass_formula P n U hU (T r) (M r) (θ r) (ξ r) (htri r) (hrep r) W hW.1
    simpa only [hEq] using hmass W hW
  -- Steps 6–9: the series of triples is represented by one integer rectifiable triple.
  obtain ⟨M', θ', ξ', htri', hnat', hsum'⟩ :=
    Submission.fiw_ims_combine P n U hU (Submission.fiw_tangent_locality P n U hU) M θ ξ c htri
      hnat hint
  -- `S = τ(M', θ', ξ')`: both are the sum of `c_r T_r(ω) = c_r τ(M_r, θ_r, ξ_r)(ω)`.
  refine ⟨S, hS, hSmass, M', θ', ξ', htri', hnat', fun ω => (hS ω).unique ?_⟩
  simpa only [hrep] using hsum' ω

/-- Simon Ch. 6, Remark 3.2(1): if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and `a, b ∈ ℤ`,
then `S = a T₁ + b T₂` is integer multiplicity.  This is the finite case of
`Submission.fiw_im_series`, for the family `(T₁, T₂, T₁, T₁, …)` with coefficients
`(a, b, 0, 0, …)`; its mass hypothesis holds because integer multiplicity currents have
`M_W < ∞` for `W ⊂⊂ U` (`Submission.fiw_im_mass_formula`). -/
theorem Submission.fiw_im_lincomb :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ),
      IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ →
      (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U hU T₁ T₂ S a b h₁ h₂ hS
  -- `X = τ(M, θ, ξ)` has `M_W(X) = ∫_{M ∩ W} θ dHⁿ ≤ ∫_{M ∩ closure W} θ dHⁿ < ∞` for `W ⊂⊂ U`.
  have hfin : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X →
      ∀ W, CompactlyContainedOpen W U → X.massOn W < ∞ := by
    rintro X ⟨M, θ, ξ, hM, -, hX⟩ W ⟨hWo, hWc, hWU⟩
    rw [Submission.fiw_im_mass_formula P n U hU X M θ ξ hM hX W hWo]
    exact (lintegral_mono_set (inter_subset_inter_right M subset_closure)).trans_lt
      (hM.integrableOn _ hWc hWU).setLIntegral_lt_top
  -- The family `T r` (`T₂` if `r = 1`, else `T₁`) and coefficients `c r`, zero for `r ≥ 2`.
  obtain ⟨T, hT0, hT1, hT⟩ : ∃ T : ℕ → GeometricCurrentOn U n,
      T 0 = T₁ ∧ T 1 = T₂ ∧ ∀ r, IsIntegerMultiplicity (T r) :=
    ⟨fun r => if r = 1 then T₂ else T₁, rfl, rfl, fun r => by
      show IsIntegerMultiplicity (if r = 1 then T₂ else T₁)
      split_ifs <;> assumption⟩
  obtain ⟨c, hc0, hc1, hc⟩ : ∃ c : ℕ → ℤ,
      c 0 = a ∧ c 1 = b ∧ ∀ r ∉ ({0, 1} : Finset ℕ), c r = 0 :=
    ⟨fun r => if r = 0 then a else if r = 1 then b else 0, rfl, rfl, fun r hr => by
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
      show (if r = 0 then a else if r = 1 then b else 0) = 0
      rw [ite_eq_right hr.1, ite_eq_right hr.2]⟩
  -- `∑' r, |c r| M_W(T r) = |a| M_W(T₁) + |b| M_W(T₂) < ∞`, so `fiw_im_series` applies.
  obtain ⟨S', hS', -, hS'im⟩ := Submission.fiw_im_series P n U hU T c hT fun W hW => by
    have h0 : ∀ r ∉ ({0, 1} : Finset ℕ), ((c r).natAbs : ℝ≥0∞) * (T r).massOn W = 0 :=
      fun r hr => by rw [hc r hr, Int.natAbs_zero, Nat.cast_zero, zero_mul]
    rw [tsum_eq_sum h0, Finset.sum_pair (zero_ne_one : (0 : ℕ) ≠ 1), hT0, hT1, hc0, hc1]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hfin T₁ h₁ W hW),
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hfin T₂ h₂ W hW)⟩
  -- The series has finite support, so `S'(ω) = a T₁(ω) + b T₂(ω) = S(ω)` and `S' = S`.
  have hS'S : S' = S := GeometricCurrentOn.ext fun ω => by
    have h0 : ∀ r ∉ ({0, 1} : Finset ℕ), (c r : ℝ) * T r ω = 0 :=
      fun r hr => by rw [hc r hr, Int.cast_zero, zero_mul]
    have h : HasSum (fun r => (c r : ℝ) * T r ω) (∑ r ∈ ({0, 1} : Finset ℕ), (c r : ℝ) * T r ω) :=
      hasSum_sum_of_ne_finset_zero h0
    rw [Finset.sum_pair (zero_ne_one : (0 : ℕ) ≠ 1), hT0, hT1, hc0, hc1, ← hS ω] at h
    exact (hS' ω).unique h
  exact hS'S ▸ hS'im

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

/-- **`L¹` norm by duality with smooth test functions** (proof of the translation estimate,
Step 4).  If `w : ℝⁿ → ℝ` is integrable and `∫ w g ≤ C` for every `C^∞` compactly supported `g`
with `|g| ≤ 1`, then `∫ |w| ≤ C`.  Given `ε > 0`, inner regularity of the finite measure `|w| dx`
gives disjoint compact sets `K₁, K₂`, approximating `{w > 0}` and `{w < 0}`, such that
`∫ |w| < ∫ w g + ε` for every measurable `g` with `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`.
Smooth Urysohn functions on disjoint thickenings of `K₁, K₂` give such a `g ∈ C_c^∞`, so
`∫ |w| < C + ε`. -/
theorem Submission.fiw_tb_te_l1_le_of_smooth_dual : ∀ (n : ℕ) (w : Eucl n → ℝ) (C : ℝ), Integrable w → (∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → (∀ x, |g x| ≤ 1) → ∫ x, w x * g x ≤ C) → ∫ x, |w x| ≤ C := by
  intro n w C hw H
  -- Step 8: it suffices that `∫ |w| < C + ε` for every `ε > 0`.
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- Steps 1, 2, 6, 7: compact `K₁, K₂` on which a `±1`-valued `g` nearly attains `∫ |w|`.
  obtain ⟨K₁, K₂, hK₁, hK₂, hd, hB⟩ := Submission.fiw_tb_te_l1d_compact_sign_approx n w hw ε hε
  -- Steps 3–5: a `C^∞` compactly supported `g` with `|g| ≤ 1`, `g = 1` on `K₁`, `g = -1` on `K₂`.
  obtain ⟨g, hg, hgc, hg1, hgK₁, hgK₂⟩ :=
    Submission.fiw_tb_te_l1d_smooth_sign_sep n K₁ K₂ hK₁ hK₂ hd
  -- `g` is continuous, hence a.e.-strongly measurable: `∫ |w| < ∫ w g + ε ≤ C + ε`.
  have h1 := hB g hg.continuous.aestronglyMeasurable hg1 hgK₁ hgK₂
  have h2 := H g hg hgc hg1
  linarith

/-- Translation estimate (Simon Ch. 6, proof of 7.2, used for the summed form of 5.1 (32)): if the
top-dimensional current `X ∈ 𝒟ₙ(ℝⁿ)` is `X(ω) = ∫ u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` with `u ∈ L¹`, then
`∫ |u(x + h) − u(x)| dx ≤ |h| M(∂X)` for every `h ∈ ℝⁿ`. -/
theorem Submission.fiw_tb_translation_estimate :
    ∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1))
      (u : Eucl (m + 1) → ℝ), Integrable u →
      (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x *
        (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))) →
      ∀ h : Eucl (m + 1),
        ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * X.boundary.mass := by
  intro m X u hu hX h
  -- Trivial cases: `h = 0` (the left side vanishes) and `M(∂X) = ∞` (the right side is `∞`).
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  by_cases hM : X.boundary.mass = ∞
  · rw [hM, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpos).ne']
    exact le_top
  -- For `φ ∈ C_c^∞` with `|φ| ≤ 1`, the directional form `ω` has `dω(e) = Dφ(h)` and
  -- `|ω| ≤ ‖h‖`, so `|∫ u Dφ(h)| = |X(dω)| = |∂X(ω)| ≤ ‖h‖ M(∂X)`.
  have hdiv : ∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      HasCompactSupport φ → (∀ x, |φ x| ≤ 1) →
        |∫ x, u x * fderiv ℝ φ x h| ≤ ‖h‖ * X.boundary.mass.toReal := by
    intro φ hφ hφc hφ1
    obtain ⟨ω, hω, hdω⟩ := Submission.fiw_tb_te_directional_form m φ h hφ hφc
    have hval : X.boundary ω = ∫ x, u x * fderiv ℝ φ x h := by
      rw [GeometricCurrentOn.boundary_apply, hX]
      exact integral_congr_ae (ae_of_all _ fun x => congrArg (u x * ·) (hdω x))
    rw [← hval]
    refine Submission.fiw_tb_te_abs_apply_le_mul_mass (m + 1) m univ X.boundary ω ‖h‖ hpos
      (fun x => ?_) hM
    calc covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x)
        ≤ ‖h‖ * |φ x| := hω x
      _ ≤ ‖h‖ * 1 := by gcongr; exact hφ1 x
      _ = ‖h‖ := mul_one _
  -- Weak estimate `|∫ (u(· + h) − u) g| ≤ ‖h‖ M(∂X)`, then `L¹` duality.
  have hweak := Submission.fiw_tb_te_translation_dual (m + 1) u h _ hu hdiv
  have hw : Integrable (fun x => u (x + h) - u x) := (hu.comp_add_right h).sub hu
  have hL1 : ∫ x, |u (x + h) - u x| ≤ ‖h‖ * X.boundary.mass.toReal :=
    Submission.fiw_tb_te_l1_le_of_smooth_dual (m + 1) (fun x => u (x + h) - u x) _ hw
      fun g hg hgc hg1 => (le_abs_self _).trans (hweak g hg hgc hg1)
  calc ∫⁻ x, ENNReal.ofReal |u (x + h) - u x|
      = ENNReal.ofReal (∫ x, |u (x + h) - u x|) :=
        (ofReal_integral_eq_lintegral_ofReal hw.abs (ae_of_all _ fun x => abs_nonneg _)).symm
    _ ≤ ENNReal.ofReal (‖h‖ * X.boundary.mass.toReal) := ENNReal.ofReal_le_ofReal hL1
    _ = ENNReal.ofReal ‖h‖ * X.boundary.mass := by
      rw [ENNReal.ofReal_mul (norm_nonneg h), ENNReal.ofReal_toReal hM]

/-- **Top-dimensional approximation by a lattice chain (Simon Ch. 6, proof of 5.1, (27)–(37) with
`Q := X`, `R := 0`).**  An integer multiplicity `X ∈ 𝒟ₙ(ℝⁿ)` (`n = m + 1`) with `M(X), M(∂X) < ∞`
has an integer `L¹` density `u`: `X(ω) = ∫ u ω(e)`, `∫ |u| = M(X)` and `u = 0` a.e. off `spt X`.
Integer medians `β_F` of `u` on the cubes `F ∈ 𝓛ₙ(ρ)` give the lattice chain `Pc = ∑ β_F [[F]]`,
integer multiplicity with density `v = β_F` on `F`.  `S = X − Pc` is integer multiplicity (LC) and
`M(S) ≤ ∫ |u − v| = ∑_F ∫_F |u − β_F| ≤ ∑_F ρ⁻ⁿ ∫_F ∫_F |u(x) − u(y)| ≤ c ρ M(∂X)` by the
translation estimate `∫ |u(· + h) − u| ≤ ‖h‖ M(∂X)`.  A cube with `β_F ≠ 0` meets `{u ≠ 0}` in
positive measure, hence meets `spt X`, and has diameter `√n ρ`. -/
theorem Submission.fiw_tb_top_dim_approx : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) → ∀ m : ℕ, ∃ c : ℝ≥0, ∀ X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ → ∃ (β : LatticeFaceIndex (m + 1) (m + 1) → ℝ) (Pc S : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsLatticeChain ρ β Pc ∧ (∀ F, ∃ k : ℤ, β F = k) ∧ (∀ F, β F ≠ 0 → latticeFace ρ F ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) X.support) ∧ (∀ F, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ 2 * X.mass) ∧ IsIntegerMultiplicity S ∧ (∀ ω, X ω - Pc ω = S ω) ∧ S.mass ≤ c * ENNReal.ofReal ρ * X.boundary.mass := by
  intro hMF hLC m
  -- `c` is the constant of the summed cube Poincaré inequality.
  obtain ⟨c, hc⟩ := Submission.fiw_tb_tda_poincare_sum m
  refine ⟨c, fun X hX hXm hXb ρ hρ => ?_⟩
  -- The integer `L¹` density `u` of `X`; its hypothesis is MF with `U = W = univ` together with
  -- `Hⁿ(M ∖ spt X) = 0` (support_null).
  obtain ⟨u, hum, huZ, huint, humass, husupp, hXu⟩ :=
    Submission.fiw_tb_tda_density m X hX hXm fun M θ ξ hM hXM => by
      refine ⟨?_, Submission.fiw_tb_rectifiable_support_null hMF (m + 1) (m + 1) univ isOpen_univ
        X M θ ξ hM hXM⟩
      have h := hMF (m + 1) (m + 1) univ isOpen_univ X M θ ξ hM hXM univ isOpen_univ
      rwa [inter_univ] at h
  -- The cubes `F ∈ 𝓛ₙ(ρ)` are measurable, of volume `ρⁿ` and diameter `√n ρ`, and `∫⁻` splits
  -- over them.
  obtain ⟨-, -, hFmeas, hFvol, hFdiam, -, hFsum, -⟩ := Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  -- Integer medians `b F` of `u` on the cubes, with (M1), (M2) and (M4).
  choose b hb1 hb2 hb3 using fun F : LatticeFaceIndex (m + 1) (m + 1) =>
    Submission.fiw_tb_tda_integer_median volume (latticeFace ρ F) (ρ ^ (m + 1)) u (hFmeas F)
      (pow_pos hρ _) (hFvol F) hum huZ huint.integrableOn
  -- (M1): `|b F| ρⁿ ≤ 2 ∫_F |u| ≤ 2 M(X)`; summed over the cubes, `≤ 2 M(X) < ∞`.
  have hcoef : ∀ F, ENNReal.ofReal (|(b F : ℝ)| * ρ ^ (m + 1)) ≤ 2 * X.mass := fun F =>
    (hb1 F).trans (by rw [← humass]; exact mul_le_mul_right (setLIntegral_le_lintegral _ _) 2)
  have hsum : (∑' F, ENNReal.ofReal (|(b F : ℝ)| * ρ ^ (m + 1))) < ∞ :=
    calc (∑' F, ENNReal.ofReal (|(b F : ℝ)| * ρ ^ (m + 1)))
        ≤ ∑' F, 2 * ∫⁻ x in latticeFace ρ F, ENNReal.ofReal |u x| := ENNReal.tsum_le_tsum hb1
      _ = 2 * X.mass := by
        rw [ENNReal.tsum_mul_left, ← hFsum fun x => ENNReal.ofReal |u x|, humass]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofNat_ne_top.lt_top hXm
  -- The lattice chain `Pc = ∑ b F [[F]]`: integer multiplicity, with density `v = b F` a.e. on `F`.
  obtain ⟨Pc, v, hPc, hPcim, hvint, hvF, hPcv⟩ :=
    Submission.fiw_tb_tda_lattice_chain m ρ hρ (fun F => (b F : ℝ)) (fun F => ⟨b F, rfl⟩) hsum
  -- `S = X − Pc` with `M(S) ≤ ∫ |u − v|`; `S` is integer multiplicity by LC (`a = 1`, `b = −1`).
  obtain ⟨S, hS, hSmass⟩ := Submission.fiw_tb_tda_sub_mass m X Pc u v huint hvint hXu hPcv
  have hSim : IsIntegerMultiplicity S :=
    hLC (m + 1) (m + 1) univ isOpen_univ X Pc S 1 (-1) hX hPcim fun ω => by
      rw [← hS ω]; push_cast; ring
  refine ⟨fun F => (b F : ℝ), Pc, S, hPc, fun F => ⟨b F, rfl⟩, fun F hF => ?_, hcoef, hSim, hS, ?_⟩
  · -- (M2): `F ∩ {u ≠ 0}` is not null and `u = 0` a.e. off `spt X`, so `F` meets `spt X`, and
    -- every point of `F` lies within `diam F = √n ρ` of that point.
    obtain ⟨p, hpF, hpX⟩ : (latticeFace ρ F ∩ X.support).Nonempty := by
      by_contra hne
      refine hb2 F (Int.cast_ne_zero.1 hF) (measure_mono_null (fun x hx => ?_) (ae_iff.1 husupp))
      exact fun h => hx.2 (h fun hxX => hne ⟨x, hx.1, hxX⟩)
    exact fun x hx => mem_cthickening_of_dist_le x p _ _ hpX (hFdiam F x hx p hpF)
  · -- (M4) on every cube, summed, then the summed Poincaré inequality fed by the translation
    -- estimate `∫ |u(· + h) − u| ≤ ‖h‖ M(∂X)`.
    calc S.mass ≤ ∫⁻ x, ENNReal.ofReal |u x - v x| := hSmass
      _ = ∑' F, ∫⁻ x in latticeFace ρ F, ENNReal.ofReal |u x - v x| := hFsum _
      _ = ∑' F, ∫⁻ x in latticeFace ρ F, ENNReal.ofReal |u x - b F| := by
        refine tsum_congr fun F => lintegral_congr_ae ?_
        filter_upwards [hvF F] with x hx
        rw [hx]
      _ ≤ ∑' F, ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| :=
        ENNReal.tsum_le_tsum hb3
      _ ≤ c * ENNReal.ofReal ρ * X.boundary.mass :=
        hc ρ hρ u _ hum (Submission.fiw_tb_translation_estimate m X u huint hXu)

/-- Simon Ch. 6, proof of 7.2 (p. 171, (1)–(3)): for `K ⊆ U` compact there is `C` such that for
every `B < ∞` and `ρ > 0` finitely many `Q ∈ 𝒟_{m+1}(U)` have the property that every `T` with
`T`, `∂T` integer multiplicity, `spt T ⊆ K` and `M(T) + M(∂T) ≤ B` is `T − Q = ∂R + S` with
`R`, `S` integer multiplicity and `M(R) + M(S) ≤ C ρ B`.  If `P < m + 1` then `T = 0`; otherwise
the centres `Q` are restrictions to `U` of lattice chains, from the Deformation Theorem
(`P ≥ m + 2`) or `fiw_tb_top_dim_approx` (`P = m + 1`), whose integer coefficients range over a
finite set (`fiw_tb_lattice_coeff_finite`). -/
theorem Submission.fiw_tb_finite_net :
    DeformationTheorem →
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n)
      (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) →
      ∀ W : Set (Eucl P), IsOpen W →
        T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) →
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ),
      IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ →
      (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) →
    ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P)), IsCompact K → K ⊆ U →
    ∃ C : ℝ≥0, ∀ (B : ℝ≥0∞), B ≠ ∞ → ∀ ρ : ℝ, 0 < ρ →
      ∃ Qs : Set (GeometricCurrentOn U (m + 1)), Qs.Finite ∧
      ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
        IsIntegerMultiplicity T.boundary → T.support ⊆ K → T.mass + T.boundary.mass ≤ B →
        ∃ Q ∈ Qs, ∃ (R : GeometricCurrentOn U (m + 1 + 1)) (S : GeometricCurrentOn U (m + 1)),
          IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
          (∀ ω, T ω - Q ω = R.boundary ω + S ω) ∧ R.mass + S.mass ≤ C * ENNReal.ofReal ρ * B := by
  intro hDT hMF hLC P m U hU K hK hKU
  -- (Z1) The zero current is integer multiplicity: `0 = τ(∅, 1, 0)`.
  have hzero : ∀ (N k : ℕ) (V : Set (Eucl N)),
      IsIntegerMultiplicity (0 : GeometricCurrentOn V k) := by
    intro N k V
    refine ⟨∅, fun _ => 1, fun _ => 0, ⟨empty_subset V, nullMeasurableSet_empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
      fun x hx => absurd hx (notMem_empty x), fun _ _ _ => by simp, aestronglyMeasurable_const,
      by simp⟩, fun x hx => absurd hx (notMem_empty x), fun ω => ?_⟩
    simp [tauAction]
  -- (Z2) `M(0) = 0`: every admissible evaluation of `0` is `ofReal 0 = 0`.
  have hmass0 : ∀ (N k : ℕ) (V : Set (Eucl N)), (0 : GeometricCurrentOn V k).mass = 0 := by
    intro N k V
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  -- (Z3)–(Z4) A lattice chain is determined by its coefficients, so the chains with
  -- coefficients in a finite set `𝓑` form a finite set.
  have hchains : ∀ (n N : ℕ) (V : Set (Eucl N)) (ρ : ℝ) (Bs : Set (LatticeFaceIndex n N → ℝ)),
      Bs.Finite → {Pc : GeometricCurrentOn V n | ∃ β ∈ Bs, IsLatticeChain ρ β Pc}.Finite := by
    intro n N V ρ Bs hBs
    classical
    let Φ : (LatticeFaceIndex n N → ℝ) → GeometricCurrentOn V n := fun β =>
      if h : ∃ Pc : GeometricCurrentOn V n, IsLatticeChain ρ β Pc then h.choose else 0
    refine (hBs.image Φ).subset ?_
    rintro Pc ⟨β, hβ, hPc⟩
    have h : ∃ Pc : GeometricCurrentOn V n, IsLatticeChain ρ β Pc := ⟨Pc, hPc⟩
    refine ⟨β, hβ, GeometricCurrentOn.ext fun ω => ?_⟩
    simp only [Φ, dite_eq_left h]
    rw [h.choose_spec ω, hPc ω]
  -- (Z5) It suffices to find the centres for currents on `ℝ^P`: extend `T` to `X` on `ℝ^P`
  -- (`fiw_tb_extend_to_univ`) and restrict `Q`, `R`, `S` to `U`
  -- (`fiw_tb_restrictDomain_mass_im`); `T(ω) = X(ιω)` and `∂(Y|_U)(ω) = ∂Y(ιω)`.
  have htransfer : ∀ C : ℝ≥0, (∀ (B : ℝ≥0∞), B ≠ ∞ → ∀ ρ : ℝ, 0 < ρ →
      ∃ Qs : Set (GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), Qs.Finite ∧
      ∀ X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), IsIntegerMultiplicity X →
        IsIntegerMultiplicity X.boundary → X.support ⊆ K → X.mass + X.boundary.mass ≤ B →
        ∃ Q ∈ Qs, ∃ (R : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1 + 1))
          (S : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
          IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
          (∀ ω, X ω - Q ω = R.boundary ω + S ω) ∧ R.mass + S.mass ≤ C * ENNReal.ofReal ρ * B) →
      ∀ (B : ℝ≥0∞), B ≠ ∞ → ∀ ρ : ℝ, 0 < ρ →
      ∃ Qs : Set (GeometricCurrentOn U (m + 1)), Qs.Finite ∧
      ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
        IsIntegerMultiplicity T.boundary → T.support ⊆ K → T.mass + T.boundary.mass ≤ B →
        ∃ Q ∈ Qs, ∃ (R : GeometricCurrentOn U (m + 1 + 1)) (S : GeometricCurrentOn U (m + 1)),
          IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
          (∀ ω, T ω - Q ω = R.boundary ω + S ω) ∧ R.mass + S.mass ≤ C * ENNReal.ofReal ρ * B := by
    intro C hnet B hB ρ hρ
    obtain ⟨Qs, hQs, hXnet⟩ := hnet B hB ρ hρ
    refine ⟨(fun Q => Q.restrictDomain (subset_univ U)) '' Qs, hQs.image _, ?_⟩
    intro T hT hdT hspt hmass
    have hTm : T.mass ≠ ∞ := ne_top_of_le_ne_top hB (le_self_add.trans hmass)
    obtain ⟨X, hXT, hXspt, hXm, hXdm, hXim, hXdim⟩ :=
      Submission.fiw_tb_extend_to_univ hMF P m U K hU hK hKU T hspt hTm
    obtain ⟨Q, hQ, R, S, hR, hS, hEq, hRS⟩ :=
      hXnet X (hXim hT) (hXdim hdT) hXspt ((add_le_add hXm hXdm).trans hmass)
    have hRU := Submission.fiw_tb_restrictDomain_mass_im P (m + 1 + 1) univ U (subset_univ U) hU R
    have hSU := Submission.fiw_tb_restrictDomain_mass_im P (m + 1) univ U (subset_univ U) hU S
    refine ⟨Q.restrictDomain (subset_univ U), ⟨Q, hQ, rfl⟩, R.restrictDomain (subset_univ U),
      S.restrictDomain (subset_univ U), hRU.2 hR, hSU.2 hS, fun ω => ?_,
      (add_le_add hRU.1 hSU.1).trans hRS⟩
    rw [← hXT]
    exact hEq (testFormOnInclusion (subset_univ U) (m + 1) ω)
  rcases lt_trichotomy P (m + 1) with hP | rfl | hP
  · -- Case `P < m + 1`: every `(m+1)`-covector on `ℝ^P` is `0`, so `T = 0`; take `C = 0`,
    -- `𝒬 = {0}` and `Q = R = S = 0`.
    refine ⟨0, fun B _ ρ _ => ⟨{0}, finite_singleton 0, fun T _ _ _ _ =>
      ⟨0, mem_singleton 0, 0, 0, hzero P (m + 1 + 1) U, hzero P (m + 1) U, fun ω => ?_, ?_⟩⟩⟩
    · have hω : ω = 0 := by
        apply Subtype.ext
        funext x
        ext v
        refine AlternatingMap.map_linearDependent
          ((ω : DifferentialForm (Eucl P) (m + 1)) x).toAlternatingMap v fun hv => ?_
        have hle := hv.fintype_card_le_finrank
        rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hle
        exact absurd hle (Nat.not_le.2 hP)
      have hT : T ω = 0 := by
        rw [hω, map_zero]
      simp [hT]
    · simp [hmass0]
  · -- Case `P = m + 1`: `fiw_tb_top_dim_approx` at scale `ρ`; `Q = Pc`, `R = 0`, `S = S̃`.
    obtain ⟨c, hc⟩ := Submission.fiw_tb_top_dim_approx hMF hLC m
    refine ⟨c, htransfer c fun B hB ρ hρ => ?_⟩
    set Y : Set (Eucl (m + 1)) := cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) K
    set A : ℝ := 2 * B.toReal / ρ ^ (m + 1) with hA
    set Bs := {β : LatticeFaceIndex (m + 1) (m + 1) → ℝ | (∀ F, ∃ k : ℤ, β F = k) ∧
      ∀ F, β F ≠ 0 → latticeFace ρ F ⊆ Y ∧ |β F| ≤ A}
    have hBsfin : Bs.Finite := Submission.fiw_tb_lattice_coeff_finite (m + 1) (m + 1) ρ hρ Y
      hK.isBounded.cthickening A
    refine ⟨{Pc | ∃ β ∈ Bs, IsLatticeChain ρ β Pc}, hchains (m + 1) (m + 1) univ ρ Bs hBsfin, ?_⟩
    intro X hX _ hspt hmass
    have hXm : X.mass ≤ B := le_self_add.trans hmass
    have hXdm : X.boundary.mass ≤ B := le_add_self.trans hmass
    obtain ⟨β, Pc, S, hPc, hβint, hβface, hβmass, hS, hEq, hSm⟩ :=
      hc X hX (hXm.trans_lt hB.lt_top) (hXdm.trans_lt hB.lt_top) ρ hρ
    -- `β ∈ 𝓑`: its faces lie in `Y`, and `|β F| ρ^{m+1} ≤ 2 M(X) ≤ 2B`.
    have hβ : β ∈ Bs := by
      refine ⟨hβint, fun F hF => ⟨(hβface F hF).trans (cthickening_subset_of_subset _ hspt), ?_⟩⟩
      have h := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB)).1
        ((hβmass F).trans (mul_le_mul_right hXm 2))
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
      rw [hA, le_div_iff₀ (pow_pos hρ _)]
      exact h
    refine ⟨Pc, ⟨β, hβ, hPc⟩, 0, S, hzero (m + 1) (m + 1 + 1) univ, hS, fun ω => ?_, ?_⟩
    · simp [hEq ω]
    · rw [hmass0, zero_add]
      exact hSm.trans (mul_le_mul_right hXdm _)
  · -- Case `P ≥ m + 2`: the Deformation Theorem at scale `ρ` in `ℝ^{(m+1)+ℓ}`; `Q = Pc`,
    -- `R = R̃`, `S = S̃`, and `fiw_tb_lattice_chain_coeff` puts the coefficients `β` in `𝓑`.
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, P = m + 1 + ℓ := ⟨P - (m + 1), by omega⟩
    obtain ⟨C, hC⟩ := hDT m ℓ (by omega)
    refine ⟨C, htransfer C fun B hB ρ hρ => ?_⟩
    set Y : Set (Eucl (m + 1 + ℓ)) :=
      cthickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) K
    set A : ℝ := C * B.toReal / ρ ^ (m + 1) with hA
    set Bs := {β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ | (∀ F, ∃ k : ℤ, β F = k) ∧
      ∀ F, β F ≠ 0 → latticeFace ρ F ⊆ Y ∧ |β F| ≤ A}
    have hBsfin : Bs.Finite := Submission.fiw_tb_lattice_coeff_finite (m + 1) (m + 1 + ℓ) ρ hρ
      Y hK.isBounded.cthickening A
    refine ⟨{Pc | ∃ β ∈ Bs, IsLatticeChain ρ β Pc},
      hchains (m + 1) (m + 1 + ℓ) univ ρ Bs hBsfin, ?_⟩
    intro X hX hdX hspt hmass
    have hXm : X.mass ≤ B := le_self_add.trans hmass
    obtain ⟨Pc, β, R, S, hPc, hEq, hPcm, -, hRm, hSm, hsptPR, -, hIM, hSim⟩ :=
      hC X (hmass.trans_lt hB.lt_top) ρ hρ
    obtain ⟨hβint, -, hRim⟩ := hIM hX
    -- `β ∈ 𝓑`: `F ⊆ spt Pc ⊆ Y` and `|β F| ρ^{m+1} ≤ M(Pc) ≤ C M(X) ≤ C B`.
    have hβ : β ∈ Bs := by
      refine ⟨hβint, fun F hF => ?_⟩
      obtain ⟨hFspt, hFmass⟩ :=
        Submission.fiw_tb_lattice_chain_coeff m (m + 1 + ℓ) ρ β Pc hρ hPc F hF
      refine ⟨fun x hx => thickening_subset_cthickening _ _
        (thickening_subset_of_subset _ hspt (hsptPR (mem_union_left _ (hFspt hx)))), ?_⟩
      have h := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hB)).1
        (hFmass.trans (hPcm.trans (mul_le_mul_right hXm _)))
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at h
      rw [hA, le_div_iff₀ (pow_pos hρ _)]
      exact h
    refine ⟨Pc, ⟨β, hβ, hPc⟩, R, S, hRim, hSim hX hdX, hEq, ?_⟩
    calc R.mass + S.mass
        ≤ C * ENNReal.ofReal ρ * X.mass + C * ENNReal.ofReal ρ * X.boundary.mass :=
          add_le_add hRm hSm
      _ = C * ENNReal.ofReal ρ * (X.mass + X.boundary.mass) := (mul_add _ _ _).symm
      _ ≤ C * ENNReal.ofReal ρ * B := mul_le_mul_right hmass _

end GMT.Ch06
