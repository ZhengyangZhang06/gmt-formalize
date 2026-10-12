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
/-- Fubini and the fundamental theorem of calculus on the cube `[0,ρ]^{n+1}`: for `φ` of class
`C¹` and `e_i = Pi.single i 1`,
`∫_{[0,ρ]^{n+1}} Dφ(s)(e_i) ds = ∫_{[0,ρ]^n} (φ(insertNth_i(ρ, s')) - φ(insertNth_i(0, s'))) ds'`.
The measure-preserving map `(t, s') ↦ insertNth_i(t, s')` pulls the cube back to
`[0,ρ] × [0,ρ]^n`, Fubini puts the `t`-integral inside, and
`d/dt φ(insertNth_i(t, s')) = Dφ(insertNth_i(t, s'))(e_i)`. -/
theorem Submission.br_cube_integral_fderiv_eq_faces :
    ∀ (n : ℕ) (ρ : ℝ), 0 ≤ ρ → ∀ (φ : (Fin (n + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      ∀ (i : Fin (n + 1)),
        ∫ s in Set.Icc (0 : Fin (n + 1) → ℝ) (fun _ => ρ), fderiv ℝ φ s (Pi.single i 1) =
          ∫ s in Set.Icc (0 : Fin n → ℝ) (fun _ => ρ),
            (φ (Fin.insertNth i ρ s) - φ (Fin.insertNth i 0 s)) := by
  intro n ρ hρ φ hφ i
  -- `g(s) = Dφ(s)(e_i)` is continuous.
  have hg : Continuous fun s => fderiv ℝ φ s (Pi.single i 1) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- `(t, s') ↦ insertNth_i(t, s')` is measure preserving and pulls `[0,ρ]^{n+1}` back to
  -- `[0,ρ] × [0,ρ]^n` (as in Mathlib's `torusIntegral_succAbove`).
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have heI : (e ⁻¹' Set.Icc 0 fun _ => ρ) =
      Set.Icc 0 ρ ×ˢ Set.Icc (0 : Fin n → ℝ) fun _ => ρ :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) i).preimage_Icc _ _).trans (Set.Icc_prod_eq _ _)
  have hint : Integrable (fun z => fderiv ℝ φ (e z) (Pi.single i 1))
      ((volume.restrict (Set.Icc (0 : ℝ) ρ)).prod
        (volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => ρ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hg.comp (continuous_fst.finInsertNth i continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← hem.map_eq, setIntegral_map_equiv, heI, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ hint]
  -- Fundamental theorem of calculus in the `i`-th coordinate, for each `s'`.
  congr 1
  funext y
  have hcurve : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (Fin.insertNth i t y : Fin (n + 1) → ℝ)) (Pi.single i 1) t := by
    intro t
    refine hasDerivAt_pi.2 fun j => ?_
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
      exact hasDerivAt_id' t
    · simp only [Fin.insertNth_apply_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne _ k)]
      exact hasDerivAt_const t (y k)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (Fin.insertNth i t y))
      (fderiv ℝ φ (Fin.insertNth i t y) (Pi.single i 1)) t := fun t =>
    ((hφ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hcurve t)
  have hcont : Continuous fun t : ℝ => fderiv ℝ φ (Fin.insertNth i t y) (Pi.single i 1) :=
    hg.comp (continuous_iff_continuousAt.2 fun t => (hcurve t).continuousAt)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hρ]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 ρ)

/-- Stokes' theorem on the parameter cube of the lattice face `ρ (z + F_α)`, `F = (z, α)`.  Put
`p = ρ z`, `v_j = e_{α j}`, `A(s) = p + ∑_j s_j v_j` and `α_i = α ∘ succAbove_i`; then
`∫_{[0,ρ]^{m+1}} dω(A(s))(v) ds` is the alternating sum over `i` of the integrals of `ω(·)(e_{α_i})`
over the faces `s_i = ρ` and `s_i = 0`, i.e. of
`∫_{[0,ρ]^m} ω(ρ (z + e_{α i}) + ∑_k s_k e_{α_i k})(e_{α_i})` minus
`∫_{[0,ρ]^m} ω(p + ∑_k s_k e_{α_i k})(e_{α_i})`.
By `exteriorDerivative_apply` and the chain rule, `dω(A(s))(v) = ∑_i (-1)^i Dφ_i(s)(e_i)` for
`φ_i(s) = ω(A(s))(removeNth_i v)`; `br_cube_integral_fderiv_eq_faces` integrates each term, and
`A(insertNth_i(t, s')) = p + t v_i + ∑_k s'_k e_{α_i k}` identifies the two faces. -/
theorem Submission.br_cube_stokes_lattice :
    ∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (F : LatticeFaceIndex (m + 1) P)
      (ω : DifferentialForm (Eucl P) m), IsSmoothForm ω →
      ∫ s in Set.Icc (0 : Fin (m + 1) → ℝ) (fun _ => ρ),
        exteriorDerivative ω (∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
          ∑ j, s j • EuclideanSpace.single (F.2 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) =
      ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
        ((∫ s in Set.Icc (0 : Fin m → ℝ) (fun _ => ρ),
          ω (∑ l, (ρ * (((F.1 + Pi.single (F.2 i) 1 : Fin P → ℤ) l : ℤ) : ℝ)) •
              EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j) (1 : ℝ))
            (fun j => EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j) (1 : ℝ))) -
        ∫ s in Set.Icc (0 : Fin m → ℝ) (fun _ => ρ),
          ω (∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j) (1 : ℝ))
            (fun j => EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j)
              (1 : ℝ))) := by
  intro P m ρ hρ F ω hω
  -- The base point `p = ρ z`, the frame `v j = e_{α j}` and `A s = p + ∑ j, s j • v j`.
  set p : Eucl P := ∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) with hp
  set v : Fin (m + 1) → Eucl P := fun j => EuclideanSpace.single (F.2 j) (1 : ℝ) with hv
  have hωd : Differentiable ℝ ω := hω.differentiable (by simp)
  -- `A` is affine with linear part `DA s = ∑ j, s j • v j`.
  let DA : (Fin (m + 1) → ℝ) →L[ℝ] Eucl P := ∑ j, (ContinuousLinearMap.proj j).smulRight (v j)
  have hDA : ∀ s, DA s = ∑ j, s j • v j := fun s => by simp [DA]
  have hAeq : (fun s : Fin (m + 1) → ℝ => p + ∑ j, s j • v j) = fun s => p + DA s := by
    funext s; rw [hDA]
  have hA : ∀ s, HasFDerivAt (fun s : Fin (m + 1) → ℝ => p + ∑ j, s j • v j) DA s := fun s => by
    rw [hAeq]
    exact DA.hasFDerivAt.const_add p
  -- `φ i s = ω (A s) (removeNth i v)` is `C¹`: evaluation at a fixed frame is continuous linear.
  set φ : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ :=
    fun i s => ω (p + ∑ j, s j • v j) (Fin.removeNth i v)
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := by
    intro i
    have h1 : ContDiff ℝ 1 (fun y => ω y (Fin.removeNth i v)) :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (Fin.removeNth i v)).contDiff.comp
        (hω.of_le (by simp))
    have h2 : ContDiff ℝ 1 (fun s : Fin (m + 1) → ℝ => p + ∑ j, s j • v j) := by
      rw [hAeq]
      exact contDiff_const.add DA.contDiff
    exact h1.comp h2
  -- Pointwise `dω(A s)(v) = ∑ i, (-1)^i Dφ_i(s)(e_i)`, by the chain rule and `DA e_i = v i`.
  have hpt : ∀ s : Fin (m + 1) → ℝ, exteriorDerivative ω (p + ∑ j, s j • v j) v =
      ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (φ i) s (Pi.single i 1) := by
    intro s
    rw [exteriorDerivative_apply (hωd _) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : HasFDerivAt (fun y => ω y (Fin.removeNth i v))
        (fderiv ℝ (fun y => ω y (Fin.removeNth i v)) (p + ∑ j, s j • v j))
        (p + ∑ j, s j • v j) :=
      ((hωd _).continuousAlternatingMap_apply_const _).hasFDerivAt
    have hφi : φ i = (fun y => ω y (Fin.removeNth i v)) ∘ (fun s => p + ∑ j, s j • v j) := rfl
    rw [hφi, (hc.comp s (hA s)).fderiv, ContinuousLinearMap.comp_apply, hDA]
    have hsum : ∑ j, (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ) j • v j = v i := by
      simp [Pi.single_apply]
    rw [hsum, zsmul_eq_mul]
    push_cast
    ring
  -- Integrate the finite sum of continuous functions over the cube term by term.
  have hcont : ∀ i, Continuous fun s => fderiv ℝ (φ i) s (Pi.single i 1) :=
    fun i => ((hφ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ i : Fin (m + 1), IntegrableOn
      (fun s => (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (φ i) s (Pi.single i 1))
      (Set.Icc (0 : Fin (m + 1) → ℝ) (fun _ => ρ)) :=
    fun i => (continuous_const.mul (hcont i)).continuousOn.integrableOn_compact isCompact_Icc
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ => hpt s),
    integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Fubini and the fundamental theorem of calculus in the `i`-th coordinate.
  rw [integral_const_mul, Submission.br_cube_integral_fderiv_eq_faces m ρ hρ.le (φ i) (hφ i) i]
  congr 1
  have hcI : ∀ c : ℝ, IntegrableOn (fun s' : Fin m → ℝ => φ i (Fin.insertNth i c s'))
      (Set.Icc 0 fun _ => ρ) := fun c =>
    ((hφ i).continuous.comp (continuous_const.finInsertNth i continuous_id)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  rw [integral_sub (hcI ρ) (hcI 0)]
  -- Identify the faces `s_i = ρ` and `s_i = 0`.
  have hA_ins : ∀ (c : ℝ) (s' : Fin m → ℝ),
      p + ∑ j, Fin.insertNth (α := fun _ => ℝ) i c s' j • v j =
        (p + c • v i) + ∑ k, s' k •
          EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) k) (1 : ℝ) := by
    intro c s'
    rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same, add_assoc]
    simp only [Fin.insertNth_apply_succAbove]
    rfl
  have hrem : Fin.removeNth i v =
      fun k => EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) k) (1 : ℝ) := rfl
  have htop : ∑ l, (ρ * (((F.1 + Pi.single (F.2 i) 1 : Fin P → ℤ) l : ℤ) : ℝ)) •
      EuclideanSpace.single l (1 : ℝ) = p + ρ • v i := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, add_smul, Finset.sum_add_distrib, hp, hv]
    congr 1
    rw [Finset.sum_eq_single (F.2 i)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  congr 1
  · refine setIntegral_congr_fun measurableSet_Icc fun s' _ => ?_
    simp only [φ, hA_ins, htop, hrem]
  · refine setIntegral_congr_fun measurableSet_Icc fun s' _ => ?_
    simp only [φ, hA_ins, hrem, zero_smul, add_zero]

/-- Stokes' theorem on a lattice face (Simon Ch. 6, §5 and the proof of 6.3): for
`F = (z, α) ∈ 𝓛ₘ₊₁(ρ)` and a smooth `m`-form `ω`,
`[[F]](dω) = ∑ᵢ (-1)ⁱ ([[(z + e_{α(i)}, α ∘ succAboveᵢ)]](ω) - [[(z, α ∘ succAboveᵢ)]](ω))`.
Every face integral is the integral over its parameter cube `[0, ρ]ᵈ`, and on the cube this is
Stokes' theorem (Fubini and the fundamental theorem of calculus). -/
theorem Submission.br_lattice_face_stokes :
    ∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (F : LatticeFaceIndex (m + 1) P)
      (ω : DifferentialForm (Eucl P) m), IsSmoothForm ω →
      latticeFaceAction ρ F (exteriorDerivative ω) =
        ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
          (latticeFaceAction ρ (F.1 + Pi.single (F.2 i) 1, (Fin.succAboveOrderEmb i).trans F.2) ω -
            latticeFaceAction ρ (F.1, (Fin.succAboveOrderEmb i).trans F.2) ω) := by
  intro P m ρ hρ F ω hω
  -- Both sides become integrals over parameter cubes: `[0, ρ]ᵐ⁺¹` for `F` and `[0, ρ]ᵐ` for
  -- the two faces opposite in direction `α(i)`.
  simp only [latticeFaceAction, Submission.br_latticeFace_setIntegral_eq_cube]
  exact Submission.br_cube_stokes_lattice P m ρ hρ F ω hω

/-- Boundaries of integer lattice chains are integer multiplicity (Simon Ch. 6, §5 and the
proof of 6.3).  If `Pc = ∑_F β_F [[F]]` with `β_F ∈ ℤ`, Stokes on each face
(`Submission.br_lattice_face_stokes`) and regrouping by `m`-faces give
`∂Pc = ∑_G γ_G [[G]]` with `γ_G ∈ ℤ`; only finitely many faces meet the support of a test
form, so all sums are finite.  An integer lattice chain `∑_G γ_G [[G]]` is `τ(M, θ, ξ)` with
`M` the union of the relative interiors `G°` with `γ_G ≠ 0`, `θ = |γ_G|` and
`ξ = sign(γ_G) e_{γ'(0)} ∧ ⋯ ∧ e_{γ'(m-1)}` on `G°`: relative interiors of distinct faces are
disjoint, relative boundaries are `Hᵐ`-null, and near a point of `G°` the set `M` is the
affine plane of `G` with constant multiplicity, which is therefore the weighted approximate
tangent space there. -/
theorem Submission.br_lattice_chain_boundary_isIntegerMultiplicity :
    ∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (β : LatticeFaceIndex (m + 1) P → ℤ)
      (Pc : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
      IsLatticeChain ρ (fun F => (β F : ℝ)) Pc → IsIntegerMultiplicity Pc.boundary := by
  -- (L3) Local finiteness: a bounded set meets only finitely many faces of each dimension.
  have faces_meeting_finite : ∀ (P d : ℕ) (ρ : ℝ), 0 < ρ → ∀ K : Set (Eucl P),
      Bornology.IsBounded K →
        {G : LatticeFaceIndex d P | (latticeFace ρ G ∩ K).Nonempty}.Finite := by
    intro P d ρ hρ K hK
    obtain ⟨R, hR⟩ := hK.subset_closedBall 0
    set N : ℤ := ⌈R / ρ⌉ + 1 with hN
    have hfin : (Set.pi univ (fun _ : Fin P => Set.Icc (-N) N) ×ˢ
        (univ : Set (SimonMultiIndex d P))).Finite :=
      (Set.Finite.pi (fun _ => Set.finite_Icc _ _)).prod Set.finite_univ
    refine hfin.subset ?_
    rintro ⟨z, α⟩ ⟨x, hxF, hxK⟩
    refine ⟨?_, mem_univ _⟩
    intro i _
    have hxi : |x i| ≤ R := by
      have h1 := hR hxK
      rw [mem_closedBall, dist_zero_right] at h1
      have h2 := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h2
      linarith
    have hxi' : |x i / ρ| ≤ R / ρ := by
      rw [abs_div, abs_of_pos hρ]
      exact div_le_div_of_nonneg_right hxi hρ.le
    have hceil : R / ρ ≤ (⌈R / ρ⌉ : ℝ) := Int.le_ceil _
    have key : (z i : ℝ) ≤ x i / ρ ∧ x i / ρ ≤ (z i : ℝ) + 1 := by
      obtain ⟨h1, h2⟩ := hxF i
      by_cases hi : i ∈ range α
      · obtain ⟨a, b⟩ := h1 hi
        constructor
        · rw [le_div_iff₀ hρ]; linarith
        · rw [div_le_iff₀ hρ]; linarith
      · have := h2 hi
        simp only at this
        rw [this, mul_div_cancel_left₀ _ hρ.ne']
        constructor <;> linarith
    obtain ⟨k1, k2⟩ := key
    have habs := abs_le.mp hxi'
    constructor
    · have : (-(N : ℝ)) ≤ (z i : ℝ) := by
        rw [hN]; push_cast; linarith
      exact_mod_cast this
    · have : (z i : ℝ) ≤ (N : ℝ) := by
        rw [hN]; push_cast; linarith
      exact_mod_cast this
  -- (L1) A point of the relative interior `G°` lies in no other face of the same dimension.
  have face_eq_of_mem_relint : ∀ (P d : ℕ) (ρ : ℝ), 0 < ρ →
      ∀ (G G' : LatticeFaceIndex d P) (x : Eucl P),
      (∀ i : Fin P, (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
        (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))) →
      x ∈ latticeFace ρ G' → G' = G := by
    intro P d ρ hρ G G' x hx hx'
    obtain ⟨w, α⟩ := G
    obtain ⟨w', α'⟩ := G'
    simp only at hx
    have hx'' : ∀ i : Fin P, (i ∈ range α' → ρ * (w' i : ℝ) ≤ x i ∧ x i ≤ ρ * ((w' i : ℝ) + 1)) ∧
        (i ∉ range α' → x i = ρ * (w' i : ℝ)) := hx'
    have noint : ∀ (a b : ℤ), ρ * (a : ℝ) < ρ * (b : ℝ) → ρ * (b : ℝ) < ρ * ((a : ℝ) + 1) →
        False := by
      intro a b h1 h2
      have h1' : (a : ℝ) < b := lt_of_mul_lt_mul_left h1 hρ.le
      have h2' : (b : ℝ) < a + 1 := lt_of_mul_lt_mul_left h2 hρ.le
      have : a < b := by exact_mod_cast h1'
      have : b < a + 1 := by exact_mod_cast h2'
      omega
    have hsub : range α ⊆ range α' := by
      intro i hi
      by_contra hi'
      obtain ⟨a, b⟩ := (hx i).1 hi
      have h2 := (hx'' i).2 hi'
      rw [h2] at a b
      exact noint _ _ a b
    have hrange : range α = range α' := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [Set.ncard_range_of_injective α.injective, Set.ncard_range_of_injective α'.injective]
    have hαα' : α' = α := (OrderEmbedding.range_inj_of_wellFoundedLT).1 hrange.symm
    subst hαα'
    have hww : w' = w := by
      funext i
      by_cases hi : i ∈ range α'
      · obtain ⟨a, b⟩ := (hx i).1 hi
        obtain ⟨c, e⟩ := (hx'' i).1 hi
        have h1 : (w i : ℝ) < w' i + 1 := by
          have : ρ * (w i : ℝ) < ρ * ((w' i : ℝ) + 1) := lt_of_lt_of_le a e
          exact lt_of_mul_lt_mul_left this hρ.le
        have h2 : (w' i : ℝ) < w i + 1 := by
          have : ρ * (w' i : ℝ) < ρ * ((w i : ℝ) + 1) := lt_of_le_of_lt c b
          exact lt_of_mul_lt_mul_left this hρ.le
        have : w i < w' i + 1 := by exact_mod_cast h1
        have : w' i < w i + 1 := by exact_mod_cast h2
        omega
      · have h1 := (hx i).2 hi
        have h2 := (hx'' i).2 hi
        rw [h1] at h2
        have := mul_left_cancel₀ hρ.ne' h2
        exact_mod_cast this.symm
    rw [hww]
  -- (L2) `Hᵈ(|G|) = ρᵈ` and the relative boundary `|G| \ G°` is `Hᵈ`-null.
  have face_measure : ∀ (P d : ℕ) (ρ : ℝ), 0 < ρ → ∀ G : LatticeFaceIndex d P,
      (μHE[d] : Measure (Eucl P)) (latticeFace ρ G) = ENNReal.ofReal (ρ ^ d) ∧
      (μHE[d] : Measure (Eucl P)) (latticeFace ρ G \ {x | ∀ i : Fin P,
        (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
        (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))}) = 0 := by
    intro P d ρ hρ G
    classical
    set e : Fin d → Eucl P := fun j => EuclideanSpace.single (G.2 j) (1:ℝ) with he_def
    have he : Orthonormal ℝ e := (EuclideanSpace.orthonormal_single).comp _ G.2.injective
    set c : Eucl P := ∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1:ℝ) with hc_def
    set A : EuclideanSpace ℝ (Fin d) → Eucl P := fun s => c + ∑ j, s j • e j with hA_def
    have hAiso : Isometry A := by
      refine Isometry.of_dist_eq fun s t => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h : A s - A t = ∑ j, (s - t) j • e j := by
        simp only [hA_def, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← sub_smul,
          PiLp.sub_apply]
      rw [h]
      have h1 : ‖∑ j, (s - t) j • e j‖ ^ 2 = ‖s - t‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, he.inner_sum, EuclideanSpace.real_norm_sq_eq]
        simp [sq]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
    have hcoord : ∀ (s : EuclideanSpace ℝ (Fin d)) (i : Fin P),
        A s i = ρ * (G.1 i : ℝ) + ∑ j, s j * (if i = G.2 j then 1 else 0) := by
      intro s i
      simp [hA_def, hc_def, he_def, Pi.single_apply]
    have hcoord1 : ∀ (s : EuclideanSpace ℝ (Fin d)) (j : Fin d),
        A s (G.2 j) = ρ * (G.1 (G.2 j) : ℝ) + s j := by
      intro s j
      rw [hcoord]
      congr 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [ite_eq_right]; · simp
        intro h; exact hb (G.2.injective h.symm)
      · simp
    have hcoord2 : ∀ (s : EuclideanSpace ℝ (Fin d)) (i : Fin P), i ∉ range G.2 →
        A s i = ρ * (G.1 i : ℝ) := by
      intro s i hi
      rw [hcoord]
      have : ∀ j, (if i = G.2 j then (1:ℝ) else 0) = 0 :=
        fun j => ite_eq_right (fun h => hi ⟨j, h.symm⟩)
      simp [this]
    -- preimage point
    have hpre : ∀ x : Eucl P, (∀ i, i ∉ range G.2 → x i = ρ * (G.1 i : ℝ)) →
        A (WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ))) = x := by
      intro x hx
      ext i
      by_cases hi : i ∈ range G.2
      · obtain ⟨j, rfl⟩ := hi
        rw [hcoord1]
        simp
      · rw [hcoord2 _ _ hi, hx i hi]
    set box : Set (EuclideanSpace ℝ (Fin d)) := {s | ∀ j, 0 ≤ s j ∧ s j ≤ ρ} with hbox
    set obox : Set (EuclideanSpace ℝ (Fin d)) := {s | ∀ j, 0 < s j ∧ s j < ρ} with hobox
    have hface : latticeFace ρ G = A '' box := by
      ext x
      constructor
      · intro hx
        have hx' := hx
        refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), ?_,
            hpre x fun i hi => (hx i).2 hi⟩
        intro j
        obtain ⟨h1, h2⟩ := (hx' (G.2 j)).1 ⟨j, rfl⟩
        simp only
        constructor <;> nlinarith
      · rintro ⟨s, hs, rfl⟩ i
        refine ⟨?_, fun hi => hcoord2 s i hi⟩
        rintro ⟨j, rfl⟩
        rw [hcoord1]
        obtain ⟨h1, h2⟩ := hs j
        constructor <;> nlinarith
    have hrel : {x : Eucl P | ∀ i : Fin P,
        (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
        (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} = A '' obox := by
      ext x
      constructor
      · intro hx
        refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), ?_,
            hpre x fun i hi => (hx i).2 hi⟩
        intro j
        obtain ⟨h1, h2⟩ := (hx (G.2 j)).1 ⟨j, rfl⟩
        simp only
        constructor <;> nlinarith
      · rintro ⟨s, hs, rfl⟩ i
        refine ⟨?_, fun hi => hcoord2 s i hi⟩
        rintro ⟨j, rfl⟩
        rw [hcoord1]
        obtain ⟨h1, h2⟩ := hs j
        constructor <;> nlinarith
    -- volumes of boxes in Euclidean space
    have hbox' : box = (WithLp.ofLp) ⁻¹' (Icc (0 : Fin d → ℝ) (fun _ => ρ)) := by
      ext s; simp [hbox, Pi.le_def, forall_and]
    have hobox' : obox = (WithLp.ofLp) ⁻¹' (pi univ fun _ : Fin d => Ioo (0:ℝ) ρ) := by
      ext s; simp [hobox]
    have hvbox : (volume : Measure (EuclideanSpace ℝ (Fin d))) box = ENNReal.ofReal (ρ ^ d) := by
      rw [hbox', (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
        measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
      simp [ENNReal.ofReal_pow hρ.le]
    have hvobox : (volume : Measure (EuclideanSpace ℝ (Fin d))) obox = ENNReal.ofReal (ρ ^ d) := by
      rw [hobox', (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
      simp [ENNReal.ofReal_pow hρ.le]
    have hsub : obox ⊆ box := fun s hs j => ⟨(hs j).1.le, (hs j).2.le⟩
    have hoboxm : MeasurableSet obox := by
      rw [hobox']
      exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).preimage (by fun_prop)
    constructor
    · rw [hface, hAiso.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvbox]
    · rw [hface, hrel, ← image_sdiff hAiso.injective, hAiso.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        measure_sdiff hsub hoboxm.nullMeasurableSet (by rw [hvobox]; exact ENNReal.ofReal_ne_top),
        hvbox, hvobox, tsub_self]
  -- Blow-up computation (step 6(g)): if `M` is the affine plane `x + L` near `x` and `θ` is
  -- constant there, then `L` is the weighted approximate tangent space of `M` at `x`.
  have tangent_of_locally_affine : ∀ (P d : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P)
      (L : Submodule ℝ (Eucl P)) (δ : ℝ), 0 < δ → Module.finrank ℝ L = d →
      M ∩ ball x δ = {y | y - x ∈ L} ∩ ball x δ → (∀ y ∈ M ∩ ball x δ, θ y = θ x) →
      HasWeightedApproximateTangentSpaceAt d M θ x L := by
    intro P d M θ x L δ hδ hL hM hθ
    refine ⟨hL, fun f => ?_⟩
    obtain ⟨R0, hR0⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    set R : ℝ := max R0 0 + 1 with hRdef
    have hRpos : 0 < R := by positivity
    have hfR : ∀ y : Eucl P, R ≤ ‖y‖ → f y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hy'
      have := hR0 hy'
      rw [mem_closedBall, dist_zero_right] at this
      have : R0 < R := by rw [hRdef]; have := le_max_left R0 0; linarith
      linarith
    -- key set identity and value of θ
    have hset : ∀ r : ℝ, 0 < r → r * R ≤ δ →
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ ball 0 R =
            (L : Set (Eucl P)) ∩ ball 0 R := by
      intro r hr hrR
      ext y
      simp only [mem_inter_iff, mem_image, mem_ball, dist_zero_right, SetLike.mem_coe,
        Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        refine ⟨?_, hy⟩
        have hzx : ‖z - x‖ < δ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hy
          have : ‖z - x‖ < r * R := by
            rw [inv_mul_lt_iff₀ hr] at hy; exact hy
          linarith
        have hz' : z ∈ M ∩ ball x δ := ⟨hz, by rw [mem_ball, dist_eq_norm]; exact hzx⟩
        rw [hM] at hz'
        exact L.smul_mem _ hz'.1
      · rintro ⟨hyL, hy⟩
        refine ⟨⟨x + r • y, ?_, ?_⟩, hy⟩
        · have hmem : x + r • y ∈ {z | z - x ∈ L} ∩ ball x δ := by
            refine ⟨?_, ?_⟩
            · simp only [Set.mem_ofPred_eq, add_sub_cancel_left]; exact L.smul_mem _ hyL
            · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                abs_of_pos hr]
              calc r * ‖y‖ < r * R := by exact mul_lt_mul_of_pos_left hy hr
                _ ≤ δ := hrR
          rw [← hM] at hmem
          exact hmem.1
        · simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    have hval : ∀ r : ℝ, 0 < r → r * R ≤ δ → ∀ y ∈ (L : Set (Eucl P)) ∩ ball 0 R,
        θ (x + r • y) = θ x := by
      intro r hr hrR y hy
      apply hθ
      have hmem : x + r • y ∈ {z | z - x ∈ L} ∩ ball x δ := by
        refine ⟨?_, ?_⟩
        · simp only [Set.mem_ofPred_eq, add_sub_cancel_left]; exact L.smul_mem _ hy.1
        · have hy2 := hy.2
          rw [mem_ball, dist_zero_right] at hy2
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos hr]
          calc r * ‖y‖ < r * R := by exact mul_lt_mul_of_pos_left hy2 hr
            _ ≤ δ := hrR
      rw [← hM] at hmem
      exact hmem
    have hLmeas : MeasurableSet ((L : Set (Eucl P)) ∩ ball 0 R) :=
      (L.closed_of_finiteDimensional.measurableSet).inter measurableSet_ball
    have key : ∀ r : ℝ, 0 < r → r * R ≤ δ →
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
            f y * θ (x + r • y) ∂(μHE[d] : Measure (Eucl P)) =
          θ x * ∫ y in (L : Set (Eucl P)), f y ∂(μHE[d] : Measure (Eucl P)) := by
      intro r hr hrR
      have hind1 : (fun y => f y * θ (x + r • y)) =
          (ball (0 : Eucl P) R).indicator (fun y => f y * θ (x + r • y)) := by
        funext y
        by_cases hy : y ∈ ball (0 : Eucl P) R
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]
          rw [mem_ball, dist_zero_right, not_lt] at hy
          rw [hfR y hy, zero_mul]
      have hind2 : (fun y => f y) = (ball (0 : Eucl P) R).indicator (fun y => f y) := by
        funext y
        by_cases hy : y ∈ ball (0 : Eucl P) R
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]
          rw [mem_ball, dist_zero_right, not_lt] at hy
          rw [hfR y hy]
      calc ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
            f y * θ (x + r • y) ∂(μHE[d] : Measure (Eucl P))
          = ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
              (ball (0 : Eucl P) R).indicator (fun y => f y * θ (x + r • y)) y
                ∂(μHE[d] : Measure (Eucl P)) := by
            rw [← hind1]
        _ = ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ ball 0 R,
              f y * θ (x + r • y) ∂(μHE[d] : Measure (Eucl P)) :=
            setIntegral_indicator measurableSet_ball
        _ = ∫ y in (L : Set (Eucl P)) ∩ ball 0 R,
              f y * θ (x + r • y) ∂(μHE[d] : Measure (Eucl P)) := by
            rw [hset r hr hrR]
        _ = ∫ y in (L : Set (Eucl P)) ∩ ball 0 R, f y * θ x ∂(μHE[d] : Measure (Eucl P)) := by
            refine setIntegral_congr_fun hLmeas ?_
            intro y hy
            simp only [hval r hr hrR y hy]
        _ = (∫ y in (L : Set (Eucl P)) ∩ ball 0 R, f y ∂(μHE[d] : Measure (Eucl P))) * θ x :=
            integral_mul_const _ _
        _ = (∫ y in (L : Set (Eucl P)),
              (ball (0 : Eucl P) R).indicator (fun y => f y) y ∂(μHE[d] : Measure (Eucl P))) *
              θ x := by
            rw [setIntegral_indicator measurableSet_ball]
        _ = θ x * ∫ y in (L : Set (Eucl P)), f y ∂(μHE[d] : Measure (Eucl P)) := by
            rw [← hind2, mul_comm]
    refine tendsto_const_nhds.congr' ?_
    have hpos : 0 < δ / R := div_pos hδ hRpos
    filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
    have hrR : r * R ≤ δ := by
      have := hr.2
      rw [lt_div_iff₀ hRpos] at this
      exact this.le
    exact (key r hr.1 hrR).symm
  have face_isClosed : ∀ {P d : ℕ} (ρ : ℝ) (G : LatticeFaceIndex d P),
      IsClosed (latticeFace ρ G) := by
    intro P d ρ G
    have : latticeFace ρ G = ⋂ i : Fin P,
        {x : Eucl P | (i ∈ range G.2 → ρ * (G.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((G.1 i : ℝ) + 1)) ∧
          (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} := by
      ext x; simp [latticeFace]
    rw [this]
    refine isClosed_iInter fun i => ?_
    have hc : Continuous fun x : Eucl P => x i := (EuclideanSpace.proj i).continuous
    by_cases hi : i ∈ range G.2
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
    · simp only [hi, IsEmpty.forall_iff, true_and, not_false_eq_true, forall_const]
      exact isClosed_eq hc continuous_const
  -- (L4) Near a point of `G°` no other face appears, and the face plane stays inside `G°`.
  have relint_local_structure : ∀ (P d : ℕ) (ρ : ℝ), 0 < ρ →
      ∀ (G : LatticeFaceIndex d P) (x : Eucl P),
      (∀ i : Fin P, (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
        (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))) →
      ∃ δ : ℝ, 0 < δ ∧
        (∀ G' : LatticeFaceIndex d P, (latticeFace ρ G' ∩ ball x δ).Nonempty → G' = G) ∧
        ∀ y : Eucl P,
          y - x ∈ Submodule.span ℝ (range fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) →
          y ∈ ball x δ → ∀ i : Fin P,
            (i ∈ range G.2 → ρ * (G.1 i : ℝ) < y i ∧ y i < ρ * ((G.1 i : ℝ) + 1)) ∧
            (i ∉ range G.2 → y i = ρ * (G.1 i : ℝ)) := by
    intro P d ρ hρ G x hx
    -- finitely many faces near x
    have hfin := faces_meeting_finite P d ρ hρ (ball x 1) isBounded_ball
    set S := {G' : LatticeFaceIndex d P | (latticeFace ρ G' ∩ ball x 1).Nonempty} \ {G} with hS
    have hSfin : S.Finite := hfin.sdiff
    set U := ⋃ G' ∈ S, latticeFace ρ G' with hU
    have hUclosed : IsClosed U := hSfin.isClosed_biUnion fun G' _ => face_isClosed ρ G'
    have hxU : x ∉ U := by
      intro hxU
      simp only [hU, mem_iUnion] at hxU
      obtain ⟨G', hG'S, hxG'⟩ := hxU
      exact hG'S.2 (face_eq_of_mem_relint P d ρ hρ G G' x hx hxG')
    obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 hUclosed.isOpen_compl x hxU
    -- open box condition
    set O :=
      {y : Eucl P | ∀ i ∈ range G.2, ρ * (G.1 i : ℝ) < y i ∧ y i < ρ * ((G.1 i : ℝ) + 1)} with hO
    have hOopen : IsOpen O := by
      have : O = ⋂ i ∈ range G.2,
          {y : Eucl P | ρ * (G.1 i : ℝ) < y i ∧ y i < ρ * ((G.1 i : ℝ) + 1)} := by
        ext y; simp [hO]
      rw [this]
      refine (Set.toFinite _).isOpen_biInter fun i _ => ?_
      have hc : Continuous fun y : Eucl P => y i := (EuclideanSpace.proj i).continuous
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    have hxO : x ∈ O := fun i hi => (hx i).1 hi
    obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.isOpen_iff.1 hOopen x hxO
    refine ⟨min (min δ₁ δ₂) 1, by positivity, ?_, ?_⟩
    · rintro G' ⟨y, hyF, hyB⟩
      by_contra hne
      have hy1 : y ∈ ball x 1 := ball_subset_ball (min_le_right _ _) hyB
      have hyδ₁ : y ∈ ball x δ₁ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hyB
      have hG'S : G' ∈ S := ⟨⟨y, hyF, hy1⟩, hne⟩
      have : y ∈ U := by
        simp only [hU, mem_iUnion]
        exact ⟨G', hG'S, hyF⟩
      exact hball₁ hyδ₁ this
    · intro y hyspan hyB i
      have hyδ₂ : y ∈ ball x δ₂ := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hyB
      refine ⟨fun hi => hball₂ hyδ₂ i hi, fun hi => ?_⟩
      -- coordinates off range vanish on the span
      have hzero : ∀ v ∈ Submodule.span ℝ (range fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)),
          (v : Eucl P) i = 0 := by
        intro v hv
        have hle : Submodule.span ℝ (range fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) ≤
            LinearMap.ker ((EuclideanSpace.proj i : Eucl P →L[ℝ] ℝ) : Eucl P →ₗ[ℝ] ℝ) := by
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          have hne : i ≠ G.2 j := fun h => hi ⟨j, h.symm⟩
          simp [hne]
        have := hle hv
        simpa using this
      have h0 := hzero _ hyspan
      have hxi := (hx i).2 hi
      have : y i = x i := by
        have : (y - x) i = y i - x i := rfl
        linarith [this ▸ h0]
      rw [this, hxi]
  -- Steps 1–3: the boundary of an integer lattice `(m+1)`-chain is an integer lattice
  -- `m`-chain, with `γ_G = ∑ ± β_F` over the faces `F` having `G` as a facet.
  have action_eq_zero : ∀ {P k : ℕ} (ρ : ℝ) (G : LatticeFaceIndex k P)
      (η : DifferentialForm (Eucl P) k) (h : latticeFace ρ G ∩ tsupport η = ∅),
      latticeFaceAction ρ G η = 0 := by
    intro P k ρ G η h
    unfold latticeFaceAction
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport η :=
      fun hx' => (h ▸ (⟨hx, hx'⟩ : x ∈ latticeFace ρ G ∩ tsupport η) : x ∈ (∅ : Set (Eucl P)))
    rw [image_eq_zero_of_notMem_tsupport hx']
    rfl
  have face_minus_sub : ∀ {P m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (F : LatticeFaceIndex (m + 1) P)
      (i : Fin (m + 1)),
      latticeFace ρ ((F.1, (Fin.succAboveOrderEmb i).trans F.2) : LatticeFaceIndex m P) ⊆
        latticeFace ρ F := by
    intro P m ρ hρ F i x hx l
    have hx' := hx l
    simp only at hx'
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j = i
      · subst hj
        have hnot : F.2 j ∉ range ((Fin.succAboveOrderEmb j).trans F.2) := by
          rintro ⟨k, hk⟩
          simp only [RelEmbedding.trans_apply, Fin.coe_succAboveOrderEmb] at hk
          exact Fin.succAbove_ne j k (F.2.injective hk)
        rw [hx'.2 hnot]
        constructor <;> nlinarith
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        exact hx'.1 ⟨k, rfl⟩
    · intro hl
      apply hx'.2
      rintro ⟨k, rfl⟩
      exact hl ⟨_, rfl⟩
  have face_plus_sub : ∀ {P m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (F : LatticeFaceIndex (m + 1) P)
      (i : Fin (m + 1)),
      latticeFace ρ ((F.1 + Pi.single (F.2 i) 1, (Fin.succAboveOrderEmb i).trans F.2) :
        LatticeFaceIndex m P) ⊆ latticeFace ρ F := by
    intro P m ρ hρ F i x hx l
    have hx' := hx l
    simp only at hx'
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j = i
      · subst hj
        have hnot : F.2 j ∉ range ((Fin.succAboveOrderEmb j).trans F.2) := by
          rintro ⟨k, hk⟩
          simp only [RelEmbedding.trans_apply, Fin.coe_succAboveOrderEmb] at hk
          exact Fin.succAbove_ne j k (F.2.injective hk)
        rw [hx'.2 hnot]
        simp only [Pi.add_apply, Pi.single_eq_same, Int.cast_add, Int.cast_one]
        constructor <;> nlinarith
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        have h := hx'.1 ⟨k, rfl⟩
        have hne : F.2 (i.succAbove k) ≠ F.2 i := fun h' => Fin.succAbove_ne i k (F.2.injective h')
        simp only [Pi.add_apply, Pi.single_eq_of_ne hne, add_zero] at h
        exact h
    · intro hl
      have hne : l ≠ F.2 i := fun h => hl ⟨i, h.symm⟩
      have h := hx'.2 (by rintro ⟨k, rfl⟩; exact hl ⟨_, rfl⟩)
      simp only [Pi.add_apply, Pi.single_eq_of_ne hne, add_zero] at h
      exact h
  -- Regrouping the finite double sum given by Stokes on each face.
  have boundary_lattice_chain : ∀ (P m : ℕ) (ρ : ℝ), 0 < ρ →
      (∀ (F : LatticeFaceIndex (m + 1) P) (ω : DifferentialForm (Eucl P) m), IsSmoothForm ω →
        latticeFaceAction ρ F (exteriorDerivative ω) =
          ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
            (latticeFaceAction ρ (F.1 + Pi.single (F.2 i) 1, (Fin.succAboveOrderEmb i).trans F.2)
              ω - latticeFaceAction ρ (F.1, (Fin.succAboveOrderEmb i).trans F.2) ω)) →
      ∀ (β : LatticeFaceIndex (m + 1) P → ℤ)
        (Pc : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
        IsLatticeChain ρ (fun F => (β F : ℝ)) Pc →
        ∃ γ : LatticeFaceIndex m P → ℤ, IsLatticeChain ρ (fun G => (γ G : ℝ)) Pc.boundary := by
    intro P m ρ hρ hS β Pc hPc
    classical
    refine ⟨fun G => ∑ p : SimonMultiIndex (m + 1) P × Fin (m + 1),
      if (Fin.succAboveOrderEmb p.2).trans p.1 = G.2 then
        (-1) ^ (p.2 : ℕ) * (β (G.1 - Pi.single (p.1 p.2) 1, p.1) - β (G.1, p.1)) else 0, ?_⟩
    intro ω
    set η : DifferentialForm (Eucl P) m := (ω : DifferentialForm (Eucl P) m) with hη
    have hsmooth : IsSmoothForm η := ω.property.1.1
    have hcpt : HasCompactSupport η := ω.property.1.2
    set K := tsupport η with hKdef
    have hKb : Bornology.IsBounded K := hcpt.isCompact.isBounded
    have hFfin := faces_meeting_finite P (m + 1) ρ hρ K hKb
    have hGfin := faces_meeting_finite P m ρ hρ K hKb
    set SF := hFfin.toFinset with hSF
    set SG := hGfin.toFinset with hSG
    -- notation for the two boundary faces
    set Dp : LatticeFaceIndex (m + 1) P → Fin (m + 1) → LatticeFaceIndex m P :=
      fun F i => (F.1 + Pi.single (F.2 i) 1, (Fin.succAboveOrderEmb i).trans F.2) with hDp
    set Dm : LatticeFaceIndex (m + 1) P → Fin (m + 1) → LatticeFaceIndex m P :=
      fun F i => (F.1, (Fin.succAboveOrderEmb i).trans F.2) with hDm
    -- vanishing of m-face actions off SG
    have hvG : ∀ G : LatticeFaceIndex m P, G ∉ SG → latticeFaceAction ρ G η = 0 := by
      intro G hG
      apply action_eq_zero
      rw [hSG, Set.Finite.mem_toFinset] at hG
      exact Set.not_nonempty_iff_eq_empty.1 hG
    -- faces of F in SG force F ∈ SF
    have hFp : ∀ F i, Dp F i ∈ SG → F ∈ SF := by
      intro F i h
      rw [hSG, Set.Finite.mem_toFinset] at h
      rw [hSF, Set.Finite.mem_toFinset]
      obtain ⟨x, hx1, hx2⟩ := h
      exact ⟨x, face_plus_sub hρ.le F i hx1, hx2⟩
    have hFm : ∀ F i, Dm F i ∈ SG → F ∈ SF := by
      intro F i h
      rw [hSG, Set.Finite.mem_toFinset] at h
      rw [hSF, Set.Finite.mem_toFinset]
      obtain ⟨x, hx1, hx2⟩ := h
      exact ⟨x, face_minus_sub hρ.le F i hx1, hx2⟩
    -- LHS
    have hL : Pc.boundary ω =
        ∑ F ∈ SF, (β F : ℝ) * latticeFaceAction ρ F (exteriorDerivative η) := by
      rw [GeometricCurrentOn.boundary_apply, hPc]
      apply tsum_eq_sum
      intro F hF
      have : latticeFaceAction ρ F (exteriorDerivative η) = 0 := by
        apply action_eq_zero
        rw [hSF, Set.Finite.mem_toFinset] at hF
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx1, hx2⟩
        exact hF ⟨x, hx1, tsupport_exteriorDerivative_subset η hx2⟩
      simp only [exteriorDerivativeTestOn, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [this, mul_zero]
    have hR : (∑' G, ((fun G => ∑ p : SimonMultiIndex (m + 1) P × Fin (m + 1),
        if (Fin.succAboveOrderEmb p.2).trans p.1 = G.2 then
          (-1) ^ (p.2 : ℕ) * (β (G.1 - Pi.single (p.1 p.2) 1, p.1) - β (G.1, p.1))
        else 0) G : ℝ) * latticeFaceAction ρ G η) =
        ∑ G ∈ SG, (((∑ p : SimonMultiIndex (m + 1) P × Fin (m + 1),
          if (Fin.succAboveOrderEmb p.2).trans p.1 = G.2 then
            (-1) ^ (p.2 : ℕ) * (β (G.1 - Pi.single (p.1 p.2) 1, p.1) - β (G.1, p.1))
          else 0 : ℤ) : ℝ) * latticeFaceAction ρ G η) := by
      apply tsum_eq_sum
      intro G hG
      rw [hvG G hG, mul_zero]
    show Pc.boundary ω = _
    rw [hL, hR]
    -- expand Stokes
    have hStokes : ∀ F ∈ SF, (β F : ℝ) * latticeFaceAction ρ F (exteriorDerivative η) =
        ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (β F : ℝ) * latticeFaceAction ρ (Dp F i) η -
        ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (β F : ℝ) * latticeFaceAction ρ (Dm F i) η := by
      intro F _
      rw [hS F η hsmooth, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hDp, hDm]
      ring
    rw [Finset.sum_congr rfl hStokes, Finset.sum_sub_distrib]
    -- RHS split
    have hsplit : ∀ G ∈ SG, (((∑ p : SimonMultiIndex (m + 1) P × Fin (m + 1),
        if (Fin.succAboveOrderEmb p.2).trans p.1 = G.2 then
          (-1) ^ (p.2 : ℕ) * (β (G.1 - Pi.single (p.1 p.2) 1, p.1) - β (G.1, p.1))
        else 0 : ℤ) : ℝ) * latticeFaceAction ρ G η) =
        (∑ p : SimonMultiIndex (m + 1) P × Fin (m + 1),
          if (Fin.succAboveOrderEmb p.2).trans p.1 = G.2 then
            (-1 : ℝ) ^ (p.2 : ℕ) * (β (G.1 - Pi.single (p.1 p.2) 1, p.1) : ℝ) *
              latticeFaceAction ρ G η
          else 0) -
        (∑ p : SimonMultiIndex (m + 1) P × Fin (m + 1),
          if (Fin.succAboveOrderEmb p.2).trans p.1 = G.2 then
            (-1 : ℝ) ^ (p.2 : ℕ) * (β (G.1, p.1) : ℝ) * latticeFaceAction ρ G η
          else 0) := by
      intro G _
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
    congr 1
    · -- plus part
      rw [← Finset.sum_product', ← Finset.sum_product']
      refine Finset.sum_bij_ne_zero (fun a _ _ => (Dp a.1 a.2, (a.1.2, a.2))) ?_ ?_ ?_ ?_
      · intro a ha hne
        refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
        by_contra hnot
        exact hne (by rw [hvG _ hnot, mul_zero])
      · intro a ha1 ha2 b hb1 hb2 hab
        simp only [hDp, Prod.mk.injEq] at hab
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hab
        have hα : a.1.2 = b.1.2 := h3
        have hi : a.2 = b.2 := h4
        have h1' : a.1.1 = b.1.1 := by
          rw [hα, hi] at h1
          exact add_right_cancel h1
        exact Prod.ext (Prod.ext h1' hα) hi
      · intro b hb hne
        obtain ⟨hbG, -⟩ := Finset.mem_product.1 hb
        have hcond : (Fin.succAboveOrderEmb b.2.2).trans b.2.1 = b.1.2 := by
          by_contra hc
          exact hne (by simp [hc])
        refine ⟨((b.1.1 - Pi.single (b.2.1 b.2.2) 1, b.2.1), b.2.2), ?_, ?_, ?_⟩
        · refine Finset.mem_product.2 ⟨hFp _ b.2.2 ?_, Finset.mem_univ _⟩
          have : Dp (b.1.1 - Pi.single (b.2.1 b.2.2) 1, b.2.1) b.2.2 = b.1 := by
            simp only [hDp, sub_add_cancel, hcond]
          rw [this]; exact hbG
        · have : Dp (b.1.1 - Pi.single (b.2.1 b.2.2) 1, b.2.1) b.2.2 = b.1 := by
            simp only [hDp, sub_add_cancel, hcond]
          simp only [this]
          simpa [hcond] using hne
        · simp only [hDp, sub_add_cancel, hcond]
      · intro a _ _
        have hc : (Fin.succAboveOrderEmb a.2).trans a.1.2 = (Dp a.1 a.2).2 := rfl
        simp only [hc, ite_true]
        simp only [hDp, add_sub_cancel_right]
    · -- minus part
      rw [← Finset.sum_product', ← Finset.sum_product']
      refine Finset.sum_bij_ne_zero (fun a _ _ => (Dm a.1 a.2, (a.1.2, a.2))) ?_ ?_ ?_ ?_
      · intro a ha hne
        refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
        by_contra hnot
        exact hne (by rw [hvG _ hnot, mul_zero])
      · intro a ha1 ha2 b hb1 hb2 hab
        simp only [hDm, Prod.mk.injEq] at hab
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hab
        exact Prod.ext (Prod.ext h1 h3) h4
      · intro b hb hne
        obtain ⟨hbG, -⟩ := Finset.mem_product.1 hb
        have hcond : (Fin.succAboveOrderEmb b.2.2).trans b.2.1 = b.1.2 := by
          by_contra hc
          exact hne (by simp [hc])
        refine ⟨((b.1.1, b.2.1), b.2.2), ?_, ?_, ?_⟩
        · refine Finset.mem_product.2 ⟨hFm _ b.2.2 ?_, Finset.mem_univ _⟩
          have : Dm (b.1.1, b.2.1) b.2.2 = b.1 := by
            simp only [hDm, hcond]
          rw [this]; exact hbG
        · have : Dm (b.1.1, b.2.1) b.2.2 = b.1 := by
            simp only [hDm, hcond]
          simp only [this]
          simpa [hcond] using hne
        · simp only [hDm, hcond]
      · intro a _ _
        have hc : (Fin.succAboveOrderEmb a.2).trans a.1.2 = (Dm a.1 a.2).2 := rfl
        simp only [hc, ite_true]
        simp only [hDm]
  -- Steps 4–7: an integer lattice chain is `τ(M, θ, ξ)` with `M = ⋃ {G° : γ_G ≠ 0}`,
  -- `θ = |γ_G|` and `ξ = sign(γ_G) e_{γ'}` on `G°`.
  have relint_sub : ∀ {P d : ℕ} (ρ : ℝ) (G : LatticeFaceIndex d P),
      {x : Eucl P | ∀ i : Fin P,
        (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
        (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} ⊆ latticeFace ρ G := by
    intro P d ρ G x hx i
    exact ⟨fun hi => ⟨((hx i).1 hi).1.le, ((hx i).1 hi).2.le⟩, (hx i).2⟩
  have relint_meas : ∀ {P d : ℕ} (ρ : ℝ) (G : LatticeFaceIndex d P),
      MeasurableSet {x : Eucl P | ∀ i : Fin P,
        (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
        (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} := by
    intro P d ρ G
    have : {x : Eucl P | ∀ i : Fin P,
          (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
          (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} = ⋂ i : Fin P,
        {x : Eucl P | (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
          (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} := by
      ext x; simp
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    have hc : Measurable fun x : Eucl P => x i := (EuclideanSpace.proj i).continuous.measurable
    by_cases hi : i ∈ range G.2
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (measurableSet_lt measurable_const hc).inter (measurableSet_lt hc measurable_const)
    · simp only [hi, IsEmpty.forall_iff, true_and, not_false_eq_true, forall_const]
      exact measurableSet_eq_fun hc measurable_const
  have mem_span_of_coord : ∀ {P d : ℕ} (G : LatticeFaceIndex d P) (v : Eucl P)
      (hv : ∀ i, i ∉ range G.2 → v i = 0),
      v ∈ Submodule.span ℝ (range fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) := by
    intro P d G v hv
    classical
    have hrepr : v = ∑ j, v (G.2 j) • EuclideanSpace.single (G.2 j) (1 : ℝ) := by
      ext i
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        PiLp.ofLp_single, Pi.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hi : i ∈ range G.2
      · obtain ⟨j, rfl⟩ := hi
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          have : G.2 j ≠ G.2 b := fun h => hb (G.2.injective h).symm
          simp [this]
        · simp
      · rw [hv i hi]
        symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have : i ≠ G.2 j := fun h => hi ⟨j, h.symm⟩
        simp [this]
    rw [hrepr]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have lattice_chain_im : ∀ (P d : ℕ) (ρ : ℝ), 0 < ρ → ∀ (β : LatticeFaceIndex d P → ℤ)
      (X : GeometricCurrentOn (univ : Set (Eucl P)) d),
      IsLatticeChain ρ (fun G => (β G : ℝ)) X → IsIntegerMultiplicity X := by
    intro P d ρ hρ β X hX
    classical
    set R : LatticeFaceIndex d P → Set (Eucl P) := fun G => {x : Eucl P | ∀ i : Fin P,
      (i ∈ range G.2 → ρ * (G.1 i : ℝ) < x i ∧ x i < ρ * ((G.1 i : ℝ) + 1)) ∧
      (i ∉ range G.2 → x i = ρ * (G.1 i : ℝ))} with hRdef
    have huniq : ∀ G G' x, x ∈ R G → x ∈ R G' → G' = G := fun G G' x h h' =>
      face_eq_of_mem_relint P d ρ hρ G G' x h (relint_sub ρ G' h')
    have hdisj : ∀ G G', G ≠ G' → Disjoint (R G) (R G') := by
      intro G G' hne
      rw [Set.disjoint_left]
      intro x h h'
      exact hne (huniq G G' x h h').symm
    set e : LatticeFaceIndex d P → Fin d → Eucl P :=
      fun G j => EuclideanSpace.single (G.2 j) (1:ℝ) with he_def
    set v : LatticeFaceIndex d P → NVector (Eucl P) d :=
      fun G => ((β G).sign : ℝ) • simpleNVector (e G) with hv_def
    set M : Set (Eucl P) := ⋃ G, ⋃ (_ : β G ≠ 0), R G with hMdef
    set idx : Eucl P → Option (LatticeFaceIndex d P) :=
      fun x => if h : ∃ G, x ∈ R G then some h.choose else none with hidxdef
    have hidx : ∀ G, ∀ x ∈ R G, idx x = some G := by
      intro G x hx
      have h : ∃ G, x ∈ R G := ⟨G, hx⟩
      simp only [hidxdef, dite_eq_left h]
      rw [huniq G h.choose x hx h.choose_spec]
    have hidxnone : ∀ x, (∀ G, x ∉ R G) → idx x = none := by
      intro x hx
      have h : ¬ ∃ G, x ∈ R G := fun ⟨G, hG⟩ => hx G hG
      simp only [hidxdef, dite_eq_right h]
    set gθ : Option (LatticeFaceIndex d P) → ℝ :=
      fun o => match o with | some G => |(β G : ℝ)| | none => 0 with hgθ
    set gξ : Option (LatticeFaceIndex d P) → NVector (Eucl P) d :=
      fun o => match o with | some G => v G | none => 0 with hgξ
    set θ : Eucl P → ℝ := gθ ∘ idx with hθdef
    set ξ : Eucl P → NVector (Eucl P) d := gξ ∘ idx with hξdef
    have hθ : ∀ G, ∀ x ∈ R G, θ x = |(β G : ℝ)| := by
      intro G x hx
      simp only [hθdef, Function.comp_apply, hidx G x hx, hgθ]
    have hξ : ∀ G, ∀ x ∈ R G, ξ x = v G := by
      intro G x hx
      simp only [hξdef, Function.comp_apply, hidx G x hx, hgξ]
    have hMmeas : MeasurableSet M :=
      MeasurableSet.iUnion fun G => MeasurableSet.iUnion fun _ => relint_meas ρ G
    have hmemM : ∀ x, x ∈ M ↔ ∃ G, β G ≠ 0 ∧ x ∈ R G := by
      intro x; simp [hMdef]
    have hRfin : ∀ G, (μHE[d] : Measure (Eucl P)) (R G) ≠ ∞ := by
      intro G
      refine ne_top_of_le_ne_top ?_ (measure_mono (relint_sub ρ G))
      rw [(face_measure P d ρ hρ G).1]; exact ENNReal.ofReal_ne_top
    -- affine parametrizations
    set c : LatticeFaceIndex d P → Eucl P :=
      fun G => ∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1:ℝ) with hc_def
    set A : LatticeFaceIndex d P → EuclideanSpace ℝ (Fin d) → Eucl P :=
      fun G s => c G + ∑ j, s j • e G j with hA_def
    have hAiso : ∀ G, Isometry (A G) := by
      intro G
      have he : Orthonormal ℝ (e G) := (EuclideanSpace.orthonormal_single).comp _ G.2.injective
      refine Isometry.of_dist_eq fun s t => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h : A G s - A G t = ∑ j, (s - t) j • e G j := by
        simp only [hA_def, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← sub_smul,
          PiLp.sub_apply]
      rw [h]
      have h1 : ‖∑ j, (s - t) j • e G j‖ ^ 2 = ‖s - t‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, he.inner_sum, EuclideanSpace.real_norm_sq_eq]
        simp [sq]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
    have hRrange : ∀ G, R G ⊆ range (A G) := by
      intro G x hx
      refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), ?_⟩
      ext i
      simp [hA_def, hc_def, he_def, Pi.single_apply]
      by_cases hi : i ∈ range G.2
      · obtain ⟨j, rfl⟩ := hi
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          have : G.2 j ≠ G.2 b := fun h => hb (G.2.injective h).symm
          simp [this]
        · simp
      · rw [(hx i).2 hi]
        have : ∀ j, (if i = G.2 j then x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ) else 0) = 0 :=
          fun j => ite_eq_right (fun h => hi ⟨j, h.symm⟩)
        simp [this]
    refine ⟨M, θ, ξ, ⟨subset_univ _, hMmeas.nullMeasurableSet, ?rect, ?pos, ?intOn, ?aesm,
      ?orients⟩, ?integer, ?repr⟩
    case rect =>
      apply CountablyRectifiable.mono (N := M) (M := ⋃₀ (range fun G => range (A G)))
      · apply Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (countable_range _)
        rintro _ ⟨G, rfl⟩
        exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hAiso G).lipschitzWith
      · intro x hx
        obtain ⟨G, -, hxG⟩ := (hmemM x).1 hx
        exact ⟨range (A G), ⟨G, rfl⟩, hRrange G hxG⟩
    case pos =>
      intro x hx
      obtain ⟨G, hG, hxG⟩ := (hmemM x).1 hx
      rw [hθ G x hxG]
      exact abs_pos.2 (by exact_mod_cast hG)
    case intOn =>
      intro K hK _
      have hfin := faces_meeting_finite P d ρ hρ K hK.isBounded
      refine IntegrableOn.mono_set (t := ⋃ G ∈ hfin.toFinset, R G) ?_ ?_
      · rw [integrableOn_finset_iUnion]
        intro G _
        have : IntegrableOn (fun _ => |(β G : ℝ)|) (R G) (μHE[d] : Measure (Eucl P)) :=
          integrableOn_const (hRfin G)
        exact this.congr_fun (fun x hx => (hθ G x hx).symm) (relint_meas ρ G)
      · rintro x ⟨hxM, hxK⟩
        obtain ⟨G, -, hxG⟩ := (hmemM x).1 hxM
        simp only [mem_iUnion]
        exact ⟨G, by rw [Set.Finite.mem_toFinset]; exact ⟨x, relint_sub ρ G hxG, hxK⟩, hxG⟩
    case aesm =>
      let : MeasurableSpace (Option (LatticeFaceIndex d P)) := ⊤
      have : MeasurableSingletonClass (Option (LatticeFaceIndex d P)) := ⟨fun _ => trivial⟩
      have hidxm : Measurable idx := by
        refine measurable_to_countable' fun o => ?_
        cases o with
        | some G =>
          have : idx ⁻¹' {some G} = R G := by
            ext x
            constructor
            · intro hx
              by_cases h : ∃ G', x ∈ R G'
              · obtain ⟨G', hG'⟩ := h
                have := hidx G' x hG'
                rw [Set.mem_preimage, Set.mem_singleton_iff, this] at hx
                cases hx
                exact hG'
              · push Not at h
                have := hidxnone x h
                rw [Set.mem_preimage, Set.mem_singleton_iff, this] at hx
                cases hx
            · intro hx
              rw [Set.mem_preimage, Set.mem_singleton_iff, hidx G x hx]
          rw [this]; exact relint_meas ρ G
        | none =>
          have : idx ⁻¹' {none} = (⋃ G, R G)ᶜ := by
            ext x
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
              not_exists]
            constructor
            · intro hx G hG
              rw [hidx G x hG] at hx
              cases hx
            · intro hx
              exact hidxnone x hx
          rw [this]
          exact (MeasurableSet.iUnion fun G => relint_meas ρ G).compl
      exact (StronglyMeasurable.of_discrete.comp_measurable hidxm).aestronglyMeasurable
    case orients =>
      refine ae_restrict_of_forall_mem hMmeas fun x hx => ?_
      obtain ⟨G, hG, hxG⟩ := (hmemM x).1 hx
      have he : Orthonormal ℝ (e G) := (EuclideanSpace.orthonormal_single).comp _ G.2.injective
      refine ⟨e G, he, ?_, ?_⟩
      · obtain ⟨δ, hδ, h1, h2⟩ := relint_local_structure P d ρ hρ G x hxG
        have hfr : Module.finrank ℝ (Submodule.span ℝ (range (e G))) = d := by
          rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
        -- M near x lies in R G
        have hnear : ∀ y ∈ M ∩ ball x δ, y ∈ R G := by
          rintro y ⟨hyM, hyB⟩
          obtain ⟨G', -, hyG'⟩ := (hmemM y).1 hyM
          have : G' = G := h1 G' ⟨y, relint_sub ρ G' hyG', hyB⟩
          rw [← this]; exact hyG'
        refine tangent_of_locally_affine P d M θ x _ δ hδ hfr ?_ ?_
        · ext y
          constructor
          · intro hy
            refine ⟨?_, hy.2⟩
            have hyG := hnear y hy
            apply mem_span_of_coord G
            intro i hi
            have h1' := (hyG i).2 hi
            have h2' := (hxG i).2 hi
            show y i - x i = 0
            rw [h1', h2', sub_self]
          · rintro ⟨hyL, hyB⟩
            refine ⟨(hmemM y).2 ⟨G, hG, h2 y hyL hyB⟩, hyB⟩
        · intro y hy
          rw [hθ G y (hnear y hy), hθ G x hxG]
      · rw [hξ G x hxG]
        simp only [hv_def]
        rcases lt_or_gt_of_ne hG with hneg | hpos
        · right
          rw [Int.sign_eq_neg_one_of_neg hneg]; push_cast
          exact neg_one_smul ℝ (simpleNVector (e G))
        · left; rw [Int.sign_eq_one_of_pos hpos]; simp
    case integer =>
      intro x hx
      obtain ⟨G, -, hxG⟩ := (hmemM x).1 hx
      refine ⟨(β G).natAbs, ?_⟩
      rw [hθ G x hxG]
      simp
    case repr =>
      intro ω
      set η : DifferentialForm (Eucl P) d := (ω : DifferentialForm (Eucl P) d) with hη
      have hcpt : HasCompactSupport η := ω.property.1.2
      have hcont : Continuous η := ω.property.1.1.continuous
      set K := tsupport η with hKdef
      have hfin := faces_meeting_finite P d ρ hρ K hcpt.isCompact.isBounded
      set SG := hfin.toFinset with hSG
      have hvG : ∀ G : LatticeFaceIndex d P, G ∉ SG → latticeFaceAction ρ G η = 0 := by
        intro G hG
        apply action_eq_zero
        rw [hSG, Set.Finite.mem_toFinset] at hG
        exact Set.not_nonempty_iff_eq_empty.1 hG
      rw [hX ω, tsum_eq_sum (s := SG) (fun G hG => by rw [hvG G hG, mul_zero])]
      set SG' := SG.filter (fun G => β G ≠ 0) with hSG'
      have hsum0 : ∑ G ∈ SG, (β G : ℝ) * latticeFaceAction ρ G η =
          ∑ G ∈ SG', (β G : ℝ) * latticeFaceAction ρ G η := by
        rw [hSG', Finset.sum_filter_of_ne]
        intro G _ h hβ
        apply h
        rw [hβ]; simp
      rw [hsum0]
      unfold tauAction
      -- bound on the form
      obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcpt
      have hpiece : ∀ G, β G ≠ 0 → ∀ x ∈ R G, θ x * ξ x (η x) = (β G : ℝ) * η x (e G) := by
        intro G hG x hx
        rw [hθ G x hx, hξ G x hx]
        simp only [hv_def, smul_apply, simpleNVector_apply, smul_eq_mul]
        rw [← mul_assoc]
        congr 1
        have : |(β G : ℝ)| * ((β G).sign : ℝ) = ((|β G| * (β G).sign : ℤ) : ℝ) := by push_cast; ring
        rw [this, mul_comm, Int.sign_mul_abs]
      have hint : ∀ G, β G ≠ 0 →
          IntegrableOn (fun x => θ x * ξ x (η x)) (R G) (μHE[d] : Measure (Eucl P)) := by
        intro G hG
        have hc2 : Continuous fun x => (β G : ℝ) * η x (e G) := by
          have : Continuous fun x => η x (e G) :=
            (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (e G)).continuous.comp hcont
          exact continuous_const.mul this
        have hI :
            IntegrableOn (fun x => (β G : ℝ) * η x (e G)) (R G) (μHE[d] : Measure (Eucl P)) := by
          refine Measure.integrableOn_of_bounded (M := |(β G : ℝ)| * C) (hRfin G)
            hc2.aestronglyMeasurable ?_
          refine Eventually.of_forall fun x => ?_
          rw [norm_mul, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc ‖η x (e G)‖ ≤ ‖η x‖ * ∏ j, ‖e G j‖ := (η x).le_opNorm _
            _ = ‖η x‖ := by simp [he_def]
            _ ≤ C := hC x
        exact hI.congr_fun (fun x hx => (hpiece G hG x hx).symm) (relint_meas ρ G)
      have hsubM : (⋃ G ∈ SG', R G) ⊆ M := by
        intro x hx
        simp only [mem_iUnion] at hx
        obtain ⟨G, hG, hxG⟩ := hx
        rw [hSG', Finset.mem_filter] at hG
        exact (hmemM x).2 ⟨G, hG.2, hxG⟩
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMmeas hsubM]
      · rw [integral_biUnion_finset SG' (fun G _ => relint_meas ρ G)
          (fun G _ G' _ hne => hdisj G G' hne) (fun G hG => hint G (Finset.mem_filter.1 hG).2)]
        refine Finset.sum_congr rfl fun G hG => ?_
        have hβ := (Finset.mem_filter.1 hG).2
        rw [setIntegral_congr_fun (relint_meas ρ G) (fun x hx => hpiece G hβ x hx),
          integral_const_mul]
        congr 1
        unfold latticeFaceAction
        symm
        apply setIntegral_congr_set
        rw [ae_eq_set]
        constructor
        · rw [sdiff_eq_empty.2 (relint_sub ρ G)]; exact measure_empty
        · exact (face_measure P d ρ hρ G).2
      · rintro x ⟨hxM, hxn⟩
        obtain ⟨G, hG, hxG⟩ := (hmemM x).1 hxM
        have hGn : G ∉ SG := by
          intro hGS
          apply hxn
          simp only [mem_iUnion]
          exact ⟨G, Finset.mem_filter.2 ⟨hGS, hG⟩, hxG⟩
        have hxK : x ∉ K := by
          intro hxK
          apply hGn
          rw [hSG, Set.Finite.mem_toFinset]
          exact ⟨x, relint_sub ρ G hxG, hxK⟩
        rw [image_eq_zero_of_notMem_tsupport hxK, map_zero, mul_zero]
  intro P m ρ hρ β Pc h
  obtain ⟨γ, hγ⟩ := boundary_lattice_chain P m ρ hρ
      (Submission.br_lattice_face_stokes P m ρ hρ) β Pc h
  exact lattice_chain_im P m ρ hρ γ Pc.boundary hγ

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
