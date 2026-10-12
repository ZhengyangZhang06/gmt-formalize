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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
