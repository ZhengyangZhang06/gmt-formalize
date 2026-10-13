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

/-- Step 1 of the proof of the Constancy Theorem (Simon Ch. 6, Theorem 2.34, pp. 142–143): every
top-degree form is `ω = a_ω dx¹ ∧ ⋯ ∧ dxⁿ` with `a_ω(x) = ω(x)(e₁, …, eₙ)`, so `T ∈ 𝒟ₙ(U)` acts as
`T(ω) = u(a_ω)` for `u(b) = T(b dx¹ ∧ ⋯ ∧ dxⁿ)`; `u` is linear on `C^∞` functions with compact
support in `U` and continuous for `C^∞` convergence with supports in a compact `K ⊆ U`.
(Book `n = m + 1`.) -/
theorem Submission.constancy_topForm_scalar_reduction : ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (T : GeometricCurrentOn U (m + 1)), ∃ u : (Eucl (m + 1) → ℝ) → ℝ, (∀ ω : TestFormOn U (m + 1), T ω = u (fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)))) ∧ (∀ b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∃ ω : TestFormOn U (m + 1), ∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) = b x) ∧ (∀ a b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → u (a + b) = u a + u b) ∧ (∀ (c : ℝ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → u (c • a) = c * u a) ∧ (∀ (a : ℕ → Eucl (m + 1) → ℝ) (b : Eucl (m + 1) → ℝ) (K : Set (Eucl (m + 1))), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b))) := by
  intro m U T
  classical
  -- `dx = dx¹ ∧ ⋯ ∧ dxⁿ`, the determinant of the coordinate matrix, with `dx(e) = 1`.
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ)
  set dx : Covector (Eucl (m + 1)) (m + 1) :=
    wedgeCovectors (m + 1) (fun i => EuclideanSpace.proj i)
  have hdx_apply : ∀ v : Fin (m + 1) → Eucl (m + 1),
      dx v = (Matrix.of fun i j => (v j) i).det := fun v => wedgeCovectors_apply_det _ _ v
  have hdx_e : dx e = 1 := by
    have h1 : (Matrix.of fun i j => (e j) i : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 1 := by
      ext i j
      simp [e, Matrix.one_apply]
    rw [hdx_apply, h1, Matrix.det_one]
  -- Every top-degree covector is `α = α(e) • dx` (`AlternatingMap.eq_smul_basis_det`).
  have hrep : ∀ α : Covector (Eucl (m + 1)) (m + 1), α = α e • dx := by
    intro α
    ext v
    set B := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
    have hB : ⇑B = e := by
      funext i
      simp [B, e]
    have hdet : B.det v = dx v := by
      rw [Module.Basis.det_apply, hdx_apply]
      congr 1
    have h := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det B α.toAlternatingMap)
    simp only [AlternatingMap.smul_apply, ContinuousAlternatingMap.coe_toAlternatingMap, hB,
      hdet] at h
    simpa using h
  -- `Λ t = t • dx`; the lift of a scalar function `b` is the form `[b] = Λ ∘ b`.
  set Λ : ℝ →L[ℝ] Covector (Eucl (m + 1)) (m + 1) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight dx
  have hΛ_apply : ∀ t, Λ t = t • dx := fun t => rfl
  have hΛ_e : ∀ t, Λ t e = t := fun t => by
    rw [hΛ_apply, ContinuousAlternatingMap.smul_apply, hdx_e, smul_eq_mul, mul_one]
  -- Admissible functions: `C^∞`, compactly supported, with support in `U`.
  let adm : (Eucl (m + 1) → ℝ) → Prop := fun b =>
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ tsupport b ⊆ U
  have hmem : ∀ b, adm b → (fun x => Λ (b x)) ∈ testFormOnSubmodule U (m + 1) := fun b hb =>
    ⟨⟨Λ.contDiff.comp hb.1, hb.2.1.comp_left (map_zero Λ)⟩,
      (tsupport_comp_subset (map_zero Λ) b).trans hb.2.2⟩
  let lift : ∀ b, adm b → TestFormOn U (m + 1) := fun b hb => ⟨fun x => Λ (b x), hmem b hb⟩
  let u : (Eucl (m + 1) → ℝ) → ℝ := fun b => if h : adm b then T (lift b h) else 0
  have hu : ∀ b (hb : adm b), u b = T (lift b hb) := fun b hb => dite_eq_left hb
  have hadm_add : ∀ a b, adm a → adm b → adm (a + b) := fun a b ha hb =>
    ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, (tsupport_add a b).trans (union_subset ha.2.2 hb.2.2)⟩
  have hadm_smul : ∀ (c : ℝ) a, adm a → adm (c • a) := fun c a ha =>
    ⟨ha.1.const_smul c, ha.2.1.smul_left (f := fun _ => c),
      (tsupport_smul_subset_right (fun _ => c) a).trans ha.2.2⟩
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) `T(ω) = u(a_ω)`, since `[a_ω] = ω`.
    intro ω
    have hω := ω.property
    have ha : adm (fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e) :=
      ⟨(ContinuousAlternatingMap.apply ℝ (Eucl (m + 1)) ℝ e).contDiff.comp hω.1.1,
        hω.1.2.comp_left (g := fun α : Covector (Eucl (m + 1)) (m + 1) => α e) rfl,
        (tsupport_comp_subset (g := fun α : Covector (Eucl (m + 1)) (m + 1) => α e) rfl
          _).trans hω.2⟩
    rw [hu _ ha]
    congr 1
    apply Subtype.ext
    funext x
    exact hrep ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x)
  · -- (ii) `[b](x)(e) = b(x)`.
    intro b hb hcb hsb
    exact ⟨lift b ⟨hb, hcb, hsb⟩, fun x => hΛ_e (b x)⟩
  · -- (iii) Additivity.
    intro a b ha hca hsa hb hcb hsb
    have ha' : adm a := ⟨ha, hca, hsa⟩
    have hb' : adm b := ⟨hb, hcb, hsb⟩
    rw [hu _ (hadm_add a b ha' hb'), hu a ha', hu b hb']
    have : lift (a + b) (hadm_add a b ha' hb') = lift a ha' + lift b hb' := by
      apply Subtype.ext
      funext x
      exact map_add Λ (a x) (b x)
    rw [this]
    exact map_add T.toCurrent _ _
  · -- (iv) Homogeneity.
    intro c a ha hca hsa
    have ha' : adm a := ⟨ha, hca, hsa⟩
    rw [hu _ (hadm_smul c a ha'), hu a ha']
    have : lift (c • a) (hadm_smul c a ha') = c • lift a ha' := by
      apply Subtype.ext
      funext x
      exact map_smul Λ c (a x)
    rw [this]
    exact map_smul T.toCurrent c _
  · -- (v) Continuity: `ω_k = [a_k] − [b] → 0` in `𝒟ⁿ(U)`.
    intro a b K hK hKU ha hb hsa hsb hconv
    have ha' : ∀ k, adm (a k) := fun k =>
      ⟨ha k, hK.of_isClosed_subset (isClosed_tsupport _) (hsa k), (hsa k).trans hKU⟩
    have hb' : adm b := ⟨hb, hK.of_isClosed_subset (isClosed_tsupport _) hsb, hsb.trans hKU⟩
    simp only [hu _ (ha' _), hu b hb']
    rw [← tendsto_sub_nhds_zero_iff]
    set ω : ℕ → TestFormOn U (m + 1) := fun k => lift (a k) (ha' k) - lift b hb'
    have hTω : ∀ k, T (ω k) = T (lift (a k) (ha' k)) - T (lift b hb') := fun k =>
      map_sub T.toCurrent _ _
    simp only [← hTω]
    apply T.continuous'
    refine ⟨K, hK, hKU, ?_, ?_, ?_⟩
    · intro k
      exact (tsupport_sub _ _).trans (union_subset
        ((tsupport_comp_subset (map_zero Λ) (a k)).trans (hsa k))
        ((tsupport_comp_subset (map_zero Λ) b).trans hsb))
    · simp
    · intro q
      apply TendstoUniformly.tendstoUniformlyOn
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hΛpos : 0 < ‖Λ‖ + 1 := by positivity
      have hδ : 0 < ε / (‖Λ‖ + 1) := div_pos hε hΛpos
      filter_upwards [Metric.tendstoUniformly_iff.mp (hconv q) _ hδ] with k hk x
      have hD : iteratedFDeriv ℝ q
          ((ω k : TestFormOn U (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1)) x =
          Λ.compContinuousMultilinearMap
            (iteratedFDeriv ℝ q (a k) x - iteratedFDeriv ℝ q b x) := by
        have h1 : ((ω k : TestFormOn U (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1)) =
            Λ ∘ (a k - b) := by
          funext y
          exact (map_sub Λ (a k y) (b y)).symm
        have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k - b) := (ha k).sub hb
        rw [h1, Λ.iteratedFDeriv_comp_left hsub.contDiffAt
          (by exact_mod_cast le_top), iteratedFDeriv_sub_apply
          ((ha k).contDiffAt.of_le (by exact_mod_cast le_top))
          (hb.contDiffAt.of_le (by exact_mod_cast le_top))]
      have h0 : iteratedFDeriv ℝ q
          (((0 : TestFormOn U (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1))) x = 0 := by
        simp
      rw [hD, h0, dist_zero_left]
      calc ‖Λ.compContinuousMultilinearMap
              (iteratedFDeriv ℝ q (a k) x - iteratedFDeriv ℝ q b x)‖
          ≤ ‖Λ‖ * ‖iteratedFDeriv ℝ q (a k) x - iteratedFDeriv ℝ q b x‖ :=
            Λ.norm_compContinuousMultilinearMap_le _
        _ ≤ ‖Λ‖ * (ε / (‖Λ‖ + 1)) := by
            gcongr
            rw [← dist_eq_norm, dist_comm]
            exact (hk x).le
        _ < (‖Λ‖ + 1) * (ε / (‖Λ‖ + 1)) := mul_lt_mul_of_pos_right (lt_add_one _) hδ
        _ = ε := by field_simp
/-- **Step 3 of the proof of Simon Ch. 6, Theorem 2.34 (Constancy Theorem, pp. 142–143).**  Let
`B = B_ρ(x₀)` with `B̄_{ρ+ε}(x₀) ⊆ U` and let `φ` be `C^∞` with `spt φ ⊆ B̄_ε(0)` and the derivative
bounds `‖D^q(φ ∗ g)‖ ≤ C_q ∫ |g|`.  Then `F(f) = u(φ ∗ 1_B f)` is linear and `L¹(B)`-bounded.  Each
`φ ∗ 1_B f` is `C^∞` with support in the compact set `K = B̄_{ρ+ε}(x₀) ⊆ U`, so linearity follows
from that of `u`.  If no bound held, there would be `f_k` with `|F(f_k)| > (k + 1) ∫_B |f_k|`; then
`g_k = F(f_k)⁻¹ f_k` has `F(g_k) = 1` and `∫_B |g_k| ≤ 1 / (k + 1)`, so all derivatives of
`φ ∗ 1_B g_k` tend to `0` uniformly and continuity of `u` gives `1 = F(g_k) → u 0 = 0`. -/
theorem Submission.constancy_mollified_functional_l1_bounded : ∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ), (∀ a b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → u (a + b) = u a + u b) → (∀ (c : ℝ) (a : Eucl n → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → u (c • a) = c * u a) → (∀ (a : ℕ → Eucl n → ℝ) (b : Eucl n → ℝ) (K : Set (Eucl n)), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b))) → ∀ (x₀ : Eucl n) (ρ ε : ℝ), 0 < ρ → 0 < ε → closedBall x₀ (ρ + ε) ⊆ U → ∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ closedBall 0 ε → (∀ q : ℕ, ∃ C : ℝ, ∀ g : Eucl n → ℝ, Integrable g volume → ∀ x : Eucl n, ‖iteratedFDeriv ℝ q (convolution φ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ C * ∫ y, |g y| ∂volume) → (∀ f g : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → IntegrableOn g (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator (f + g)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) + u (convolution φ ((ball x₀ ρ).indicator g) (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ∧ (∀ (c : ℝ) (f : Eucl n → ℝ), IntegrableOn f (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator (c • f)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = c * u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ∧ ∃ C : ℝ, ∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → |u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume)| ≤ C * ∫ x in ball x₀ ρ, |f x| ∂volume := by
  intro n U u hadd hsmul hcont x₀ ρ ε hρ hε hU φ hφ hφc hφs hBd
  -- `K = B̄_{ρ+ε}(x₀)` is a compact subset of `U`.
  have hKc : IsCompact (closedBall x₀ (ρ + ε)) := isCompact_closedBall x₀ (ρ + ε)
  -- Step 1: for `f` integrable on `B`, `φ ∗ 1_B f` exists everywhere, is `C^∞` and has support
  -- in `K`, hence compact support.
  have hint : ∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume →
      Integrable ((ball x₀ ρ).indicator f) volume :=
    fun f hf => hf.integrable_indicator measurableSet_ball
  have hsmooth : ∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    fun f hf => hφc.contDiff_convolution_left _ hφ (hint f hf).locallyIntegrable
  have hexists : ∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume →
      ConvolutionExists φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    fun f hf => hφc.convolutionExists_left _ hφ.continuous (hint f hf).locallyIntegrable
  have hsupp : ∀ f : Eucl n → ℝ,
      tsupport (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        ⊆ closedBall x₀ (ρ + ε) := by
    intro f
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_add.mp (support_convolution_subset _ hx)
    have hs' : ‖s‖ ≤ ε := mem_closedBall_zero_iff.mp (hφs (subset_tsupport _ hs))
    have ht' : t ∈ ball x₀ ρ := Set.support_indicator_subset ht
    rw [mem_ball, dist_eq_norm] at ht'
    rw [mem_closedBall, dist_eq_norm, add_sub_assoc]
    exact (norm_add_le _ _).trans (by linarith)
  have hcs : ∀ f : Eucl n → ℝ,
      HasCompactSupport
        (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    fun f => hKc.of_isClosed_subset (isClosed_tsupport _) (hsupp f)
  -- Step 2: `F(f) = u(φ ∗ 1_B f)` is additive and homogeneous.
  have hFadd : ∀ f g : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume →
      IntegrableOn g (ball x₀ ρ) volume →
      u (convolution φ ((ball x₀ ρ).indicator (f + g)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
        u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) +
          u (convolution φ ((ball x₀ ρ).indicator g) (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    intro f g hf hg
    rw [Set.indicator_add', (hexists f hf).distrib_add (hexists g hg)]
    exact hadd _ _ (hsmooth f hf) (hcs f) ((hsupp f).trans hU) (hsmooth g hg) (hcs g)
      ((hsupp g).trans hU)
  have hFsmul : ∀ (c : ℝ) (f : Eucl n → ℝ), IntegrableOn f (ball x₀ ρ) volume →
      u (convolution φ ((ball x₀ ρ).indicator (c • f)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
        c * u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    intro c f hf
    have hind : (ball x₀ ρ).indicator (c • f) = c • (ball x₀ ρ).indicator f :=
      Set.indicator_const_smul (ball x₀ ρ) c f
    rw [hind, convolution_smul]
    exact hsmul c _ (hsmooth f hf) (hcs f) ((hsupp f).trans hU)
  -- Step 3: `u 0 = 0`, by homogeneity with `c = 0`.
  have hu0 : u 0 = 0 := by
    have h := hsmul 0 0 contDiff_zero_fun HasCompactSupport.zero (by simp)
    rwa [zero_smul, zero_mul] at h
  refine ⟨hFadd, hFsmul, ?_⟩
  -- Step 4: boundedness, by contradiction.  Otherwise pick `f_k` with
  -- `|F(f_k)| > (k + 1) ∫_B |f_k|`.
  by_contra hcon
  push Not at hcon
  choose f hfint hfbig using fun k : ℕ => hcon ((k : ℝ) + 1)
  set F : ℕ → ℝ := fun k =>
    u (convolution φ ((ball x₀ ρ).indicator (f k)) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
  have hL1nn : ∀ h : Eucl n → ℝ, 0 ≤ ∫ x in ball x₀ ρ, |h x| :=
    fun h => integral_nonneg fun _ => abs_nonneg _
  have hFne : ∀ k, F k ≠ 0 := by
    intro k hk
    have h1 := hfbig k
    have h2 : 0 ≤ ((k : ℝ) + 1) * ∫ x in ball x₀ ρ, |f k x| :=
      mul_nonneg (by positivity) (hL1nn _)
    change _ < |F k| at h1
    rw [hk, abs_zero] at h1
    linarith
  -- Normalize: `g_k = F(f_k)⁻¹ f_k` has `F(g_k) = 1` and `∫_B |g_k| ≤ 1 / (k + 1)`.
  set g : ℕ → Eucl n → ℝ := fun k => (F k)⁻¹ • f k with hgdef
  have hgint : ∀ k, IntegrableOn (g k) (ball x₀ ρ) volume := fun k => (hfint k).smul _
  have hFg : ∀ k,
      u (convolution φ ((ball x₀ ρ).indicator (g k)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = 1 :=
    fun k => by rw [hFsmul _ _ (hfint k)]; exact inv_mul_cancel₀ (hFne k)
  have hgL1 : ∀ k : ℕ, ∫ x in ball x₀ ρ, |g k x| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have heq : ∫ x in ball x₀ ρ, |g k x| = |F k|⁻¹ * ∫ x in ball x₀ ρ, |f k x| := by
      simp only [hgdef, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv]
      exact integral_const_mul _ _
    have hpos : 0 < |F k| := abs_pos.mpr (hFne k)
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [heq, inv_mul_le_iff₀ hpos, mul_one_div, le_div_iff₀ hk1]
    have := hfbig k
    change _ < |F k| at this
    linarith
  -- By (Bd), every derivative of `b_k = φ ∗ 1_B g_k` tends to `0` uniformly.
  have hunif : ∀ q : ℕ, TendstoUniformly
      (fun k x => iteratedFDeriv ℝ q
        (convolution φ ((ball x₀ ρ).indicator (g k)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x)
      (fun x => iteratedFDeriv ℝ q (0 : Eucl n → ℝ) x) atTop := by
    intro q
    obtain ⟨C, hC⟩ := hBd q
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    have hlim : Tendsto (fun k : ℕ => max C 0 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (max C 0)
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with k hk x
    have hzero : iteratedFDeriv ℝ q (0 : Eucl n → ℝ) x = 0 := by
      simp
    rw [hzero, dist_zero_left]
    have habs : ∫ y, |(ball x₀ ρ).indicator (g k) y| = ∫ y in ball x₀ ρ, |g k y| := by
      have hpt : (fun y => |(ball x₀ ρ).indicator (g k) y|) =
          (ball x₀ ρ).indicator (fun y => |g k y|) := by
        ext y
        by_cases hy : y ∈ ball x₀ ρ <;> simp [hy]
      rw [hpt, integral_indicator measurableSet_ball]
    calc ‖iteratedFDeriv ℝ q
          (convolution φ ((ball x₀ ρ).indicator (g k)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
        ≤ C * ∫ y, |(ball x₀ ρ).indicator (g k) y| := hC _ (hint _ (hgint k)) x
      _ = C * ∫ y in ball x₀ ρ, |g k y| := by rw [habs]
      _ ≤ max C 0 * ∫ y in ball x₀ ρ, |g k y| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hL1nn _)
      _ ≤ max C 0 * (1 / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hgL1 k) (le_max_right _ _)
      _ < δ := hk
  -- The continuity hypothesis gives `1 = F(g_k) → u 0 = 0`, a contradiction.
  have hlim := hcont
    (fun k => convolution φ ((ball x₀ ρ).indicator (g k)) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
    0 (closedBall x₀ (ρ + ε)) hKc hU (fun k => hsmooth _ (hgint k)) contDiff_zero_fun
    (fun k => hsupp _) (by simp) hunif
  simp only [hFg, hu0] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
/-- Simon Ch. 6, Proof of Theorem 2.34 (Constancy Theorem, pp. 142–143), display (2):
`∫ D_j a θ_ε dLⁿ = T(dω_j) = ∂T(ω_j) = 0`.  Here `u(D_j a) = 0` for every `a ∈ C_c^∞` with
`spt a ⊆ U` plays the role of `∂T = 0`, `φ` the role of the mollifier `ϕ_ε`, and `θ` represents
`f ↦ u(φ ∗ (1_B f))` on `B = B_ρ(x₀)` (display (1)).  For `a ∈ C_c^∞` with `spt a ⊆ B`, the
function `d = D_j a` is continuous with `spt d ⊆ spt a ⊆ B`; `φ ∗ a` is `C^∞` with compact support
and `spt (φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U`; and `D_j (φ ∗ a) = φ ∗ d = φ ∗ (1_B d)`.  Hence
`0 = u(D_j (φ ∗ a)) = ∫_B d θ = ∫ θ d`, the last step because `d θ` vanishes off `B`. -/
theorem Submission.constancy_mdc_weak_partials_vanish :
    ∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ),
      (∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
        tsupport a ⊆ U → ∀ j : Fin n,
          u (fun x => fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ))) = 0) →
      ∀ (x₀ : Eucl n) (ρ ε : ℝ), closedBall x₀ (ρ + ε) ⊆ U →
      ∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ closedBall 0 ε →
      ∀ θ : Eucl n → ℝ,
        (∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume →
          u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
            ∫ x in ball x₀ ρ, f x * θ x ∂volume) →
      ∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
        tsupport a ⊆ ball x₀ ρ →
      ∀ j : Fin n, ∫ x, θ x * fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ)) ∂volume = 0 := by
  intro n U u hu x₀ ρ ε hU φ hφ hφc hφs θ h1 a ha hac has j
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast le_top)
  set v : Eucl n := EuclideanSpace.single j (1 : ℝ) with hv
  set d : Eucl n → ℝ := fun x => fderiv ℝ a x v with hd
  -- Step 1: `d = D_j a` is continuous with `spt d ⊆ spt a ⊆ B`, so it is integrable, vanishes
  -- off `B`, and `1_B d = d`.
  have hdcont : Continuous d := (ha1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdsupp : tsupport d ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ v
  have hdc : HasCompactSupport d := hac.fderiv_apply ℝ v
  have hdint : Integrable d volume := hdcont.integrable_of_hasCompactSupport hdc
  have hdzero : ∀ x, x ∉ ball x₀ ρ → d x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (has (hdsupp h)))
  have hind : (ball x₀ ρ).indicator d = d :=
    Set.indicator_eq_self.2 ((subset_tsupport d).trans (hdsupp.trans has))
  -- Step 2: `φ ∗ a` is `C^∞` with compact support and `spt (φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U`, since
  -- `{φ ∗ a ≠ 0} ⊆ {φ ≠ 0} + {a ≠ 0} ⊆ B̄_ε(0) + B_ρ(x₀)`.
  have hφli : LocallyIntegrable φ volume := hφ.continuous.locallyIntegrable
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hφc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ
      ha.continuous.locallyIntegrable
  have hcs : HasCompactSupport (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hφc.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hac
  have hts : tsupport (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ U := by
    refine (closure_minimal ?_ isClosed_closedBall).trans hU
    intro x hx
    obtain ⟨s, hs, t, ht, rfl⟩ :=
      Set.mem_add.1 (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx)
    have hs' := hφs (subset_tsupport _ hs)
    have ht' := has (subset_tsupport _ ht)
    rw [mem_closedBall, dist_zero_right] at hs'
    rw [mem_ball, dist_eq_norm] at ht'
    rw [mem_closedBall, dist_eq_norm]
    calc ‖s + t - x₀‖ = ‖s + (t - x₀)‖ := by rw [add_sub_assoc]
      _ ≤ ‖s‖ + ‖t - x₀‖ := norm_add_le _ _
      _ ≤ ρ + ε := by linarith
  -- Step 3: the derivative falls on `a`: `D_j (φ ∗ a) = φ ∗ d = φ ∗ (1_B d)`.
  have hderiv : (fun x => fderiv ℝ (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v) =
      convolution φ ((ball x₀ ρ).indicator d) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    rw [hind]
    funext x
    rw [(hac.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφli ha1 x).fderiv]
    exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hφli (hac.fderiv ℝ)
      (ha1.continuous_fderiv one_ne_zero) x v
  -- Step 4: `0 = u(D_j (φ ∗ a)) = u(φ ∗ (1_B d)) = ∫_B d θ`, and `d θ` vanishes off `B`.
  have hu0 := hu _ hsm hcs hts j
  rw [← hv, hderiv, h1 d hdint.integrableOn] at hu0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball x₀ ρ)
    (fun x hx => by simp only [hd] at hdzero ⊢; rw [hdzero x hx, mul_zero])]
  simpa only [mul_comm] using hu0
/-- A smooth approximate identity on `ℝⁿ` (Simon Ch. 6, proof of 2.34, p. 143; Ch. 2, §2):
`ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)` for a smooth bump `0 ≤ h ≤ 1` with `h(0) = 1`,
`spt h ⊆ B_1(0)` and `I = ∫ h > 0`.  Each `ψ_k` is `C^∞`, nonnegative, of integral `1` and
supported in `B̄_{1/(k+1)}(0)`, and `0 ≤ ψ_k ≤ (k+1)ⁿ I⁻¹`.  For locally integrable `g` and every
Lebesgue point `x` of `g` (Simon Ch. 1, 3.17), `|(g ∗ ψ_k)(x) − g(x)| ≤ I⁻¹ Lⁿ(B_1(0)) ·
⨍_{B̄_{1/(k+1)}(x)} |g − g(x)| → 0`, so `g ∗ ψ_k → g` almost everywhere. -/
theorem Submission.constancy_mdc_smooth_approx_identity_ae_tendsto :
    ∀ n : ℕ, ∃ ψ : ℕ → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k : ℕ, tsupport (ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1))) ∧ (∀ k y, 0 ≤ ψ k y) ∧
      (∀ k, ∫ y, ψ k y ∂volume = 1) ∧
      ∀ g : Eucl n → ℝ, LocallyIntegrable g volume → ∀ᵐ x ∂volume,
        Tendsto (fun k => convolution g (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop
          (𝓝 (g x)) := by
  intro n
  -- A smooth bump `h` with `0 ≤ h ≤ 1`, `h 0 = 1` and `spt h ⊆ B_1(0)`; `I = ∫ h > 0`.
  obtain ⟨h, hts, hhc, hhs, hrange, h0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ball_mem_nhds (0 : Eucl n) one_pos)
  have hh0 : ∀ y, 0 ≤ h y := fun y => (hrange ⟨y, rfl⟩).1
  have hh1 : ∀ y, h y ≤ 1 := fun y => (hrange ⟨y, rfl⟩).2
  have hhcont : Continuous h := hhs.continuous
  have hhint : Integrable h volume := hhcont.integrable_of_hasCompactSupport hhc
  have hIpos : 0 < ∫ y, h y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => hh0 y) hhint]
    exact hhcont.isOpen_support.measure_pos volume ⟨0, by simp [Function.mem_support, h0]⟩
  set I := ∫ y, h y with hI
  have hzero : ∀ y : Eucl n, 1 ≤ ‖y‖ → h y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have := hts hy'
    rw [mem_ball, dist_zero_right] at this
    linarith
  -- The kernels `ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)`.
  have hs : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  set Ψ : ℕ → Eucl n → ℝ := fun k y => ((k : ℝ) + 1) ^ n * (I⁻¹ * h (((k : ℝ) + 1) • y))
    with hΨ
  have hΨsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ k) := fun k =>
    contDiff_const.mul (contDiff_const.mul (hhs.comp (contDiff_const_smul _)))
  have hΨzero : ∀ (k : ℕ) (y : Eucl n), 1 / ((k : ℝ) + 1) ≤ ‖y‖ → Ψ k y = 0 := by
    intro k y hy
    have h1 : 1 ≤ ‖((k : ℝ) + 1) • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hs k).le]
      rw [div_le_iff₀ (hs k)] at hy
      linarith
    simp only [hΨ, hzero _ h1, mul_zero]
  have hΨsupp : ∀ k : ℕ, tsupport (Ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1)) := by
    intro k
    refine closure_minimal ?_ isClosed_closedBall
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    exact hy (hΨzero k y hlt.le)
  have hΨc : ∀ k, HasCompactSupport (Ψ k) := fun k =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport _).trans (hΨsupp k))
  have hΨnn : ∀ k y, 0 ≤ Ψ k y := fun k y => by
    have := hh0 (((k : ℝ) + 1) • y)
    have := (hs k).le
    have := inv_nonneg.2 hIpos.le
    simp only [hΨ]
    positivity
  have hΨle : ∀ k y, Ψ k y ≤ ((k : ℝ) + 1) ^ n * I⁻¹ := fun k y => by
    simp only [hΨ]
    have hp : 0 ≤ ((k : ℝ) + 1) ^ n := by positivity
    have hIi : 0 ≤ I⁻¹ := inv_nonneg.2 hIpos.le
    have := hh1 (((k : ℝ) + 1) • y)
    calc ((k : ℝ) + 1) ^ n * (I⁻¹ * h (((k : ℝ) + 1) • y))
        ≤ ((k : ℝ) + 1) ^ n * (I⁻¹ * 1) := by gcongr
      _ = _ := by ring
  have hΨint : ∀ k, Integrable (Ψ k) volume := fun k =>
    (hΨsmooth k).continuous.integrable_of_hasCompactSupport (hΨc k)
  -- `∫ ψ_k = (k+1)ⁿ I⁻¹ (k+1)⁻ⁿ ∫ h = 1` by the linear change of variables `y ↦ (k+1) y`.
  have hΨone : ∀ k, ∫ y, Ψ k y = 1 := by
    intro k
    simp only [hΨ]
    rw [integral_const_mul, integral_const_mul, Measure.integral_comp_smul,
      finrank_euclideanSpace_fin]
    rw [smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < (((k : ℝ) + 1) ^ n)⁻¹), ← hI]
    field_simp
  refine ⟨Ψ, hΨsmooth, hΨc, hΨsupp, hΨnn, hΨone, ?_⟩
  intro g hg
  -- Lebesgue points: `⨍_{B̄_r(x)} |g − g(x)| → 0` as `r ↓ 0`, for a.e. `x`.
  have hleb :=
    IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Eucl n)) hg 1
  filter_upwards [hleb] with x hx
  set r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k, 0 < r k := fun k => by simp only [hr]; positivity
  have hrlim : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => hrpos k⟩
  have havg := hx (fun _ => x) r hrlim (Eventually.of_forall fun k => by
    rw [one_mul]; exact mem_closedBall_self (hrpos k).le)
  set ω := (volume : Measure (Eucl n)).real (ball 0 1) with hω
  have hωpos : 0 < ω := by
    rw [hω, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set C := I⁻¹ * ω with hC
  -- `|(g ∗ ψ_k)(x) − g(x)| ≤ C ⨍_{B̄_{1/(k+1)}(x)} |g − g(x)|` with `C = I⁻¹ Lⁿ(B_1(0))`.
  have hbound : ∀ k, ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ ≤
      C * ⨍ y in closedBall x (r k), ‖g y - g x‖ := by
    intro k
    set K := closedBall x (r k) with hK
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hconv : Integrable (fun t => g t * Ψ k (x - t)) volume := by
      have := (hΨc k).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hg
        (hΨsmooth k).continuous x
      simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using this
    have hconst : Integrable (fun t => g x * Ψ k (x - t)) volume :=
      ((hΨint k).comp_sub_left x).const_mul (g x)
    have hgx : g x = ∫ t, g x * Ψ k (x - t) := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun y => Ψ k y) volume x, hΨone k,
        mul_one]
    have hdiff : convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x =
        ∫ t, (g t - g x) * Ψ k (x - t) := by
      rw [convolution_def]
      conv_lhs => rw [hgx]
      rw [← integral_sub _ hconst]
      · congr 1
        funext t
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        ring
      · simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hconv
    have hoff : ∀ t, t ∉ K → ‖g t - g x‖ * Ψ k (x - t) = 0 := by
      intro t ht
      rw [hK, mem_closedBall, not_le, dist_eq_norm, ← norm_neg, neg_sub] at ht
      rw [hΨzero k (x - t) ht.le, mul_zero]
    have hgK : IntegrableOn g K volume := hg.integrableOn_isCompact hKc
    have hgxK : IntegrableOn (fun t => ‖g t - g x‖) K volume :=
      (hgK.sub (integrableOn_const (hKc.measure_lt_top.ne))).norm
    calc ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖
        = ‖∫ t, (g t - g x) * Ψ k (x - t)‖ := by rw [hdiff]
      _ ≤ ∫ t, ‖(g t - g x) * Ψ k (x - t)‖ := norm_integral_le_integral_norm _
      _ = ∫ t, ‖g t - g x‖ * Ψ k (x - t) := by
          congr 1
          funext t
          rw [norm_mul, Real.norm_of_nonneg (hΨnn k _)]
      _ = ∫ t in K, ‖g t - g x‖ * Ψ k (x - t) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
      _ ≤ ∫ t in K, ‖g t - g x‖ * (((k : ℝ) + 1) ^ n * I⁻¹) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hgxK.mul_const _)
            (Eventually.of_forall fun t => ?_)
          · exact mul_nonneg (norm_nonneg _) (hΨnn k _)
          · exact mul_le_mul_of_nonneg_left (hΨle k _) (norm_nonneg _)
      _ = (∫ t in K, ‖g t - g x‖) * (((k : ℝ) + 1) ^ n * I⁻¹) := integral_mul_const _ _
      _ = C * ⨍ y in K, ‖g y - g x‖ := by
          rw [setAverage_eq, smul_eq_mul, hC]
          have hKvol : (volume : Measure (Eucl n)).real K = r k ^ n * ω := by
            rw [measureReal_def, hK, Measure.addHaar_closedBall _ _ (hrpos k).le,
              finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
              hω, measureReal_def]
          rw [hKvol]
          simp only [hr]
          field_simp
          rw [mul_assoc, ← mul_pow, mul_one_div_cancel (hs k).ne', one_pow, mul_one]
  -- Squeeze: `0 ≤ |(g ∗ ψ_k)(x) − g(x)| ≤ C ⨍ … → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  simpa using havg.const_mul C

/-- Weak constancy on a ball (Simon Ch. 6, Theorem 2.34, printed proof p. 143): if `θ` is locally
integrable and `∫ θ D_j a = 0` for every `a ∈ C_c^∞(B_ρ(x₀))` and every `j`, then `θ` is a.e.
constant on `B_ρ(x₀)`.  The mollifications `θ ∗ ψ_k` have vanishing derivative on
`B_{ρ - 1/(k+1)}(x₀)`, hence are constant there, and they converge to `θ` a.e. -/
theorem Submission.constancy_mdc_ae_const_of_weak_partials_vanish :
    ∀ (n : ℕ) (θ : Eucl n → ℝ), LocallyIntegrable θ volume → ∀ (x₀ : Eucl n) (ρ : ℝ), 0 < ρ →
      (∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
        tsupport a ⊆ ball x₀ ρ → ∀ j : Fin n,
          ∫ x, θ x * fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ)) ∂volume = 0) →
      ∃ c : ℝ, ∀ᵐ x ∂volume.restrict (ball x₀ ρ), θ x = c := by
  intro n θ hθ x₀ ρ hρ hw
  -- Step 1: mollifiers `ψ k` with `tsupport (ψ k) ⊆ closedBall 0 (1 / (k + 1))` and
  -- `θ ∗ ψ k → θ` almost everywhere.
  obtain ⟨ψ, hψs, hψc, hψt, -, -, hψlim⟩ :=
    Submission.constancy_mdc_smooth_approx_identity_ae_tendsto n
  -- Steps 2–3: if `closedBall x (1 / (k + 1)) ⊆ ball x₀ ρ`, then `a = ψ k (x - ·)` is an
  -- admissible test function and `D(θ ∗ ψ k)(x) e_j = -∫ θ D_j a = 0` for every `j`.
  have hd : ∀ (k : ℕ) (x : Eucl n), closedBall x (1 / ((k : ℝ) + 1)) ⊆ ball x₀ ρ →
      fderiv ℝ (convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0 := by
    intro k x hx
    have hψ1 : ContDiff ℝ 1 (ψ k) := (hψs k).of_le (by exact_mod_cast le_top)
    let a : Eucl n → ℝ := fun y => ψ k (x - y)
    have ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a :=
      (hψs k).comp (contDiff_const.sub contDiff_id)
    have hac : HasCompactSupport a := (hψc k).comp_homeomorph (Homeomorph.subLeft x)
    have has : tsupport a ⊆ ball x₀ ρ := by
      refine (tsupport_comp_subset_preimage (ψ k) (continuous_const.sub continuous_id)).trans ?_
      intro y hy
      apply hx
      have hy' := hψt k hy
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hy'
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hy'
    have hda : ∀ y, fderiv ℝ a y = -(fderiv ℝ (ψ k) (x - y)) := by
      intro y
      have h1 : HasFDerivAt (ψ k) (fderiv ℝ (ψ k) (x - y)) (x - y) :=
        ((hψ1.differentiable one_ne_zero) (x - y)).hasFDerivAt
      have h2 : HasFDerivAt (fun y : Eucl n => x - y) (-ContinuousLinearMap.id ℝ (Eucl n)) y :=
        (hasFDerivAt_id y).const_sub x
      simpa [a, Function.comp_def] using (h1.comp y h2).fderiv
    rw [((hψc k).hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hθ hψ1 x).fderiv]
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun j => ?_
    rw [ContinuousLinearMap.coe_coe, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hθ
      ((hψc k).fderiv ℝ) (hψ1.continuous_fderiv one_ne_zero)]
    have hz := hw a ha hac has j
    simp only [hda, neg_apply, mul_neg, integral_neg, neg_eq_zero] at hz
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, LinearMap.zero_apply,
      ContinuousLinearMap.toLinearMap_zero]
    simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hz
  -- Step 4: `θ ∗ ψ k` has zero derivative on the convex open ball `ball x₀ (ρ - 1 / (k + 1))`,
  -- hence is constant there.
  have hconst : ∀ (k : ℕ) (x y : Eucl n), x ∈ ball x₀ (ρ - 1 / ((k : ℝ) + 1)) →
      y ∈ ball x₀ (ρ - 1 / ((k : ℝ) + 1)) →
      convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
        convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
    intro k x y hx hy
    have hdiff : Differentiable ℝ (convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
      ((hψc k).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hθ
        (hψs k)).differentiable (by simp)
    refine isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
      hdiff.differentiableOn ?_ hx hy
    intro z hz
    apply hd k z
    intro w hw'
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hw'
    calc dist w x₀ ≤ dist w z + dist z x₀ := dist_triangle _ _ _
      _ < ρ := by linarith
  -- Steps 5–6: pick `x₁ ∈ ball x₀ ρ` with `(θ ∗ ψ k)(x₁) → θ x₁`.  For a.e. `x ∈ ball x₀ ρ`,
  -- `(θ ∗ ψ k)(x) = (θ ∗ ψ k)(x₁)` for all large `k`, so `θ x = θ x₁`.
  have hlim := hψlim θ hθ
  have hpos : volume (ball x₀ ρ) ≠ 0 := (measure_ball_pos volume x₀ hρ).ne'
  obtain ⟨x₁, hx₁, hlim₁⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hlim)
  refine ⟨θ x₁, ?_⟩
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_ball] with x hx hxb
  apply tendsto_nhds_unique hx
  apply hlim₁.congr'
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have e1 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ρ - dist x₁ x₀ :=
    hr.eventually (gt_mem_nhds (by have := mem_ball.mp hx₁; linarith))
  have e2 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ρ - dist x x₀ :=
    hr.eventually (gt_mem_nhds (by have := mem_ball.mp hxb; linarith))
  filter_upwards [e1, e2] with k hk1 hk2
  exact hconst k x₁ x (by rw [mem_ball]; linarith) (by rw [mem_ball]; linarith)

/-- Simon Ch. 6, 2.34, printed display (2) and the conclusion that `θ_ε` is constant on
`B_ρ(x₀)`: a bounded measurable density `θ` of `f ↦ u(φ ∗ (1_B f))`, `B = B_ρ(x₀)`, is a.e. a
constant `c` on `B`, so `u(φ ∗ (1_B f)) = c ∫_B f`.  `θ` is locally integrable (measurable and
bounded), its weak coordinate derivatives vanish on `B`
(`Submission.constancy_mdc_weak_partials_vanish`), hence `θ = c` a.e. on `B`
(`Submission.constancy_mdc_ae_const_of_weak_partials_vanish`). -/
theorem Submission.constancy_mollified_density_const : ∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ), (∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ∀ j : Fin n, u (fun x => fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ))) = 0) → ∀ (x₀ : Eucl n) (ρ ε : ℝ), 0 < ρ → 0 < ε → closedBall x₀ (ρ + ε) ⊆ U → ∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ closedBall 0 ε → ∀ θ : Eucl n → ℝ, Measurable θ → (∃ M : ℝ, ∀ x, |θ x| ≤ M) → (∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = ∫ x in ball x₀ ρ, f x * θ x ∂volume) → ∃ c : ℝ, ∀ f : Eucl n → ℝ, IntegrableOn f (ball x₀ ρ) volume → u (convolution φ ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = c * ∫ x in ball x₀ ρ, f x ∂volume := by
  intro n U u hu x₀ ρ ε hρ _hε hU φ hφ hφc hφs θ hθm hθb h1
  obtain ⟨M, hM⟩ := hθb
  -- `θ` is measurable and bounded, hence integrable on every compact set.
  have hθli : LocallyIntegrable θ volume :=
    locallyIntegrable_iff.2 fun K hK =>
      Measure.integrableOn_of_bounded (M := M) hK.measure_lt_top.ne hθm.aestronglyMeasurable
        (Eventually.of_forall fun x => (Real.norm_eq_abs (θ x)).le.trans (hM x))
  -- Printed display (2): the weak coordinate derivatives of `θ` vanish on `B_ρ(x₀)`.
  have hw := Submission.constancy_mdc_weak_partials_vanish n U u hu x₀ ρ ε hU φ hφ hφc hφs θ h1
  -- Hence `θ = c` a.e. on `B_ρ(x₀)`.
  obtain ⟨c, hc⟩ :=
    Submission.constancy_mdc_ae_const_of_weak_partials_vanish n θ hθli x₀ ρ hρ hw
  -- `u(φ ∗ (1_B f)) = ∫_B f θ = ∫_B c f = c ∫_B f`.
  refine ⟨c, fun f hf => ?_⟩
  rw [h1 f hf, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hc] with x hx
  rw [hx, mul_comm]
/-- Simon Ch. 6, Theorem 2.34, Step 5 of the proof (p. 143, "letting ε ↓ 0"): let `u` be
sequentially continuous on C^∞ functions supported in a fixed compact `K ⊆ U` (condition (C)),
`B̄_R(x₀) ⊆ U`, and let continuous kernels `ψ_k` with `spt ψ_k ⊆ B̄_{r_k}(0)`, `ρ + r_k ≤ R`, satisfy
`D^q(ψ_k ∗ b) → D^q b` uniformly for every C^∞ compactly supported `b`.  If
`u(ψ_k ∗ (1_{B_ρ(x₀)} f)) = c_k ∫_{B_ρ(x₀)} f` for all `k` and all `f` integrable on `B_ρ(x₀)`,
then `u(b) = c₀ ∫ b` for one constant `c₀` and every C^∞ compactly supported `b` with
`spt b ⊆ B_ρ(x₀)`. -/
theorem Submission.constancy_local_of_mollified_const : ∀ (n : ℕ) (U : Set (Eucl n)) (u : (Eucl n → ℝ) → ℝ), (∀ (a : ℕ → Eucl n → ℝ) (b : Eucl n → ℝ) (K : Set (Eucl n)), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b))) → ∀ (x₀ : Eucl n) (ρ R : ℝ), 0 < ρ → closedBall x₀ R ⊆ U → ∀ (ψ : ℕ → Eucl n → ℝ) (r : ℕ → ℝ), (∀ k, Continuous (ψ k)) → (∀ k, tsupport (ψ k) ⊆ closedBall 0 (r k)) → (∀ k, 0 ≤ r k) → (∀ k, ρ + r k ≤ R) → (∀ b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → ∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → ∀ c : ℕ → ℝ, (∀ (k : ℕ) (f : Eucl n → ℝ), IntegrableOn f (ball x₀ ρ) volume → u (convolution (ψ k) ((ball x₀ ρ).indicator f) (ContinuousLinearMap.lsmul ℝ ℝ) volume) = c k * ∫ x in ball x₀ ρ, f x ∂volume) → ∃ c₀ : ℝ, ∀ b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ ball x₀ ρ → u b = c₀ * ∫ x, b x ∂volume := by
  intro n U u hC x₀ ρ R hρ hRU ψ r hψc hψs hr0 hrR hconv c hc
  -- Steps 1–3: for every C^∞ compactly supported `b` with `spt b ⊆ B_ρ(x₀)`,
  -- `c_k ∫ b = u(ψ_k ∗ b) → u(b)`.
  have key : ∀ b : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b →
      tsupport b ⊆ ball x₀ ρ →
        Tendsto (fun k => c k * ∫ x, b x ∂volume) atTop (𝓝 (u b)) := by
    intro b hb hbc hbs
    -- Step 1: `1_B b = b` and `∫_B b = ∫ b`, so `u(ψ_k ∗ b) = c_k ∫ b`.
    have hrep : ∀ k, u (convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
        c k * ∫ x, b x ∂volume := by
      intro k
      have hint : IntegrableOn b (ball x₀ ρ) volume :=
        (hb.continuous.integrable_of_hasCompactSupport hbc).integrableOn
      have hind : (ball x₀ ρ).indicator b = b :=
        Set.indicator_eq_self.2 ((subset_tsupport b).trans hbs)
      have hset : ∫ x in ball x₀ ρ, b x ∂volume = ∫ x, b x ∂volume :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
          image_eq_zero_of_notMem_tsupport fun h => hx (hbs h)
      have h := hc k b hint
      rwa [hind, hset] at h
    -- Step 2: `ψ_k ∗ b` is C^∞ with `spt (ψ_k ∗ b) ⊆ B̄_{ρ + r_k}(x₀) ⊆ K := B̄_R(x₀)`;
    -- also `spt b ⊆ K`.
    have hsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun k =>
      hbc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hψc k).locallyIntegrable hb
    have hsupp : ∀ k, tsupport (convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
        closedBall x₀ R := by
      intro k
      refine closure_minimal (fun x hx => ?_) isClosed_closedBall
      obtain ⟨s, hs, t, ht, rfl⟩ :=
        Set.mem_add.1 (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx)
      have h1 : ‖s‖ ≤ r k := mem_closedBall_zero_iff.1 (hψs k (subset_tsupport _ hs))
      have h2 : ‖t - x₀‖ < ρ := by
        have h := hbs (subset_tsupport _ ht)
        rwa [mem_ball, dist_eq_norm] at h
      rw [mem_closedBall, dist_eq_norm, add_sub_assoc]
      linarith [norm_add_le s (t - x₀), hrR k]
    have hbK : tsupport b ⊆ closedBall x₀ R :=
      hbs.trans (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith [hrR 0, hr0 0])))
    -- Step 3: the convergence hypothesis and (C) give `u(ψ_k ∗ b) → u(b)`.
    exact Tendsto.congr hrep
      (hC (fun k => convolution (ψ k) b (ContinuousLinearMap.lsmul ℝ ℝ) volume) b
        (closedBall x₀ R) (isCompact_closedBall x₀ R) hRU hsmooth hb hsupp hbK (hconv b hb hbc))
  -- Steps 4–5: the constants `c_k` converge, to `c₀ := u(b₀) / ∫ b₀` for any admissible `b₀`
  -- with `∫ b₀ ≠ 0`, and uniqueness of limits gives `u(b) = c₀ ∫ b`.  (If every admissible
  -- `b` has `∫ b = 0`, then `u(b) = lim c_k · 0 = 0` and any `c₀` works.)
  by_cases h : ∃ b₀ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b₀ ∧ HasCompactSupport b₀ ∧
      tsupport b₀ ⊆ ball x₀ ρ ∧ ∫ x, b₀ x ∂volume ≠ 0
  · obtain ⟨b₀, hb₀, hb₀c, hb₀s, hI⟩ := h
    refine ⟨u b₀ / ∫ x, b₀ x ∂volume, fun b hb hbc hbs => ?_⟩
    have hck : Tendsto c atTop (𝓝 (u b₀ / ∫ x, b₀ x ∂volume)) :=
      Tendsto.congr (fun k => mul_div_cancel_right₀ (c k) hI)
        ((key b₀ hb₀ hb₀c hb₀s).div_const _)
    exact tendsto_nhds_unique (key b hb hbc hbs) (hck.mul_const _)
  · push Not at h
    refine ⟨0, fun b hb hbc hbs => ?_⟩
    have h0 := h b hb hbc hbs
    have hlim := key b hb hbc hbs
    simp only [h0, mul_zero] at hlim ⊢
    exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
