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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
