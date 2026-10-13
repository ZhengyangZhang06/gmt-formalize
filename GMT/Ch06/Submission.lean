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

/-- Geometry of an orthonormal frame `τ` in `ℝ^P`: with `π y = ∑ ⟪τᵢ, y⟫ τᵢ`, `p y = (⟪τᵢ, y⟫)ᵢ`
and `d y = ‖y − π y‖`, Pythagoras gives `‖y‖² = ‖p y‖² + d(y)²`; hence `‖p‖ ≤ 1`, `d` is
`1`-Lipschitz, `p` inverts `a ↦ ∑ aᵢ τᵢ`, `d = 0` on `span τ`, the cylinder
`{‖p‖ < 1, d < 3/4}` lies in `closedBall 0 (5/4) ⊆ B₂(0)`, and `p⁻¹(K) ∩ {d ≤ γ}` is a compact
subset of it for compact `K ⊆ B₁(0)` and `γ < 3/4`. -/
theorem Submission.ind_pi_frame_geometry :
    ∀ (P n : ℕ) (τ : Fin n → Eucl P) (p : Eucl P →L[ℝ] Eucl n) (d : Eucl P → ℝ), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → LipschitzWith 1 d ∧ (∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2) ∧ ‖p‖ ≤ 1 ∧ (∀ a : Eucl n, p (∑ i, a i • τ i) = a) ∧ (∀ i, p (τ i) = EuclideanSpace.single i (1 : ℝ)) ∧ (∀ z ∈ Submodule.span ℝ (Set.range τ), d z = 0) ∧ CompactlyContainedOpen {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (ball (0 : Eucl P) 2) ∧ ∀ γ : ℝ, γ < 3 / 4 → ∀ K : Set (Eucl n), IsCompact K → K ⊆ ball (0 : Eucl n) 1 → IsCompact (p ⁻¹' K ∩ {y | d y ≤ γ}) ∧ p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} := by
  intro P n τ p d hτ hp hd
  -- The orthogonal projection `π y = ∑ ⟪τᵢ, y⟫ τᵢ` onto `span τ`, so `d y = ‖y − π y‖`.
  obtain ⟨π, hπ⟩ : ∃ π : Eucl P → Eucl P, ∀ y, π y = ∑ i, inner ℝ (τ i) y • τ i :=
    ⟨_, fun _ => rfl⟩
  have hdπ : ∀ y, d y = ‖y - π y‖ := fun y => by rw [hd, hπ]
  -- Step 1: `⟪τⱼ, π y⟫ = ⟪τⱼ, y⟫`.
  have h1 : ∀ y j, inner ℝ (τ j) (π y) = inner ℝ (τ j) y := fun y j => by
    rw [hπ]
    exact hτ.inner_right_fintype (fun i => inner ℝ (τ i) y) j
  have hπinner : ∀ y v, inner ℝ (π y) v = ∑ i, inner ℝ (τ i) y * inner ℝ (τ i) v := by
    intro y v
    rw [hπ, sum_inner]
    simp only [real_inner_smul_left]
  -- Step 2: `π y ⊥ y − π y`.
  have h2 : ∀ y, inner ℝ (π y) (y - π y) = 0 := by
    intro y
    rw [hπinner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sub_right, h1, sub_self, mul_zero]
  -- Step 3: `‖p y‖² = ‖π y‖² = ∑ ⟪τᵢ, y⟫²` and Pythagoras.
  have hpπ : ∀ y, ‖p y‖ ^ 2 = ‖π y‖ ^ 2 := by
    intro y
    rw [EuclideanSpace.real_norm_sq_eq, ← real_inner_self_eq_norm_sq, hπinner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, hp, sq]
  have hb : ∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2 := by
    intro y
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (h2 y)
    rw [add_sub_cancel] at h
    rw [hpπ, hdπ, sq, sq, sq, h]
  -- Step 4: `0 ≤ d y ≤ ‖y‖` and `‖p y‖ ≤ ‖y‖`.
  have hd0 : ∀ y, 0 ≤ d y := fun y => by rw [hdπ]; exact norm_nonneg _
  have hdle : ∀ y, d y ≤ ‖y‖ := by
    intro y
    have := hb y
    nlinarith [hd0 y, norm_nonneg y, sq_nonneg ‖p y‖]
  have hple : ∀ y, ‖p y‖ ≤ ‖y‖ := by
    intro y
    have := hb y
    nlinarith [norm_nonneg (p y), norm_nonneg y, sq_nonneg (d y)]
  -- Step 5: `π` is additive, so `d x ≤ d y + d (x − y) ≤ d y + dist x y`.
  have hπsub : ∀ x y, π (x - y) = π x - π y := by
    intro x y
    simp only [hπ, inner_sub_right, sub_smul, Finset.sum_sub_distrib]
  have hLip : LipschitzWith 1 d := by
    refine LipschitzWith.of_le_add fun x y => ?_
    have e : x - π x = (y - π y) + ((x - y) - π (x - y)) := by rw [hπsub]; abel
    calc d x = ‖(y - π y) + ((x - y) - π (x - y))‖ := by rw [hdπ, e]
      _ ≤ ‖y - π y‖ + ‖(x - y) - π (x - y)‖ := norm_add_le _ _
      _ = d y + d (x - y) := by rw [hdπ, hdπ]
      _ ≤ d y + ‖x - y‖ := by gcongr; exact hdle _
      _ = d y + dist x y := by rw [dist_eq_norm]
  -- The cylinder `{‖p‖ ≤ 1, d ≤ 3/4}` lies in `closedBall 0 (5/4)`.
  have hball : ∀ y, ‖p y‖ ≤ 1 → d y ≤ 3 / 4 → y ∈ closedBall (0 : Eucl P) (5 / 4) := by
    intro y hpy hdy
    rw [mem_closedBall_zero_iff]
    have h := hb y
    have hp0 := norm_nonneg (p y)
    have hd0' := hd0 y
    nlinarith [norm_nonneg y]
  refine ⟨hLip, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (c) `‖p‖ ≤ 1`.
  · exact p.opNorm_le_bound zero_le_one fun y => by rw [one_mul]; exact hple y
  -- (d) `p (∑ aᵢ τᵢ) = a`.
  · intro a
    ext j
    rw [hp]
    exact hτ.inner_right_fintype (fun i => a i) j
  -- (e) `p τᵢ = eᵢ`.
  · intro i
    ext j
    rw [hp, PiLp.single_apply, orthonormal_iff_ite.mp hτ j i]
  -- (f) `d = 0` on `span τ`.
  · intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
    have hc : ∀ i, inner ℝ (τ i) (∑ j, c j • τ j) = c i := fun i => hτ.inner_right_fintype c i
    rw [hd]
    simp only [hc, sub_self, norm_zero]
  -- (g) `{‖p‖ < 1, d < 3/4} ⊂⊂ B₂(0)`.
  · have hcl : closure {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ⊆ closedBall (0 : Eucl P) (5 / 4) := by
      refine (closure_minimal (t := {y : Eucl P | ‖p y‖ ≤ 1 ∧ d y ≤ 3 / 4})
        (fun y hy => ⟨hy.1.le, hy.2.le⟩) ?_).trans fun y hy => hball y hy.1 hy.2
      exact (isClosed_le p.continuous.norm continuous_const).inter
        (isClosed_le hLip.continuous continuous_const)
    refine ⟨?_, ?_, ?_⟩
    · exact (isOpen_lt p.continuous.norm continuous_const).inter
        (isOpen_lt hLip.continuous continuous_const)
    · exact (isCompact_closedBall (0 : Eucl P) (5 / 4)).of_isClosed_subset isClosed_closure hcl
    · exact hcl.trans (closedBall_subset_ball (by norm_num))
  -- (h) `p⁻¹(K) ∩ {d ≤ γ}` is compact and lies in the cylinder.
  · intro γ hγ K hK hKB
    have hsub : p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} := by
      intro y hy
      exact ⟨mem_ball_zero_iff.mp (hKB hy.1), lt_of_le_of_lt hy.2 hγ⟩
    refine ⟨?_, hsub⟩
    refine (isCompact_closedBall (0 : Eucl P) (5 / 4)).of_isClosed_subset ?_
      fun y hy => hball y (hsub hy).1.le (hsub hy).2.le
    exact (hK.isClosed.preimage p.continuous).inter (isClosed_le hLip.continuous continuous_const)
/-- Simon Ch. 6, proof of 8.2: for an orthonormal frame `τ₁, …, τₙ` of `Q = span τ ⊆ ℝ^P`, the
parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is a linear isometry `ℝⁿ → ℝ^P` with range `Q`, so it pushes
Lebesgue measure on `ℝⁿ` (`= Hⁿ`) forward to `Hⁿ ⌞ Q`.  As a closed, hence measurable, embedding
it gives `∫_Q h dHⁿ = ∫_{ℝⁿ} h(ι(a)) da` for every `h`, and `(Hⁿ ⌞ Q)(K) = Lⁿ(ι⁻¹ K) < ∞` for
compact `K`. -/
theorem Submission.ind_pi_span_integral :
    ∀ (P n : ℕ) (τ : Fin n → Eucl P), Orthonormal ℝ τ → (∀ h : Eucl P → ℝ, ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), h z ∂(μHE[n] : Measure (Eucl P)) = ∫ a : Eucl n, h (∑ i, a i • τ i)) ∧ ∀ K : Set (Eucl P), IsCompact K → ((μHE[n] : Measure (Eucl P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Eucl P))) K < ∞ := by
  intro P n τ hτ
  -- The parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is linear.
  let ι : Eucl n →ₗ[ℝ] Eucl P :=
    { toFun := fun a => ∑ i, a i • τ i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.smul_sum, smul_smul] }
  have hι : ∀ a : Eucl n, ι a = ∑ i, a i • τ i := fun a => rfl
  -- `ι` is an isometry: `‖ι a‖² = ∑ᵢ aᵢ² = ‖a‖²` by orthonormality.
  have hiso : Isometry ι := by
    refine AddMonoidHomClass.isometry_of_norm ι fun a => ?_
    have hsq : ‖ι a‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [hι, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  -- `range ι = span τ`.
  have hrange : Set.range ι = (Submodule.span ℝ (Set.range τ) : Set (Eucl P)) := by
    ext z
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨fun i => a i, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨WithLp.toLp 2 c, by simp [hι]⟩
  -- `ι` is a closed, hence measurable, embedding.
  have hemb : MeasurableEmbedding ι := hiso.isClosedEmbedding.measurableEmbedding
  -- `ι` pushes Lebesgue measure `= Hⁿ` on `ℝⁿ` forward to `Hⁿ ⌞ span τ`.
  have hmap : (volume : Measure (Eucl n)).map ι =
      (μHE[n] : Measure (Eucl P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Eucl P)) := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, hiso.map_euclideanHausdorffMeasure,
      hrange]
  refine ⟨fun h => ?_, fun K hK => ?_⟩
  · rw [← hmap, hemb.integral_map]
    rfl
  · rw [← hmap, hemb.map_apply]
    exact (hiso.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
/-- Simon Ch. 6, (2.7) (p. 136) for a constant `n`-vector: if `μ` is finite on compact sets and
`w ∈ Λₙ(ℝ^P)`, then `T(ω) = ∫ ⟨ω(x), w⟩ dμ(x)` defines a current `T ∈ 𝒟ₙ(U)` with
representation `(μ, w)`. -/
theorem Submission.ind_pi_constant_vector_current :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (w : NVector (Eucl P) n),
      (∀ K : Set (Eucl P), IsCompact K → μ K < ∞) →
      ∃ T : GeometricCurrentOn U n, IsMeasureRepresentation T μ (fun _ => w) := by
  intro P n U μ w hμ
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ K hK⟩
  -- `x ↦ ⟨ω(x), w⟩` is continuous with compact support (`w 0 = 0`), hence `μ`-integrable.
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => w ((ω : DifferentialForm (Eucl P) n) x)) μ := fun ω =>
    (w.continuous.comp ω.property.1.1.continuous).integrable_of_hasCompactSupport
      (ω.property.1.2.comp_left (map_zero w))
  -- The linear functional `L(ω) = ∫ ⟨ω, w⟩ dμ`.
  let L : CurrentOn U n :=
    { toFun := fun ω => ∫ x, w ((ω : DifferentialForm (Eucl P) n) x) ∂μ
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => ⟨hint ω, rfl⟩⟩
  -- Sequential continuity: the `ω_j` are supported in one compact `K` and `ω_j → 0` uniformly
  -- on `K`, so `|L(ω_j)| ≤ ‖w‖ · sup_K ‖ω_j‖ · μ(K) → 0`.
  obtain ⟨K, hK, -, hsupp, -, hderiv⟩ := hωs
  have hunif := Metric.tendstoUniformlyOn_iff.1 (hderiv 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hm : 0 ≤ μ.real K := measureReal_nonneg
  have hC : 0 < ‖w‖ * μ.real K + 1 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / (‖w‖ * μ.real K + 1)) (div_pos hε hC))
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_zero_right]
  change ‖∫ x, w ((ωs j : DifferentialForm (Eucl P) n) x) ∂μ‖ < ε
  -- The integrand vanishes off `K ⊇ tsupport ω_j`.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h), map_zero]]
  -- On `K`, `|⟨ω_j(x), w⟩| ≤ ‖w‖ ‖ω_j(x)‖ ≤ ‖w‖ · ε / (‖w‖ μ(K) + 1)`.
  have hbound : ∀ x ∈ K, ‖w ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
      ‖w‖ * (ε / (‖w‖ * μ.real K + 1)) := by
    intro x hx
    have h := (hN j hj x hx).le
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      Function.comp_apply, LinearIsometryEquiv.dist_map, ZeroMemClass.coe_zero, Pi.zero_apply,
      dist_zero_left] at h
    exact (w.le_opNorm _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg w))
  refine (norm_setIntegral_le_of_norm_le_const (hμ K hK) hbound).trans_lt ?_
  rw [show ‖w‖ * (ε / (‖w‖ * μ.real K + 1)) * μ.real K =
      ε * (‖w‖ * μ.real K / (‖w‖ * μ.real K + 1)) by ring]
  exact mul_lt_of_lt_one_right hε ((div_lt_one hC).2 (lt_add_one _))

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
