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

/-- Properness transfer (fact (P)); "proper on `F`" means `f⁻¹(K) ∩ F` is compact for every
compact `K`.  (a) If `G` is proper on the closed set `F` and the continuous map `g` is `d`-close
to `G` on `F`, then `g⁻¹(K) ∩ F` is a closed subset of the compact set
`G⁻¹(cthickening d K) ∩ F`.  (b) The affine homotopy `H(y) = F₀(x) + s • (F₁(x) − F₀(x))`,
`y = (s, x)`, of two such maps stays in the closed `d`-ball about `G(x)` by convexity, so
`H⁻¹(K) ∩ ([0,1] × F)` is a closed subset of the image of the compact set
`[0,1] × (G⁻¹(cthickening d K) ∩ F)` under the continuous chart `(s, x) ↦ y`. -/
theorem Submission.dph_lpf_proper_transfer :
    (∀ (m m' : ℕ) (G g : Eucl m → Eucl m') (F : Set (Eucl m)) (d : ℝ), IsClosed F → Continuous g → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → (∀ x ∈ F, dist (g x) (G x) ≤ d) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact (g ⁻¹' K ∩ F)) ∧ (∀ (m m' : ℕ) (G F₀ F₁ : Eucl m → Eucl m') (F : Set (Eucl m)) (d : ℝ), IsClosed F → Continuous F₀ → Continuous F₁ → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → (∀ x ∈ F, dist (F₀ x) (G x) ≤ d) → (∀ x ∈ F, dist (F₁ x) (G x) ≤ d) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ F})) := by
  refine ⟨?_, ?_⟩
  · intro m m' G g F d hF hg hG hd K hK
    refine (hG _ (hK.cthickening (r := d))).of_isClosed_subset
      ((hK.isClosed.preimage hg).inter hF) ?_
    rintro x ⟨hxK, hxF⟩
    exact ⟨mem_cthickening_of_dist_le (G x) (g x) d K hxK ((dist_comm _ _).trans_le (hd x hxF)),
      hxF⟩
  · intro m m' G F₀ F₁ F d hF hF₀ hF₁ hG hd₀ hd₁ K hK
    set e := EuclideanSpace.equiv (Fin (m + 1)) ℝ
    set e' := EuclideanSpace.equiv (Fin m) ℝ
    -- The coordinates `s = t(y)`, `x = tl(y)` and the homotopy `H` are continuous.
    have ht : Continuous fun y : Eucl (m + 1) => e y 0 := (continuous_apply 0).comp e.continuous
    have htl : Continuous fun y : Eucl (m + 1) => e'.symm (Fin.tail (e y)) :=
      e'.symm.continuous.comp (continuous_pi fun i => (continuous_apply i.succ).comp e.continuous)
    have hH : Continuous fun y : Eucl (m + 1) => F₀ (e'.symm (Fin.tail (e y))) +
        e y 0 • (F₁ (e'.symm (Fin.tail (e y))) - F₀ (e'.symm (Fin.tail (e y)))) :=
      (hF₀.comp htl).add (ht.smul ((hF₁.comp htl).sub (hF₀.comp htl)))
    -- The inverse chart `(s, x) ↦ y` is continuous.
    have hc : Continuous fun p : ℝ × Eucl m => e.symm (Fin.cons p.1 (e' p.2) : Fin (m + 1) → ℝ) :=
      e.symm.continuous.comp
        (continuous_fst.finCons (A := fun _ => ℝ) (e'.continuous.comp continuous_snd))
    -- `H⁻¹(K) ∩ cyl(F)` is closed and lies in the chart image of
    -- `[0,1] × (G⁻¹(cthickening d K) ∩ F)`, which is compact.
    refine (((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
        (hG _ (hK.cthickening (r := d)))).image hc).of_isClosed_subset
      ((hK.isClosed.preimage hH).inter ((isClosed_Icc.preimage ht).inter (hF.preimage htl))) ?_
    rintro y ⟨hyK, hyt, hyF⟩
    refine ⟨(e y 0, e'.symm (Fin.tail (e y))), ⟨hyt, ?_, hyF⟩, ?_⟩
    · -- `H(y)` lies in the closed `d`-ball about `G(x)`, so `G(x) ∈ cthickening d K`.
      have hmem := (convex_closedBall (G (e'.symm (Fin.tail (e y)))) d).add_smul_sub_mem
        (mem_closedBall.2 (hd₀ _ hyF)) (mem_closedBall.2 (hd₁ _ hyF)) hyt
      exact mem_cthickening_of_dist_le _ _ d K hyK
        ((dist_comm _ _).trans_le (mem_closedBall.1 hmem))
    · show e.symm (Fin.cons (e y 0) (e' (e'.symm (Fin.tail (e y))))) = y
      rw [e'.apply_symm_apply, Fin.cons_self_tail, e.symm_apply_apply]

/-- **Reference smooth approximations near a closed set** (Simon Ch. 6, 2.28–2.29; Step 2 of the
Lipschitz push-forward).  Assume the smooth approximation statement (SA) of
`dph_lipschitz_smooth_approx`.  If `F` is closed, `G` is `Λ`-Lipschitz on `F_r` (`r > 0`) and
proper on `F`, (SA) with `A := F`, `δ := r` gives `C^∞` maps `Gₙ` with `‖DGₙ‖ ≤ Λ` on `F_(r/2)`
and `Gₙ → Ĝ` uniformly, where `Ĝ = G` on `F_r ⊇ F_(r/2)`.  So `Gₙ → G` uniformly on `F_(r/2)`,
eventually `dist (Gₙ x) (G x) ≤ 1` on `F`, and `dph_lpf_proper_transfer` (a) makes `Gₙ` proper
on `F`. -/
theorem Submission.dph_lpf_reference_sequence : (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ → LipschitzOnWith Λ G (thickening δ A) → ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧ (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧ TendstoUniformly Gj G' atTop ∧ (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧ ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m') (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε → (∀ x ∈ thickening ε A, G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) → ∀ i, i ∉ range α → G x i = z i) → (∀ y, (ω : DifferentialForm (Eucl m') k) y (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) → ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A, ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap (fderiv ℝ (Gj j) x) = 0) → (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) := by
  intro hSA m m' G Λ r F hr hF hG hprop
  -- 1. (SA) with `A := F`, `δ := r`.
  obtain ⟨G', Gj, L, -, hG'G, hsmooth, -, hconv, hderiv, -⟩ := hSA m m' G Λ F r hr hG
  -- 2. `F_(r/2) ⊆ F_r`, where `G' = G`, so `Gj → G` uniformly on `F_(r/2)`.
  have hsub : thickening (r / 2) F ⊆ thickening r F := thickening_mono (half_le_self hr.le) F
  have hconvG : TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) :=
    hconv.tendstoUniformlyOn.congr_right (hG'G.mono hsub)
  refine ⟨Gj, hsmooth, hderiv, hconvG, ?_⟩
  -- 3. Eventually `dist (G x) (Gj n x) < 1` on `F_(r/2) ⊇ F`.
  have hFsub : F ⊆ thickening (r / 2) F := self_subset_thickening (half_pos hr) F
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconvG 1 one_pos] with n hn
  -- 4. `Gj n` is continuous and `1`-close to `G` on `F`, hence proper on `F`.
  exact Submission.dph_lpf_proper_transfer.1 m m' G (Gj n) F 1 hF (hsmooth n).continuous hprop
    fun x hx => by
      rw [dist_comm]
      exact (hn x (hFsub hx)).le
/-- **The affine homotopy restricts to its ends and is smooth** (Simon Ch. 6, (2.26), p. 140:
`h(t, x) = f(x) + t (g(x) − f(x))`).  On `ℝ^{m+1}` write `t(y) = y₀` and `tl(y) = (y₁, …, y_m)`;
`G = F₀ ∘ tl + t • (F₁ ∘ tl − F₀ ∘ tl)`.  For `y = cons(s, x)`, `t(y) = s` and `tl(y) = x` hold
definitionally, so `G(cons(0, x)) = F₀(x)` and `G(cons(1, x)) = F₁(x)`.  The maps `t` and `tl` are
coordinate projections composed with continuous linear equivalences, hence `C^∞`, so `G` is `C^∞`
when `F₀` and `F₁` are. -/
theorem Submission.dph_lpf_cmp_affine_homotopy : ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m') (G : Eucl (m + 1) → Eucl m'), G = (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) → (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) = F₀ ∧ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) = F₁ ∧ (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) := by
  intro m m' F₀ F₁ G hG
  subst hG
  refine ⟨funext fun x => ?_, funext fun x => ?_, fun h₀ h₁ => ?_⟩
  -- `t(cons(0, x)) = 0` and `tl(cons(0, x)) = x` definitionally (`simp` does not see through
  -- `EuclideanSpace.equiv`, so restate the goal by `change`).
  · change F₀ x + (0 : ℝ) • (F₁ x - F₀ x) = F₀ x
    rw [zero_smul, add_zero]
  -- Likewise `t(cons(1, x)) = 1` and `tl(cons(1, x)) = x`.
  · change F₀ x + (1 : ℝ) • (F₁ x - F₀ x) = F₁ x
    rw [one_smul, add_sub_cancel]
  -- `Fin.tail` is `C^∞`: each of its coordinates `q ↦ q i.succ` is.
  · have htail : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) :=
      contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ
    -- `tl` is `C^∞`: compose with the continuous linear equivalences.
    have htl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Eucl (m + 1) =>
        (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) :=
      (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.comp
        (htail.comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).contDiff)
    -- `t` is `C^∞`: the coordinate `q ↦ q 0` composed with a continuous linear equivalence.
    have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Eucl (m + 1) =>
        EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 :=
      (contDiff_apply ℝ ℝ (0 : Fin (m + 1))).comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).contDiff
    exact (h₀.comp htl).add (ht.smul ((h₁.comp htl).sub (h₀.comp htl)))
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
/-- A current kills every test form whose support misses `spt T`: `tsupport ω` is a compact subset
of the zero region, so finitely many open `W ⊂⊂ U` on which `T` vanishes cover it, and a smooth
partition of unity `ψᵢ` on `tsupport ω` subordinate to them splits `ω = ∑ᵢ ψᵢ ω` into test forms
supported in those `W`. -/
theorem Submission.isoperimetric_apply_eq_zero_of_disjoint_support :
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

/-- Supports of boundaries, weak limits and linear combinations: `spt ∂Z ⊆ spt Z`; a weak limit of
currents supported in a closed `K` is supported in `K`; `spt Z ⊆ spt Z₁ ∪ spt Z₂` when
`Z = a Z₁ + b Z₂`.  In each case a point outside the claimed support lies in an open `W ⊂⊂ U` on
which the current vanishes, i.e. in its zero region. -/
theorem Submission.iwl_cr_support_lemmas :
    (∀ (P m : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (m + 1)),
      Z.boundary.support ⊆ Z.support) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P))
      (Zj : ℕ → GeometricCurrentOn U n) (Z : GeometricCurrentOn U n), IsClosed K →
      (∀ j, (Zj j).support ⊆ K) → WeaklyConvergesOn Zj Z → Z.support ⊆ K) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Z₁ Z₂ Z : GeometricCurrentOn U n) (a b : ℝ),
      (∀ ω : TestFormOn U n, Z ω = a * Z₁ ω + b * Z₂ ω) →
      Z.support ⊆ Z₁.support ∪ Z₂.support) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) If `Z` vanishes on an admissible `W`, so does `∂Z`: `∂Z φ = Z (dφ)` and
    -- `tsupport dφ ⊆ tsupport φ ⊆ W`.
    intro P m U Z x hx
    refine ⟨hx.1, fun hxZ => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
    refine Set.mem_sUnion.2 ⟨W, ⟨hWo, hWc, hWU, fun φ hφ => ?_⟩, hxW⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hφ)
  · -- (2) For `x ∈ spt Z \ K`, the ball `W = B(x, ε/2)` has `closure W ⊆ U \ K`.  A test form
    -- supported in `W` misses `K ⊇ spt (Zj j)`, so every `Zj j` kills it, and so does the limit.
    intro P n U hU K Zj Z hK hZj hconv x hx
    by_contra hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.sdiff hK) x ⟨hx.1, hxK⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ U \ K := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans sdiff_subset, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have h0 : ∀ j, Zj j ω = 0 := fun j =>
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U (Zj j) ω
          (Set.disjoint_left.2 fun y hy hyS => (hcl (subset_closure (hω hy))).2 (hZj j hyS))
      have hlim := hconv ω
      simp only [h0] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- (3) For `x ∈ spt Z` outside `spt Z₁ ∪ spt Z₂`, the ball `W = B(x, ε/2)` has `closure W`
    -- inside both zero regions and `U`, so `Z₁`, `Z₂` and hence `Z = a Z₁ + b Z₂` vanish on `W`.
    intro P n U hU Z₁ Z₂ Z a b hZ x hx
    by_contra hx12
    have h1 : x ∈ Z₁.zeroRegion := by
      by_contra h
      exact hx12 (Or.inl ⟨hx.1, h⟩)
    have h2 : x ∈ Z₂.zeroRegion := by
      by_contra h
      exact hx12 (Or.inr ⟨hx.1, h⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((Z₁.isOpen_zeroRegion.inter Z₂.isOpen_zeroRegion).inter hU) x ⟨⟨h1, h2⟩, hx.1⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ Z₁.zeroRegion ∩ Z₂.zeroRegion ∩ U := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans inter_subset_right, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have e1 : Z₁ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₁ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.1)
      have e2 : Z₂ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₂ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.2)
      rw [hZ ω, e1, e2]
      ring
/-- **Test forms have bounded Euclidean coefficient norm** (the finiteness of `sup_x |ω(x)|` behind
"Evidently (1), (2) give `P_k(ω) → T(ω)`" in the proof of Simon Ch. 6, 6.2, p. 169).
`x ↦ |ω(x)|` is continuous, since `α ↦ |α|` is the square root of a finite sum of squares of
evaluations, and has compact support, since `|0| = 0`.  A continuous compactly supported real
function is bounded by some `C₀ ≥ 0`, and `C = C₀ + 1` is positive. -/
theorem Submission.br_la_testForm_covectorNorm_bounded : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U n), ∃ C : ℝ, 0 < C ∧ ∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C := by
  intro P n U ω
  -- `ω` is smooth, hence continuous.
  have hω : Continuous (ω : DifferentialForm (Eucl P) n) := ω.property.1.1.continuous
  -- `x ↦ |ω(x)|` is continuous: a square root of a finite sum of squares of evaluations.
  have hcont : Continuous fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (hω.eval_const _).pow 2
    · exact continuous_const
  -- `|ω(x)| = 0` wherever `ω(x) = 0`, so `x ↦ |ω(x)|` inherits the compact support of `ω`.
  have hsupp : HasCompactSupport fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) := by
    refine ω.property.1.2.mono' fun x hx => subset_tsupport _ fun h => hx ?_
    simp [h]
  -- A continuous compactly supported function is bounded by some `C₀ ≥ |f(0)| ≥ 0`.
  obtain ⟨C₀, hC₀⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨C₀ + 1, by linarith [(norm_nonneg _).trans (hC₀ 0)], fun x => ?_⟩
  linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)),
    (Real.norm_eq_abs _).symm.trans_le (hC₀ x)]
/-- **Core estimate of the comparison lemma** (Simon Ch. 6, proof of 2.29, p. 141: the homotopy
formula 2.25 for the affine homotopy 2.26 and the mass bound 2.27 give
`|f_ε# T(ω) − f_δ# T(ω)| ≤ C sup |f_ε − f_δ| (Lip f)ⁿ`).  Assume the interval product (Prod) and
the homotopy formulas (E0), (E1) with the affine estimate (Aff).  For `X` with `M(X) < ∞` (and
`M(∂X) < ∞` if `k ≥ 1`), `ω` and `L ≥ 0`, everything entering `C₀` is chosen before the maps: `Z`
with `ProdChar(X, Z)`, the constant `c` of (Aff), `C₁ ≥ |dω|` and `B = M(X)`; for `k = j + 1` also
`Z′` with `ProdChar(∂X, Z′)`, `c′`, `C₂ ≥ |ω|` and `B′ = M(∂X)`.  For the affine homotopy
`H = H[F₀, F₁]`, the pull-backs `η′ = H^# dω`, `θ′ = H^# ω` near `[0, 1] × spt X` turn the homotopy
formula into `X(η₁) − X(η₀) = Z(η′) (+ Z′(θ′))`, and (Aff) bounds each term by
`c s L^k M(·) sup |·|`. -/
theorem Submission.dph_lpf_cmp_core_estimate : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (L : ℝ), 0 ≤ L → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s : ℝ) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → 0 ≤ s → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (F₀ x)).compContinuousLinearMap (fderiv ℝ F₀ x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (F₁ x)).compContinuousLinearMap (fderiv ℝ F₁ x)) → |X η₁ - X η₀| ≤ C₀ * s := by
  intro hProd hSH m m' k X hXm hbd ω L hL
  obtain ⟨hE0, hE1, hAff⟩ := hSH
  -- 1. Data that do not depend on the maps: `Z` with `ProdChar(X, Z)`, the constant `c` of (Aff),
  -- a bound `C₁` for `|dω|` and `B = M(X)`.
  obtain ⟨Z, hZ⟩ := hProd m k X hXm
  obtain ⟨c, hc0, hc⟩ := hAff m m' k
  obtain ⟨C₁, hC₁0, hC₁⟩ := Submission.br_la_testForm_covectorNorm_bounded m' (k + 1) univ
    (exteriorDerivativeTestOn univ k ω)
  obtain ⟨B, hB0, hXB⟩ : ∃ B : ℝ, 0 ≤ B ∧ X.mass ≤ ENNReal.ofReal B :=
    ⟨X.mass.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hXm.ne).ge⟩
  cases k with
  | zero =>
    -- 2. `k = 0`: `C₀ = c B C₁`.
    refine ⟨c * B * C₁, mul_nonneg (mul_nonneg hc0 hB0) hC₁0.le, ?_⟩
    intro F₀ F₁ O s η₀ η₁ hF₀ hF₁ hO hXO hs hdist hD₀ hD₁ hF₀p hHp hη₀ hη₁
    -- (i) The affine homotopy `H = H[F₀, F₁]` has ends `F₀`, `F₁` and is `C^∞`.
    set H : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))) with hH
    obtain ⟨hH₀, hH₁, hHs⟩ := Submission.dph_lpf_cmp_affine_homotopy m m' F₀ F₁ H hH
    have hHsm := hHs hF₀ hF₁
    -- (ii) `η′ = H^# dω` near `[0, 1] × spt X`, as `H` is proper there.
    obtain ⟨η', -, N, hN, hXN, -, -, hη', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (0 + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) (exteriorDerivativeTestOn univ 0 ω)
    -- (iii) The homotopy formula (E0), its end conditions rewritten by (i):
    -- `X(η₁) − X(η₀) = Z(η′)`.
    rw [hE0 m m' X Z H hXm hZ hHsm hHp ω η₀ η₁ η' (by rw [hH₀]; exact hη₀)
      (by rw [hH₁]; exact hη₁) ⟨N, hN, hXN, hη'⟩]
    -- (iv)–(v) The affine estimate (Aff) with `ψ = dω`: `|Z(η′)| ≤ c s L⁰ B C₁ = C₀ s`.
    calc |Z η'| ≤ c * s * L ^ 0 * B * C₁ :=
          hc X Z F₀ F₁ O s L B hs hL hB0 hXB hZ hF₀ hF₁ hO hXO hdist hD₀ hD₁ hF₀p
            (exteriorDerivativeTestOn univ 0 ω) C₁ η' hC₁ ⟨N, hN, hXN, hη'⟩
      _ = c * B * C₁ * s := by ring
  | succ j =>
    -- 3. `k = j + 1`, further data that do not depend on the maps: `B′ = M(∂X) < ∞`, `Z′` with
    -- `ProdChar(∂X, Z′)`, the constant `c′` of (Aff) in degree `j`, a bound `C₂` for `|ω|`, and
    -- `spt ∂X ⊆ spt X` with `spt ∂X` closed.
    have hbm : X.boundary.mass < ∞ := hbd j X rfl HEq.rfl
    obtain ⟨B', hB'0, hXB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧ X.boundary.mass ≤ ENNReal.ofReal B' :=
      ⟨X.boundary.mass.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hbm.ne).ge⟩
    obtain ⟨Z', hZ'⟩ := hProd m j X.boundary hbm
    obtain ⟨c', hc'0, hc'⟩ := hAff m m' j
    obtain ⟨C₂, hC₂0, hC₂⟩ := Submission.br_la_testForm_covectorNorm_bounded m' (j + 1) univ ω
    have hsub : X.boundary.support ⊆ X.support := Submission.iwl_cr_support_lemmas.1 m j univ X
    have hcl : IsClosed X.boundary.support := isClosed_univ.sdiff X.boundary.isOpen_zeroRegion
    refine ⟨c * L ^ (j + 1) * B * C₁ + c' * L ^ j * B' * C₂,
      add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (pow_nonneg hL _)) hB0) hC₁0.le)
        (mul_nonneg (mul_nonneg (mul_nonneg hc'0 (pow_nonneg hL _)) hB'0) hC₂0.le), ?_⟩
    intro F₀ F₁ O s η₀ η₁ hF₀ hF₁ hO hXO hs hdist hD₀ hD₁ hF₀p hHp hη₀ hη₁
    -- 4. The affine homotopy `H = H[F₀, F₁]`, as in 2(i).
    set H : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))) with hH
    obtain ⟨hH₀, hH₁, hHs⟩ := Submission.dph_lpf_cmp_affine_homotopy m m' F₀ F₁ H hH
    have hHsm := hHs hF₀ hF₁
    -- (i) `η′ = H^# dω` and `θ′ = H^# ω` near `[0, 1] × spt X`.
    obtain ⟨η', -, N, hN, hXN, -, -, hη', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (j + 1 + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) (exteriorDerivativeTestOn univ (j + 1) ω)
    obtain ⟨θ', -, N', hN', hXN', -, -, hθ', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (j + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) ω
    -- (ii) The homotopy formula (E1): `X(η₁) − X(η₀) = Z(η′) + Z′(θ′)`.
    rw [hE1 m m' j X Z Z' H hXm hZ hZ' hHsm hHp ω η₀ η₁ η' θ' (by rw [hH₀]; exact hη₀)
      (by rw [hH₁]; exact hη₁) ⟨N, hN, hXN, hη'⟩ ⟨N', hN', hXN', hθ'⟩]
    -- (iii) (Aff) for `X` with `ψ = dω`: `|Z(η′)| ≤ c s L^(j+1) B C₁`.
    have hest : |Z η'| ≤ c * s * L ^ (j + 1) * B * C₁ :=
      hc X Z F₀ F₁ O s L B hs hL hB0 hXB hZ hF₀ hF₁ hO hXO hdist hD₀ hD₁ hF₀p
        (exteriorDerivativeTestOn univ (j + 1) ω) C₁ η' hC₁ ⟨N, hN, hXN, hη'⟩
    -- (iv) `F₀` is proper on the closed subset `spt ∂X` of `spt X`.
    have hF₀p' : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.boundary.support) := by
      intro K hK
      have h := (hF₀p K hK).inter_right hcl
      rwa [inter_assoc, inter_eq_right.mpr hsub] at h
    -- (v) (Aff) for `∂X` with `ψ = ω`, as `[0, 1] × spt ∂X ⊆ [0, 1] × spt X ⊆ N′`:
    -- `|Z′(θ′)| ≤ c′ s L^j B′ C₂`.
    have hest' : |Z' θ'| ≤ c' * s * L ^ j * B' * C₂ :=
      hc' X.boundary Z' F₀ F₁ O s L B' hs hL hB'0 hXB' hZ' hF₀ hF₁ hO (hsub.trans hXO) hdist hD₀
        hD₁ hF₀p' ω C₂ θ' hC₂ ⟨N', hN', fun y hy => hXN' ⟨hy.1, hsub hy.2⟩, hθ'⟩
    -- (vi) Sum the two estimates.
    calc |Z η' + Z' θ'| ≤ |Z η'| + |Z' θ'| := abs_add_le _ _
      _ ≤ c * s * L ^ (j + 1) * B * C₁ + c' * s * L ^ j * B' * C₂ := add_le_add hest hest'
      _ = (c * L ^ (j + 1) * B * C₁ + c' * L ^ j * B' * C₂) * s := by ring
/-- Comparison lemma (Step 1 of the Lipschitz push-forward): if `C^∞` maps `Gₙ`, `G'ₙ` with
eventual derivative bounds `L`, `L'` near `spt X` both converge uniformly to a map `G` proper on
`spt X`, then pull-backs `ηₙ`, `η'ₙ` of `ω` compatible with `Gₙ`, `G'ₙ` near `spt X` satisfy
`X(η'ₙ) − X(ηₙ) → 0`.  For `ε > 0`, eventually `Gₙ` and `G'ₙ` are `ε`-close to `G` on
`O ∩ O' ⊇ spt X`; so `Gₙ` is proper on `spt X` and the affine homotopy between `Gₙ` and `G'ₙ` is
proper on `[0,1] × spt X` (properness transfer), `dist(G'ₙ, Gₙ) ≤ 2ε` on `O ∩ O'`, and the core
estimate gives `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε`, which is `< δ` for `ε = δ/(2C₀ + 1)`. -/
theorem Submission.dph_lpf_comparison : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) := by
  intro hProd hSH m m' k X G hXm hbd hG Gj Gj' O O' L L' hO hXO hGj hGjL hGjU hO' hXO' hGj'
    hGjL' hGjU' ω ηj ηj' hηj hηj'
  -- Step 1 (core estimate), with the common derivative bound `L'' = max (max L L') 0`: a
  -- constant `C₀ ≥ 0` that does not depend on the maps.
  obtain ⟨C₀, hC₀, hcore⟩ := Submission.dph_lpf_cmp_core_estimate hProd hSH m m' k X hXm hbd ω
    (max (max L L') 0) (le_max_right _ _)
  -- `spt X = univ \ zeroRegion X` is closed.
  have hXc : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- Step 4: `ε = δ / (2C₀ + 1)`.
  have hpos : 0 < 2 * C₀ + 1 := by linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (2 * C₀ + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ div_pos hδ hpos
  -- Step 2: eventually the derivative bounds, `ε`-closeness to `G` and the compatibilities hold.
  filter_upwards [hGjL, hGjL', Metric.tendstoUniformlyOn_iff.1 hGjU ε hε0,
    Metric.tendstoUniformlyOn_iff.1 hGjU' ε hε0, hηj, hηj'] with n hL hL' hd hd' hc hc'
  -- Step 3: `Gₙ` and `G'ₙ` are `ε`-close to `G` on `spt X`, so properness transfers to `Gₙ` on
  -- `spt X` and to the affine homotopy between them on `cyl(spt X)`.
  have hd₀ : ∀ x ∈ X.support, dist (Gj n x) (G x) ≤ ε := fun x hx =>
    (dist_comm _ _).trans_le (hd x (hXO hx)).le
  have hd₁ : ∀ x ∈ X.support, dist (Gj' n x) (G x) ≤ ε := fun x hx =>
    (dist_comm _ _).trans_le (hd' x (hXO' hx)).le
  have hest : |X (ηj' n) - X (ηj n)| ≤ C₀ * (2 * ε) :=
    hcore (Gj n) (Gj' n) (O ∩ O') (2 * ε) (ηj n) (ηj' n) (hGj n) (hGj' n) (hO.inter hO')
      (subset_inter hXO hXO') (by linarith)
      (fun x hx => by
        linarith [dist_triangle (Gj' n x) (G x) (Gj n x), dist_comm (Gj' n x) (G x),
          hd x hx.1, hd' x hx.2])
      (fun x hx => (hL x hx.1).trans ((le_max_left L L').trans (le_max_left _ 0)))
      (fun x hx => (hL' x hx.2).trans ((le_max_right L L').trans (le_max_left _ 0)))
      (Submission.dph_lpf_proper_transfer.1 m m' G (Gj n) X.support ε hXc (hGj n).continuous
        hG hd₀)
      (Submission.dph_lpf_proper_transfer.2 m m' G (Gj n) (Gj' n) X.support ε hXc
        (hGj n).continuous (hGj' n).continuous hG hd₀ hd₁)
      hc hc'
  -- `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε = δ · 2C₀/(2C₀ + 1) < δ`.
  rw [Real.dist_eq, sub_zero]
  calc |X (ηj' n) - X (ηj n)| ≤ C₀ * (2 * ε) := hest
    _ = 2 * C₀ * δ / (2 * C₀ + 1) := by rw [hε]; ring
    _ < δ := by
      rw [div_lt_iff₀ hpos]
      linarith
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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
