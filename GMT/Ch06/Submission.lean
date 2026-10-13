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

/-- An orthonormal `n`-frame in `ℝⁿ` has simple `n`-vector `±e₁ ∧ ⋯ ∧ eₙ` (Simon Ch. 6, 3.1 in top
dimension: an orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` is `±e₁ ∧ ⋯ ∧ eₙ`, so `⟨ω, ξ⟩ = ±a` for
`ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, as in the proof of 8.2, p. 179).  `τ` is linearly independent with
`n = dim ℝⁿ` members, hence an orthonormal basis of `ℝⁿ`, as is the standard basis `e`.  An
`n`-covector `α` is an alternating `n`-form on `ℝⁿ`, so `α(τ) = α(e) det_e(τ)`
(`AlternatingMap.eq_smul_basis_det`), and `det_e(τ) = ±1` because the change of basis between
orthonormal bases is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.ind_top_orthonormal_frame_sign :
    ∀ (n : ℕ) (τ : Fin n → Eucl n), Orthonormal ℝ τ →
      simpleNVector τ = simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) ∨
        simpleNVector τ = -simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro n τ hτ
  -- Step 1: `τ` spans `ℝⁿ` (`n = 0` included).
  have hspan : Submodule.span ℝ (range τ) = ⊤ :=
    hτ.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  -- Step 2: `τ` and the standard basis `e` are orthonormal bases `bτ`, `be` of `ℝⁿ`.
  let bτ : OrthonormalBasis (Fin n) ℝ (Eucl n) := OrthonormalBasis.mk hτ hspan.ge
  let be : OrthonormalBasis (Fin n) ℝ (Eucl n) := EuclideanSpace.basisFun (Fin n) ℝ
  have hbτ : ⇑bτ = τ := OrthonormalBasis.coe_mk hτ hspan.ge
  have hbe : ⇑be.toBasis = fun i => EuclideanSpace.single i (1 : ℝ) := by
    funext i
    simp [be]
  -- Step 3: `det_e(τ) = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : be.toBasis.det τ = 1 ∨ be.toBasis.det τ = -1 := by
    simpa only [hbτ] using be.det_to_matrix_orthonormalBasis_real bτ
  -- Step 4: an `n`-covector `α` is `α(e) • det_e`, so `α(τ) = α(e) * det_e(τ)`.
  have key : ∀ α : Covector (Eucl n) n,
      α τ = α (fun i => EuclideanSpace.single i (1 : ℝ)) * be.toBasis.det τ := by
    intro α
    have h := DFunLike.congr_fun (α.toAlternatingMap.eq_smul_basis_det be.toBasis) τ
    rw [AlternatingMap.smul_apply, smul_eq_mul, hbe] at h
    exact h
  -- Step 5: extensionality, as `simpleNVector v α = α v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun α => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key α, hd, mul_one]
  · right
    refine ContinuousLinearMap.ext fun α => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key α, hd, mul_neg_one]
/-- Densities of top-degree test-form functionals on an open set are unique a.e. (Simon Ch. 6, end
of the Proof of 8.2, p. 179: `θ ≡ θ(x)` in `B₁ⁿ(0)`, top-dimensional currents acting by
`ω = a dx¹ ∧ ⋯ ∧ dxⁿ ↦ ∫ a θ dLⁿ` as in 2.35 (∗)).  For `a ∈ C_c^∞(U)`, the form `ω = a • vol`
with `vol = dx¹ ∧ ⋯ ∧ dxⁿ` is a test form on `U` with `ω(x)(e₁, …, eₙ) = a(x)`
(`wedgeCovectors_apply_det`: `vol(e) = det 1 = 1`), so the hypothesis gives
`∫ a (u - v) = ∫_U u a - ∫_U v a = 0`.  As `u - v` is locally integrable on the open set `U`, the
fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `u = v` a.e. on `U`. -/
theorem Submission.ind_top_form_density_ae_unique :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (u v : Eucl (m + 1) → ℝ), IsOpen U →
      (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) →
      (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn v K volume) →
      (∀ ω : TestFormOn U (m + 1),
        ∫ x in U, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume =
        ∫ x in U, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) →
      ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x = v x := by
  intro m U u v hU hu hv h
  -- Step 1: the volume covector `vol = dx¹ ∧ ⋯ ∧ dxⁿ` has `vol(e) = det 1 = 1`.
  obtain ⟨vol, hvol⟩ : ∃ vol : Covector (Eucl (m + 1)) (m + 1),
      vol (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), ?_⟩
    rw [wedgeCovectors_apply_det]
    have hI : (Matrix.of fun i j =>
        (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ) (EuclideanSpace.single j (1 : ℝ))) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    rw [hI, Matrix.det_one]
  -- Step 2: `u - v` is integrable on compact subsets of the open set `U`, so it is locally
  -- integrable on `U`.
  have hloc : LocallyIntegrableOn (fun x => u x - v x) U volume := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    exact (hu K hK hKU).sub (hv K hK hKU)
  -- Step 3: the fundamental lemma; it remains to show `∫ a • (u - v) = 0` for `a ∈ C_c^∞(U)`.
  have key : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x - v x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun a ha ha_cs ha_sub => ?_
    -- Step 4: `ω = a • vol` is a test form on `U` with `ω(x)(e) = a(x)`.
    let ω : TestFormOn U (m + 1) :=
      ⟨fun x => a x • vol,
        ⟨⟨ha.smul contDiff_const, ha_cs.smul_right⟩,
          (tsupport_smul_subset_left _ _).trans ha_sub⟩⟩
    have hω : ∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) = a x := by
      intro x
      simp [ω, hvol]
    -- Step 5: the hypothesis for `ω` reads `∫_U u a = ∫_U v a`.
    have hua := h ω
    simp only [hω] at hua
    -- Step 6: `w a` is integrable for `w ∈ {u, v}`: it is integrable on the compact set
    -- `tsupport a ⊆ U` and vanishes outside it.
    have hK : IsCompact (tsupport a) := ha_cs
    have hint : ∀ w : Eucl (m + 1) → ℝ,
        (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn w K volume) →
        IntegrableOn (fun x => w x * a x) U volume := by
      intro w hw
      have h1 : IntegrableOn (fun x => w x * a x) (tsupport a) volume :=
        (hw _ hK ha_sub).mul_continuousOn ha.continuous.continuousOn hK
      have h2 : Integrable (fun x => w x * a x) volume := by
        rw [← integrableOn_iff_integrable_of_support_subset]
        · exact h1
        · intro x hx
          apply subset_tsupport
          intro hax
          apply hx
          simp [hax]
      exact h2.integrableOn
    -- Step 7: `a = 0` off `U`, so `∫ a • (u - v) = ∫_U u a - ∫_U v a = 0`.
    have hzero : ∀ x, x ∉ U → a x • (u x - v x) = 0 := by
      intro x hx
      have : a x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (ha_sub hx'))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hsplit : ∀ x, a x • (u x - v x) = u x * a x - v x * a x := by
      intro x
      simp only [smul_eq_mul]
      ring
    simp only [hsplit]
    rw [integral_sub (hint u hu) (hint v hv), hua, sub_self]
  -- Step 8: conclusion.
  filter_upwards [key] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-- A top-dimensional integer multiplicity current has an integer density (Simon Ch. 6, 2.35 (∗),
`T(ω) = ∫ aθ dLⁿ` for `ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, with `θ` integer-valued as at the end of the Proof of
8.2, p. 179).  Write `X = τ(M, θ, ξ)` in `U ⊆ ℝⁿ`, `n = m + 1`, and `e = (e₁, …, eₙ)`; on `ℝⁿ`,
`Hⁿ = μHE[n]` is Lebesgue measure.  By `Submission.ind_top_orthonormal_frame_sign`,
`ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`, so `ξ(x)(α) = σ(x) α(e)` with the sign
`σ(x) = ξ(x)(dx¹ ∧ ⋯ ∧ dxⁿ) = ±1`.  The density is `u = θσ` on `M` and `u = 0` off `M`. -/
theorem Submission.ind_top_dim_integer_density :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (X : GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity X → ∃ u : Eucl (m + 1) → ℝ,
        (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∃ k : ℤ, u x = k) ∧
        (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) ∧
        ∀ ω : TestFormOn U (m + 1), X ω = ∫ x in U, u x *
          (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
            (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume := by
  intro m U X hX
  -- Step 1: `X = τ(M, θ, ξ)` with `θ` integer-valued on `M`; `μHE[m + 1]` is `volume`.
  obtain ⟨M, θ, ξ, hT, hθ, hXω⟩ := hX
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  have hM : NullMeasurableSet M volume := by
    simpa only [hvol] using hT.nullMeasurableSet
  have hξ : AEStronglyMeasurable ξ (volume.restrict M) := by
    simpa only [hvol] using hT.aestronglyMeasurable
  have horients := hT.orients
  rw [hvol] at horients
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- Step 2: the volume covector `vol = dx¹ ∧ ⋯ ∧ dxⁿ` has `vol(e) = det 1 = 1`.
  set vol : Covector (Eucl (m + 1)) (m + 1) :=
    wedgeCovectors (m + 1) fun j => EuclideanSpace.proj j with hvol_def
  have hvol_e : vol e = 1 := by
    rw [hvol_def, wedgeCovectors_apply_det]
    convert Matrix.det_one (n := Fin (m + 1)) (R := ℝ)
    ext i j
    simp [he, Matrix.one_apply]
  -- Step 3: `ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`.
  have hsign : ∀ᵐ x ∂volume.restrict M, ξ x = simpleNVector e ∨ ξ x = -simpleNVector e := by
    filter_upwards [horients] with x hx
    obtain ⟨τ, hτ, -, hξτ⟩ := hx
    rcases Submission.ind_top_orthonormal_frame_sign (m + 1) τ hτ with h | h <;>
      rcases hξτ with hξτ | hξτ
    · exact Or.inl (hξτ.trans h)
    · exact Or.inr (by rw [hξτ, h])
    · exact Or.inr (hξτ.trans h)
    · refine Or.inl (ContinuousLinearMap.ext fun α => ?_)
      rw [hξτ, _root_.neg_apply, h, _root_.neg_apply, neg_neg]
  -- Step 4: the sign `σ(x) = ξ(x)(vol)`; a.e. on `M`, `σ = ±1` and `ξ(x)(α) = σ(x) α(e)`.
  set σ : Eucl (m + 1) → ℝ := fun x => ξ x vol
  have hσm : AEStronglyMeasurable σ (volume.restrict M) :=
    (continuous_eval_const vol).comp_aestronglyMeasurable hξ
  have hσ : ∀ᵐ x ∂volume.restrict M, (σ x = 1 ∨ σ x = -1) ∧
      ∀ α : Covector (Eucl (m + 1)) (m + 1), ξ x α = σ x * α e := by
    filter_upwards [hsign] with x hx
    rcases hx with hx | hx
    · have h1 : σ x = 1 := by
        show ξ x vol = 1
        rw [hx, simpleNVector_apply, hvol_e]
      exact ⟨Or.inl h1, fun α => by rw [h1, one_mul, hx, simpleNVector_apply]⟩
    · have h1 : σ x = -1 := by
        show ξ x vol = -1
        rw [hx, _root_.neg_apply, simpleNVector_apply, hvol_e]
      exact ⟨Or.inr h1, fun α => by
        rw [h1, neg_one_mul, hx, _root_.neg_apply, simpleNVector_apply]⟩
  -- Step 5: `u = θσ` on `M` and `u = 0` off `M`.
  refine ⟨M.indicator fun x => θ x * σ x, ?_, ?_, ?_⟩
  · -- Step 6: `u` is integer-valued a.e.
    filter_upwards [(ae_restrict_iff'₀ hM).1 hσ] with x hx
    by_cases hxM : x ∈ M
    · obtain ⟨k, hk⟩ := hθ x hxM
      rcases (hx hxM).1 with h1 | h1
      · exact ⟨k, by simp [Set.indicator_of_mem hxM, hk, h1]⟩
      · exact ⟨-k, by simp [Set.indicator_of_mem hxM, hk, h1]⟩
    · exact ⟨0, by simp [Set.indicator_of_notMem hxM]⟩
  · -- Step 7: `θ` is integrable on `M ∩ K` and `|σ| ≤ 1`, so `u` is integrable on `K`.
    intro K hK hKU
    rw [integrableOn_indicator_iff hM]
    have hθK : IntegrableOn θ (M ∩ K) volume := by
      simpa only [hvol] using hT.integrableOn K hK hKU
    refine Integrable.mul_bdd (c := 1) hθK
      (hσm.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Set.inter_subset_left : M ∩ K ⊆ M) hσ] with x hx
    rcases hx.1 with h1 | h1 <;> simp [h1]
  · -- Step 8: `X(ω) = ∫_M θσ ω(e) dx = ∫_U u ω(e) dx`.
    intro ω
    have hMU : NullMeasurableSet M (volume.restrict U) := hM.mono Measure.restrict_le_self
    rw [hXω ω, tauAction, hvol]
    calc ∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) ∂volume
        = ∫ x in M, θ x * σ x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hσ] with x hx
          rw [hx.2]
          ring
      _ = ∫ x in U, M.indicator (fun x =>
            θ x * σ x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e) x ∂volume := by
          rw [integral_indicator₀ hMU, Measure.restrict_restrict₀ hMU,
            Set.inter_eq_left.2 hT.subset]
      _ = ∫ x in U, M.indicator (fun x => θ x * σ x) x *
            (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e ∂volume := by
          congr 1
          funext x
          by_cases hx : x ∈ M <;> simp [hx]

/-- A constant multiple `c [[U]]` of a nonempty open `U ⊆ ℝⁿ` is integer multiplicity only if
`c ∈ ℤ` (Simon Ch. 6, end of the proof of 8.2, p. 179: "`θ ≡ θ(x)` in `B₁ⁿ(0)`; thus
`θ(x) ∈ ℤ`").  An integer multiplicity `X ∈ 𝒟ₙ(U)` acts as `X(ω) = ∫_U u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`
with `u` a.e. integer-valued and integrable on compact subsets of `U`; the constant `c` is a
second such density of `X`, so `c = u` a.e. on `U`, and `Lⁿ(U) > 0`. -/
theorem Submission.ind_const_multiple_integer :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (c : ℝ) (X : GeometricCurrentOn U (m + 1)), IsOpen U →
      U.Nonempty → IsIntegerMultiplicity X →
      (∀ ω : TestFormOn U (m + 1),
        X ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ k : ℤ, c = k := by
  intro m U c X hU hne hX hXc
  -- `X(ω) = ∫_U u ω(e) dx` with `u` a.e. integer-valued and integrable on compacts of `U`.
  obtain ⟨u, hu_int, hu_loc, hu_rep⟩ := Submission.ind_top_dim_integer_density m U X hX
  -- The constant `c` is another density of `X`, hence `c = u` a.e. on `U`.
  have hcu : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → c = u x :=
    Submission.ind_top_form_density_ae_unique m U (fun _ => c) u hU
      (fun K hK _ => integrableOn_const hK.measure_ne_top) hu_loc
      (fun ω => by rw [integral_const_mul, ← hXc]; exact hu_rep ω)
  -- If `c ∉ ℤ`, a.e. point lies outside `U`, contradicting `Lⁿ(U) > 0` for open `U ≠ ∅`.
  by_contra hc
  have hnull : (volume : Measure (Eucl (m + 1))) U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcu, hu_int] with x hx ⟨k, hk⟩ hxU
    exact hc ⟨k, (hx hxU).trans hk⟩
  exact (hU.measure_pos volume hne).ne' hnull

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
