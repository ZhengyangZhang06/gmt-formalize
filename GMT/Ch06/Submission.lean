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

/-- Adapted frame of a nonzero functional (step 1 of the regular level-set charts used for slices
of a rectifiable triple, Simon Ch. 6, 4.1–4.4): for `ℓ ≠ 0` on `ℝ^{m+1}` there are a
norm-preserving `ι : ℝ^m → ℝ^{m+1}` onto `ker ℓ`, a vector `e ⟂ range ι` with `ℓ e = 1`, and `p`
with `ι (p u) + ℓ u • e = u`.  Take `e = ‖a‖⁻² • a` for the Riesz vector `a` of `ℓ`, `ι` from an
orthonormal basis of `ker ℓ` (dimension `m` by rank–nullity) and `p u = ι⁻¹ (u - ℓ u • e)`. -/
theorem Submission.slicing_im_st_lsc_kernel_frame :
    ∀ (m : ℕ) (ℓ : Eucl (m + 1) →L[ℝ] ℝ), ℓ ≠ 0 → ∃ (ι : Eucl m →L[ℝ] Eucl (m + 1)) (p : Eucl (m + 1) →L[ℝ] Eucl m) (e : Eucl (m + 1)), ℓ e = 1 ∧ (∀ v, ‖ι v‖ = ‖v‖) ∧ (∀ v, inner ℝ (ι v) e = 0) ∧ ∀ u, ι (p u) + ℓ u • e = u := by
  intro m ℓ hℓ
  -- Riesz vector `a` of `ℓ` (`ℓ u = ⟪a, u⟫`) and `e := ‖a‖⁻² • a`, so that `ℓ e = 1`.
  set a : Eucl (m + 1) := (InnerProductSpace.toDual ℝ (Eucl (m + 1))).symm ℓ with ha
  have hℓa : ∀ u, ℓ u = inner ℝ a u := fun u => by
    rw [ha, InnerProductSpace.toDual_symm_apply]
  have ha0 : a ≠ 0 := by
    intro h0
    apply hℓ
    ext u
    simp [hℓa, h0]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha0
  set e : Eucl (m + 1) := (‖a‖ ^ 2)⁻¹ • a with he
  have hℓe : ℓ e = 1 := by
    rw [hℓa, he, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  -- `K := ker ℓ` has dimension `m`: `ℓ` maps onto `ℝ`, then rank–nullity.
  set K : Submodule ℝ (Eucl (m + 1)) := LinearMap.ker ℓ.toLinearMap with hKdef
  have htop : LinearMap.range ℓ.toLinearMap = ⊤ := by
    obtain ⟨u, hu⟩ : ∃ u, ℓ u ≠ 0 := by
      by_contra hcon
      apply hℓ
      ext u
      by_contra hu
      exact hcon ⟨u, by simpa using hu⟩
    rw [eq_top_iff]
    rintro y -
    refine ⟨(y / ℓ u) • u, ?_⟩
    simp [hu]
  have hK : Module.finrank ℝ K = m := by
    rw [hKdef]
    have hrn := LinearMap.finrank_range_add_finrank_ker ℓ.toLinearMap
    rw [htop, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hrn
    omega
  -- A linear isometry `J : ℝ^m ≃ K` from an orthonormal basis of `K` indexed by `Fin m`;
  -- `ι := (K ↪ ℝ^{m+1}) ∘ J` and `p u := J⁻¹ (u - ℓ u • e)`.
  let J : Eucl m ≃ₗᵢ[ℝ] K := ((stdOrthonormalBasis ℝ K).reindex (finCongr hK)).repr.symm
  let ι : Eucl m →L[ℝ] Eucl (m + 1) :=
    K.subtypeL.comp J.toContinuousLinearEquiv.toContinuousLinearMap
  have hιK : ∀ v, ι v ∈ K := fun v => (J v).2
  have hmemK : ∀ u, u - ℓ u • e ∈ K := by
    intro u
    simp [hKdef, LinearMap.mem_ker, hℓe]
  let q : Eucl (m + 1) →L[ℝ] K :=
    (ContinuousLinearMap.id ℝ (Eucl (m + 1)) - ℓ.smulRight e).codRestrict K (by
      intro u
      simpa using hmemK u)
  let p : Eucl (m + 1) →L[ℝ] Eucl m :=
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp q
  refine ⟨ι, p, e, hℓe, ?_, ?_, ?_⟩
  · intro v
    show ‖((J v : K) : Eucl (m + 1))‖ = ‖v‖
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  · intro v
    have h1 : ℓ (ι v) = 0 := hιK v
    rw [hℓa] at h1
    rw [he, inner_smul_right, real_inner_comm, h1, mul_zero]
  · intro u
    show ((J (J.symm (q u)) : K) : Eucl (m + 1)) + ℓ u • e = u
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp [q]
/-- `C¹` germ extension (steps 1–2 of the level-set chart construction for Simon Ch. 6, 4.6): if
`g` is `C¹` at `x`, then some `g'` that is `C¹` on all of `ℝ^m` agrees with `g` on a ball
`B(x, ρ)`.  Take `ε` with `g` `C¹` on `B(x, ε)`, `ρ = ε / 3`, a bump `χ` with `χ = 1` on
`B̄(x, ρ)` and `χ = 0` off `B(x, 2ρ)`, and `g' = χ g`. -/
theorem Submission.slicing_im_st_lsc_c1_extension :
    ∀ (m : ℕ) (g : Eucl m → ℝ) (x : Eucl m), ContDiffAt ℝ 1 g x → ∃ ρ : ℝ, 0 < ρ ∧ ∃ g' : Eucl m → ℝ, ContDiff ℝ 1 g' ∧ ∀ v ∈ ball x ρ, g' v = g v := by
  intro m g x hg
  -- `g` is `C¹` at every point of some ball `B(x, ε)` (`ContDiffAt.eventually`); `ρ := ε / 3`.
  have hev := hg.eventually (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  set ρ := ε / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  -- Bump `χ` with `χ = 1` on `closedBall x ρ` and `χ = 0` off `ball x (2ρ)`; `g' := χ * g`.
  let χ : ContDiffBump x := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  refine ⟨ρ, hρ, fun y => χ y * g y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y x < ε
    · exact χ.contDiffAt.mul (hball hy)
    · -- Off `B(x, ε)`, `g'` vanishes on the open neighbourhood `{z | 2ρ < |z - x|}` of `y`.
      have hopen : IsOpen {z : Eucl m | 2 * ρ < dist z x} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hy2 : 2 * ρ < dist y x := by
        have := not_lt.1 hy
        linarith
      have hzero : (fun y => χ y * g y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds hy2] with z hz
        have : χ z = 0 := χ.zero_of_le_dist (le_of_lt hz)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro v hv
    have : χ v = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hv)
    simp [this]
/-- Local graph chart of a regular level set (implicit-function step of the level-set charts used
for integer multiplicity slices, Simon Ch. 6, §4): if `h` is `C¹`, `U` is open, `w₀ ∈ U` and
`Dh(w₀) ≠ 0`, then a `C¹` map `ψ : ℝ^m → ℝ^{m+1}` with `‖v - v'‖ ≤ ‖ψ v - ψ v'‖` maps `B(0, r)`
into `U ∩ {h = h(w₀), Dh ≠ 0}` and onto the level set inside an open `W ∋ w₀`.  With the frame
`(ι, p, e)` of `Dh(w₀)` (`slicing_im_st_lsc_kernel_frame`), `ψ v = w₀ + ι v + g̃ v • e`, where
`g̃` is a `C¹` extension (`slicing_im_st_lsc_c1_extension`) of the implicit function `g` of
`H (v, s) = h (w₀ + ι v + s • e)`, obtained from the inverse function theorem for
`Φ (v, s) = (v, H (v, s))`. -/
theorem Submission.slicing_im_st_lsc_local_graph :
    ∀ (m : ℕ) (h : Eucl (m + 1) → ℝ) (U : Set (Eucl (m + 1))) (w₀ : Eucl (m + 1)), ContDiff ℝ 1 h → IsOpen U → w₀ ∈ U → fderiv ℝ h w₀ ≠ 0 → ∃ (ψ : Eucl m → Eucl (m + 1)) (r : ℝ) (W : Set (Eucl (m + 1))), ContDiff ℝ 1 ψ ∧ 0 < r ∧ IsOpen W ∧ w₀ ∈ W ∧ (∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖) ∧ (∀ v ∈ ball (0 : Eucl m) r, ψ v ∈ U ∧ h (ψ v) = h w₀ ∧ fderiv ℝ h (ψ v) ≠ 0) ∧ ∀ w ∈ W, h w = h w₀ → ∃ v ∈ ball (0 : Eucl m) r, ψ v = w := by
  have hKF := Submission.slicing_im_st_lsc_kernel_frame
  have hC1E := Submission.slicing_im_st_lsc_c1_extension
  intro m h U w₀ hh hU hw₀ hdh
  -- Frame of `ℓ := Dh(w₀)`: `ℓ e = 1`, `ι` isometric, `ι v ⟂ e` and `ι (p u) + ℓ u • e = u`.
  obtain ⟨ι, p, e, hℓe, hιn, hιe, hdec⟩ := hKF m (fderiv ℝ h w₀) hdh
  set ℓ := fderiv ℝ h w₀ with hℓdef
  -- `A (v, s) = w₀ + ι v + s • e` and `H := h ∘ A`, with `DH(0, 0) = ℓ ∘ L`.
  let L : Eucl m × ℝ →L[ℝ] Eucl (m + 1) :=
    ι.comp (ContinuousLinearMap.fst ℝ (Eucl m) ℝ) +
      (ContinuousLinearMap.snd ℝ (Eucl m) ℝ).smulRight e
  let A : Eucl m × ℝ → Eucl (m + 1) := fun q => w₀ + L q
  have hAapp : ∀ q : Eucl m × ℝ, A q = w₀ + ι q.1 + q.2 • e := by
    intro q
    simp [A, L, add_assoc]
  let H : Eucl m × ℝ → ℝ := fun q => h (A q)
  have hAd : ∀ q, HasFDerivAt A L q := fun q => (L.hasFDerivAt).const_add w₀
  have hA0 : A (0, 0) = w₀ := by
    rw [hAapp]
    simp
  have hH : ContDiff ℝ 1 H := hh.comp (contDiff_const.add L.contDiff)
  have hHd : HasFDerivAt H (ℓ.comp L) ((0 : Eucl m), (0 : ℝ)) := by
    have h1 := (hh.differentiable one_ne_zero (A (0, 0))).hasFDerivAt.comp ((0 : Eucl m), (0 : ℝ))
      (hAd (0, 0))
    rw [hA0] at h1
    exact h1
  -- `Φ (v, s) := (v, H (v, s))` has derivative `Φ₀ (v, s) = (v, ℓ (ι v) + s)` at `(0, 0)`, an
  -- equivalence with inverse `Ψ₀ (v, t) = (v, t - ℓ (ι v))`.
  let Φ : Eucl m × ℝ → Eucl m × ℝ := fun q => (q.1, H q)
  have hΦC : ContDiff ℝ 1 Φ := contDiff_fst.prodMk hH
  let Φ₀ : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ :=
    (ContinuousLinearMap.fst ℝ (Eucl m) ℝ).prod (ℓ.comp L)
  let Ψ₀ : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ :=
    (ContinuousLinearMap.fst ℝ (Eucl m) ℝ).prod
      (ContinuousLinearMap.snd ℝ (Eucl m) ℝ - (ℓ.comp ι).comp (ContinuousLinearMap.fst ℝ (Eucl m) ℝ))
  have hleft : Function.LeftInverse Ψ₀ Φ₀ := by
    rintro ⟨v, s⟩
    simp [Φ₀, Ψ₀, L, hℓe]
  have hright : Function.RightInverse Ψ₀ Φ₀ := by
    rintro ⟨v, t⟩
    simp [Φ₀, Ψ₀, L, hℓe]
  let Φ₀e : (Eucl m × ℝ) ≃L[ℝ] Eucl m × ℝ := ContinuousLinearEquiv.equivOfInverse Φ₀ Ψ₀ hleft hright
  have hΦd : HasFDerivAt Φ (Φ₀e : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ) ((0 : Eucl m), (0 : ℝ)) :=
    hasFDerivAt_fst.prodMk hHd
  have hΦs : HasStrictFDerivAt Φ (Φ₀e : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ) ((0 : Eucl m), (0 : ℝ)) := by
    have h1 := hΦC.contDiffAt.hasStrictFDerivAt (x := ((0 : Eucl m), (0 : ℝ))) one_ne_zero
    rwa [hΦd.fderiv] at h1
  -- Inverse function theorem: `Φ` is a local homeomorphism `T` near `(0, 0)` with `C¹` inverse.
  let T := hΦs.toOpenPartialHomeomorph Φ
  have hsrc : ((0 : Eucl m), (0 : ℝ)) ∈ T.source := hΦs.mem_toOpenPartialHomeomorph_source
  have htgt : ((0 : Eucl m), H ((0 : Eucl m), (0 : ℝ))) ∈ T.target :=
    hΦs.image_mem_toOpenPartialHomeomorph_target
  have hT0 : T.symm ((0 : Eucl m), H ((0 : Eucl m), (0 : ℝ))) = ((0 : Eucl m), (0 : ℝ)) :=
    T.left_inv hsrc
  have hTC : ContDiffAt ℝ 1 T.symm ((0 : Eucl m), H ((0 : Eucl m), (0 : ℝ))) := by
    refine T.contDiffAt_symm (f₀' := Φ₀e) htgt ?_ ?_
    · rw [hT0]
      exact hΦd
    · rw [hT0]
      exact hΦC.contDiffAt
  -- Implicit function `g v := (T⁻¹ (v, H (0, 0))).2`: `g 0 = 0`, `g` is `C¹` at `0` and, near
  -- `(0, 0)`, `H (v, s) = H (0, 0) ↔ g v = s`.
  let g : Eucl m → ℝ := fun v => (T.symm (v, H ((0 : Eucl m), (0 : ℝ)))).2
  have hg0 : g 0 = 0 := by
    simp only [g, hT0]
  have hgC1 : ContDiffAt ℝ 1 g 0 := by
    have hin : ContDiffAt ℝ 1 (fun v : Eucl m => (v, H ((0 : Eucl m), (0 : ℝ)))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    exact contDiffAt_snd.comp (0 : Eucl m)
      (ContDiffAt.comp (f := fun v : Eucl m => (v, H ((0 : Eucl m), (0 : ℝ)))) (0 : Eucl m) hTC hin)
  have hiff : ∀ᶠ q in 𝓝 ((0 : Eucl m), (0 : ℝ)), H q = H ((0 : Eucl m), (0 : ℝ)) ↔ g q.1 = q.2 := by
    have hsrc' : ∀ᶠ q in 𝓝 ((0 : Eucl m), (0 : ℝ)), q ∈ T.source := T.open_source.mem_nhds hsrc
    have htgt' : ∀ᶠ q in 𝓝 ((0 : Eucl m), (0 : ℝ)),
        (q.1, H ((0 : Eucl m), (0 : ℝ))) ∈ T.target :=
      (continuous_fst.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (T.open_target.mem_nhds htgt)
    filter_upwards [hsrc', htgt'] with q hq1 hq2
    constructor
    · intro hq
      have hΦq : T q = (q.1, H ((0 : Eucl m), (0 : ℝ))) := Prod.ext rfl hq
      show (T.symm (q.1, H ((0 : Eucl m), (0 : ℝ)))).2 = q.2
      rw [← hΦq, T.left_inv hq1]
    · intro hq
      have hr : Φ (T.symm (q.1, H ((0 : Eucl m), (0 : ℝ)))) = (q.1, H ((0 : Eucl m), (0 : ℝ))) :=
        T.right_inv hq2
      have hr1 := congrArg Prod.fst hr
      have hr2 := congrArg Prod.snd hr
      have hq' : T.symm (q.1, H ((0 : Eucl m), (0 : ℝ))) = q := Prod.ext hr1 hq
      rw [hq'] at hr2
      exact hr2
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 hiff
  -- `g' = g` on `B(0, ρ)` is `C¹` on `ℝ^m`, and `ψ v := w₀ + ι v + g' v • e`.
  obtain ⟨ρ, hρ, g', hg'C, hg'eq⟩ := hC1E m g 0 hgC1
  let ψ : Eucl m → Eucl (m + 1) := fun v => w₀ + ι v + g' v • e
  have hψC : ContDiff ℝ 1 ψ := (contDiff_const.add ι.contDiff).add (hg'C.smul contDiff_const)
  have hψ0 : ψ 0 = w₀ := by
    simp [ψ, hg'eq 0 (mem_ball_self hρ), hg0]
  -- (i) Pythagoras: `‖ψ v - ψ v'‖² = ‖v - v'‖² + ‖(g' v - g' v') • e‖²`.
  have hanti : ∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖ := by
    intro v v'
    have hdiff : ψ v - ψ v' = ι (v - v') + (g' v - g' v') • e := by
      simp only [ψ, map_sub, sub_smul]
      abel
    have horth : inner ℝ (ι (v - v')) ((g' v - g' v') • e) = 0 := by
      rw [inner_smul_right, hιe, mul_zero]
    have hsq : ‖ψ v - ψ v'‖ ^ 2 = ‖v - v'‖ ^ 2 + ‖(g' v - g' v') • e‖ ^ 2 := by
      rw [hdiff, norm_add_sq_real, horth, hιn]
      ring
    have hle : ‖v - v'‖ ^ 2 ≤ ‖ψ v - ψ v'‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ‖(g' v - g' v') • e‖]
    exact le_of_sq_le_sq hle (norm_nonneg _)
  -- `r := min r₀ (min ρ ε)`, where `ψ (B(0, r₀)) ⊆ U ∩ {Dh ≠ 0}` and `|g| < ε` on `B(0, r₀)`.
  have hopen : IsOpen (U ∩ {w | fderiv ℝ h w ≠ 0}) :=
    hU.inter (isOpen_ne_fun (hh.continuous_fderiv one_ne_zero) continuous_const)
  have h1 : ∀ᶠ v in 𝓝 (0 : Eucl m), ψ v ∈ U ∩ {w | fderiv ℝ h w ≠ 0} := by
    apply hψC.continuous.continuousAt.preimage_mem_nhds
    rw [hψ0]
    exact hopen.mem_nhds ⟨hw₀, hdh⟩
  have h2 : ∀ᶠ v in 𝓝 (0 : Eucl m), g v ∈ ball (0 : ℝ) ε := by
    apply hgC1.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact ball_mem_nhds _ hε
  obtain ⟨r₀, hr₀, hr₀ball⟩ := Metric.mem_nhds_iff.1 (h1.and h2)
  set r := min r₀ (min ρ ε) with hrdef
  have hr : 0 < r := lt_min hr₀ (lt_min hρ hε)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  -- `W := {w | p (w - w₀) ∈ B(0, r), |ℓ (w - w₀)| < ε}`; by the frame,
  -- `A (p (w - w₀), ℓ (w - w₀)) = w`.
  let W : Set (Eucl (m + 1)) := {w | p (w - w₀) ∈ ball (0 : Eucl m) r ∧ ℓ (w - w₀) ∈ ball (0 : ℝ) ε}
  have hWo : IsOpen W := by
    apply IsOpen.inter
    · exact isOpen_ball.preimage (p.continuous.comp (continuous_id.sub continuous_const))
    · exact isOpen_ball.preimage (ℓ.continuous.comp (continuous_id.sub continuous_const))
  have hw₀W : w₀ ∈ W := by
    simp [W, hr, hε]
  refine ⟨ψ, r, W, hψC, hr, hWo, hw₀W, hanti, ?_, ?_⟩
  -- (ii) For `v ∈ B(0, r)`: `(v, g v) ∈ B((0, 0), ε)` and `ψ v = A (v, g v)`.
  · intro v hv
    have hvr₀ : v ∈ ball (0 : Eucl m) r₀ := ball_subset_ball hrr₀ hv
    obtain ⟨⟨hU', hd'⟩, hgv⟩ := hr₀ball hvr₀
    refine ⟨hU', ?_, hd'⟩
    have hvρ : v ∈ ball (0 : Eucl m) ρ := ball_subset_ball hrρ hv
    have hvε : v ∈ ball (0 : Eucl m) ε := ball_subset_ball hrε hv
    have hq : ((v, g v) : Eucl m × ℝ) ∈ ball ((0 : Eucl m), (0 : ℝ)) ε := by
      rw [← ball_prod_same]
      exact ⟨hvε, hgv⟩
    have hHq : H (v, g v) = H ((0 : Eucl m), (0 : ℝ)) := (hεball hq).2 rfl
    have hψv : ψ v = A (v, g v) := by
      rw [hAapp]
      simp [ψ, hg'eq v hvρ]
    rw [hψv]
    simpa [H, hA0] using hHq
  -- (iii) For `w ∈ W` on the level set, `v := p (w - w₀)` has `g v = ℓ (w - w₀)`, so `ψ v = w`.
  · intro w hw hhw
    obtain ⟨hpw, hℓw⟩ := hw
    have hAw : A (p (w - w₀), ℓ (w - w₀)) = w := by
      rw [hAapp]
      have := hdec (w - w₀)
      simp only at this ⊢
      rw [add_assoc, this]
      abel
    have hvε : p (w - w₀) ∈ ball (0 : Eucl m) ε := ball_subset_ball hrε hpw
    have hq : ((p (w - w₀), ℓ (w - w₀)) : Eucl m × ℝ) ∈ ball ((0 : Eucl m), (0 : ℝ)) ε := by
      rw [← ball_prod_same]
      exact ⟨hvε, hℓw⟩
    have hHq : H (p (w - w₀), ℓ (w - w₀)) = H ((0 : Eucl m), (0 : ℝ)) := by
      simp only [H]
      rw [hAw, hA0]
      exact hhw
    have hgs : g (p (w - w₀)) = ℓ (w - w₀) := (hεball hq).1 hHq
    refine ⟨p (w - w₀), hpw, ?_⟩
    have hvρ : p (w - w₀) ∈ ball (0 : Eucl m) ρ := ball_subset_ball hrρ hpw
    calc ψ (p (w - w₀)) = w₀ + ι (p (w - w₀)) + g' (p (w - w₀)) • e := rfl
      _ = w₀ + ι (p (w - w₀)) + ℓ (w - w₀) • e := by rw [hg'eq _ hvρ, hgs]
      _ = A (p (w - w₀), ℓ (w - w₀)) := (hAapp (p (w - w₀), ℓ (w - w₀))).symm
      _ = w := hAw
/-- Derivative lower bound (step 1 of the C¹ chart approximate tangent argument for Simon Ch. 6,
3.9): if `c ‖v - v'‖ ≤ ‖Φ v - Φ v'‖` on an open `Ω ∋ w` and `Φ` is differentiable at `w`, then
`c ‖s‖ ≤ ‖DΦ(w) s‖` for every `s` (no sign condition on `c`).  Apply the bound to `v = w + t • s`,
`v' = w`, divide by `t > 0` and let `t → 0⁺`. -/
theorem Submission.lpf_wtc_cat_fderiv_lower_bound :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (c : ℝ) (w : Eucl n), IsOpen Ω → w ∈ Ω → DifferentiableAt ℝ Φ w → (∀ v ∈ Ω, ∀ v' ∈ Ω, c * ‖v - v'‖ ≤ ‖Φ v - Φ v'‖) → ∀ s : Eucl n, c * ‖s‖ ≤ ‖fderiv ℝ Φ w s‖ := by
  intro Q n Φ Ω c w hΩ hw hdiff hanti s
  -- `γ t = Φ (w + t • s)` has derivative `DΦ(w) s` at `0`, so its right slopes converge to it.
  have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
  have hγ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 := by
    have h0 : w + (0 : ℝ) • s = w := by simp
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
  have hnorm : Tendsto (fun t : ℝ => ‖t⁻¹ • (Φ (w + (0 + t) • s) - Φ (w + (0 : ℝ) • s))‖)
      (𝓝[>] 0) (𝓝 ‖fderiv ℝ Φ w s‖) := hγ.tendsto_slope_zero_right.norm
  -- The segment `w + t • s` stays in the open set `Ω` for small `t`.
  have hcont : Continuous (fun t : ℝ => w + t • s) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), w + t • s ∈ Ω := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hw
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c * ‖s‖ ≤ ‖t⁻¹ • (Φ (w + (0 + t) • s) - Φ (w + (0 : ℝ) • s))‖ := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with t ht htpos
    have htpos : (0 : ℝ) < t := htpos
    have h1 := hanti (w + t • s) ht w hw
    simp only [zero_add, zero_smul, add_zero]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), le_inv_mul_iff₀ htpos]
    linarith [h1]
  exact ge_of_tendsto hnorm hev

/-- Tangent range of a level-set chart (step 7 of the level-set charts for the slicing theorem,
Simon Ch. 6, §4): if `ψ` is differentiable at `v` and `c`-antilipschitz (`c > 0`) on an open
`V ∋ v`, and `h ∘ ψ` is constant on `V` with `Dh(ψ v) ≠ 0`, then
`range D(Φ ∘ ψ)(v) = DΦ(ψ v)(ker Dh(ψ v))`.  By the derivative lower bound `Dψ(v)` is injective,
by the chain rule its range lies in `ker Dh(ψ v)`, and both subspaces have dimension `m`. -/
theorem Submission.slicing_im_st_lsc_tangent_range :
    ∀ (P m : ℕ) (ψ : Eucl m → Eucl (m + 1)) (Φ : Eucl (m + 1) → Eucl P) (h : Eucl (m + 1) → ℝ) (V : Set (Eucl m)) (c : ℝ) (v : Eucl m), IsOpen V → v ∈ V → 0 < c → DifferentiableAt ℝ ψ v → DifferentiableAt ℝ Φ (ψ v) → DifferentiableAt ℝ h (ψ v) → fderiv ℝ h (ψ v) ≠ 0 → (∀ v' ∈ V, ∀ v'' ∈ V, c * ‖v' - v''‖ ≤ ‖ψ v' - ψ v''‖) → (∀ v' ∈ V, h (ψ v') = h (ψ v)) → LinearMap.range (fderiv ℝ (Φ ∘ ψ) v).toLinearMap = Submodule.map (fderiv ℝ Φ (ψ v)).toLinearMap (LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap) := by
  intro P m ψ Φ h V c v hV hv hc hψd hΦd hhd hdh hanti hconst
  -- `c ‖u‖ ≤ ‖Dψ(v) u‖` with `c > 0`, so `Dψ(v)` is injective.
  have hlow := Submission.lpf_wtc_cat_fderiv_lower_bound (m + 1) m ψ V c v hV hv hψd hanti
  have hinj : Function.Injective (fderiv ℝ ψ v) := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  -- `h ∘ ψ` is constant near `v`, so `Dh(ψ v) ∘ Dψ(v) = D(h ∘ ψ)(v) = 0`.
  have hev : (h ∘ ψ) =ᶠ[𝓝 v] fun _ => h (ψ v) := by
    filter_upwards [hV.mem_nhds hv] with v' hv' using hconst v' hv'
  have hzero : fderiv ℝ (h ∘ ψ) v = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  have hcomp : fderiv ℝ (h ∘ ψ) v = (fderiv ℝ h (ψ v)).comp (fderiv ℝ ψ v) :=
    fderiv_comp v hhd hψd
  have hle : LinearMap.range (fderiv ℝ ψ v).toLinearMap ≤
      LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap := by
    rintro _ ⟨u, rfl⟩
    have h3 := congrArg (fun L : Eucl m →L[ℝ] ℝ => L u) (hcomp.symm.trans hzero)
    simpa using h3
  -- Both subspaces have dimension `m`: `Dψ(v)` is injective, and `Dh(ψ v) ≠ 0` maps onto `ℝ`.
  have hrange : Module.finrank ℝ (LinearMap.range (fderiv ℝ ψ v).toLinearMap) = m := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  have htop : LinearMap.range (fderiv ℝ h (ψ v)).toLinearMap = ⊤ := by
    obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ h (ψ v) u ≠ 0 := by
      by_contra hcon
      apply hdh
      ext u
      by_contra hu
      exact hcon ⟨u, by simpa using hu⟩
    rw [eq_top_iff]
    rintro y -
    refine ⟨(y / fderiv ℝ h (ψ v) u) • u, ?_⟩
    simp [hu]
  have hker : Module.finrank ℝ (LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap) = m := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ h (ψ v)).toLinearMap
    rw [htop, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hrn
    omega
  have heq : LinearMap.range (fderiv ℝ ψ v).toLinearMap =
      LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (hrange.trans hker.symm)
  -- Chain rule: `range D(Φ ∘ ψ)(v) = DΦ(ψ v)(range Dψ(v))`.
  rw [fderiv_comp v hΦd hψd]
  show LinearMap.range ((fderiv ℝ Φ (ψ v)).toLinearMap.comp (fderiv ℝ ψ v).toLinearMap) = _
  rw [LinearMap.range_comp, heq]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
