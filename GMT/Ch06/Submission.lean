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

/-- Polar coordinates for an integrable `g` on `ℝ^{m+1}`, with `σ = (Lᵐ⁺¹).toSphere`:
`∫ g = ∫_{S^m} ∫_0^∞ r^m g(rθ) dr dσ(θ)`.  As in Mathlib's `integral_fun_norm_addHaar`,
`homeomorphUnitSphereProd` carries Lebesgue measure on `ℝ^{m+1} ∖ {0}` to `σ ⊗ volumeIoiPow m`,
Fubini splits the product, and `volumeIoiPow m` is `r^m dr` on `(0, ∞)`. -/
theorem Submission.rpn_pe_integral_eq_polar :
    ∀ (m : ℕ) (g : Eucl (m + 1) → ℝ), Integrable g → ∫ x, g x =
      ∫ θ : sphere (0 : Eucl (m + 1)) 1, (∫ r in Ioi (0 : ℝ), r ^ m * g (r • (θ : Eucl (m + 1))))
        ∂(volume : Measure (Eucl (m + 1))).toSphere := by
  intro m g hg
  -- `Φ = homeomorphUnitSphereProd` is measure preserving onto `σ ⊗ volumeIoiPow m`.
  have hdim : Module.finrank ℝ (Eucl (m + 1)) - 1 = m := by simp
  have hmp : MeasurePreserving (homeomorphUnitSphereProd (Eucl (m + 1)))
      ((volume : Measure (Eucl (m + 1))).comap (↑))
      ((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    have := (volume : Measure (Eucl (m + 1))).measurePreserving_homeomorphUnitSphereProd
    rwa [hdim] at this
  -- `G(θ, r) = g(rθ)` satisfies `G ∘ Φ = g` on `ℝ^{m+1} ∖ {0}`.
  set G : sphere (0 : Eucl (m + 1)) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => g ((p.2 : ℝ) • (p.1 : Eucl (m + 1))) with hG
  have hGΦ : ∀ x : ({0}ᶜ : Set (Eucl (m + 1))), G (homeomorphUnitSphereProd _ x) = g x := by
    intro x
    have hx : ‖(x : Eucl (m + 1))‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    simp only [hG, homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
    rw [smul_smul, mul_inv_cancel₀ hx, one_smul]
  -- Remove the null point `0`, then change variables along `Φ`.
  have h3 : ∫ x, g x = ∫ x : ({0}ᶜ : Set (Eucl (m + 1))), g x
      ∂((volume : Measure (Eucl (m + 1))).comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]
  have h4 : ∫ x : ({0}ᶜ : Set (Eucl (m + 1))), g x
      ∂((volume : Measure (Eucl (m + 1))).comap (↑)) =
      ∫ p, G p ∂((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) G]
    simp only [hGΦ]
  have h5 : Integrable G
      ((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : G ∘ homeomorphUnitSphereProd (Eucl (m + 1)) = g ∘ Subtype.val := funext hGΦ
    rw [this, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hg.integrableOn
  -- Fubini, then unfold `volumeIoiPow m = r^m dr` on `(0, ∞)` for each `θ`.
  rw [h3, h4, integral_prod G h5]
  congr 1
  funext θ
  simp only [hG, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ m) • g (a • (θ : Eucl (m + 1)))),
    setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal
/-- The radial integral `∫_{B_ρ(0)} |w|^{1-n} dw = n ω_n ρ` in `ℝⁿ`, `n = m + 1`, `ρ > 0`,
`ω_n = Lⁿ(B_1(0))` (formula (R) of the potential estimate in the proof of Simon Ch. 6, 8.1);
`|w|^{1-n}` is written `(‖w‖ ^ m)⁻¹`.  In polar coordinates (`integrableOn_fun_norm_addHaar`,
`integral_fun_norm_addHaar`) the radial profile `r^{n-1} (r^{n-1})⁻¹` is `1` on `(0, ρ)`: this
gives integrability, and with `1_{B_ρ(0)}(w) = 1_{(-∞, ρ)}(|w|)` the value `n ω_n ρ`. -/
theorem Submission.rpn_pe_inv_norm_pow_ball :
    ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) (ball (0 : Eucl (m + 1)) ρ) ∧ ∫ t in ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ = ((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ρ := by
  intro m ρ hρ
  have hdim : Module.finrank ℝ (Eucl (m + 1)) - 1 = m := by
    rw [finrank_euclideanSpace_fin, Nat.add_sub_cancel]
  constructor
  · -- Integrability: `r ^ m • (r ^ m)⁻¹ = 1` is integrable on `(0, ρ)`.
    rw [integrableOn_fun_norm_addHaar (volume : Measure (Eucl (m + 1)))
      (f := fun r : ℝ => (r ^ m)⁻¹), hdim]
    refine (integrableOn_congr_fun (g := fun _ => (1 : ℝ)) (fun r hr => ?_) measurableSet_Ioo).2
      (integrableOn_const measure_Ioo_lt_top.ne)
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hr.1))
  · -- `h = 1_{(-∞, ρ)} · (r ↦ (r ^ m)⁻¹)`, so `1_{B_ρ(0)}(w) (‖w‖ ^ m)⁻¹ = h ‖w‖`.
    set h : ℝ → ℝ := (Iio ρ).indicator fun r => (r ^ m)⁻¹ with hh
    have hind : (ball (0 : Eucl (m + 1)) ρ).indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) =
        fun t => h ‖t‖ := by
      ext t
      simp [hh, indicator]
    -- For `r > 0`, `r ^ m • h r = 1_{(-∞, ρ)}(r)`, so the radial integral is `L¹((0, ρ)) = ρ`.
    have hrad : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Eucl (m + 1)) - 1) • h y = ρ := by
      rw [hdim, setIntegral_congr_fun measurableSet_Ioi
        (g := (Iio ρ).indicator fun _ => (1 : ℝ)) (fun y hy => ?_)]
      · rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          setIntegral_const, Iio_inter_Ioi, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one, sub_zero]
      · by_cases hy' : y < ρ
        · simp [hh, indicator, hy', mul_inv_cancel₀ (pow_ne_zero m (ne_of_gt (mem_Ioi.1 hy)))]
        · simp [hh, indicator, hy']
    rw [← integral_indicator measurableSet_ball, hind,
      integral_fun_norm_addHaar (volume : Measure (Eucl (m + 1))) h, hrad,
      finrank_euclideanSpace_fin, measureReal_def, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-- Potential estimate over a set of finite measure (Gilbarg–Trudinger, proof of Lemma 7.12, with
the cruder constant `n + 1`): for measurable `S ⊆ ℝⁿ`, `n = m + 1`, with `Lⁿ(S) < ∞`, the kernel
`|w|^{1-n} = (|w|^m)⁻¹` is integrable on `S` and
`∫_S |w|^{1-n} dw ≤ (n + 1) ω^{(n-1)/n} Lⁿ(S)^{1/n}`, `ω = Lⁿ(B_1(0))`.  Split `S` at the radius
`ρ = (Lⁿ(S)/ω)^{1/n}`: the part inside `B_ρ(0)` contributes at most `∫_{B_ρ(0)} |w|^{1-n} = nωρ`,
the part outside at most `ρ^{1-n} Lⁿ(S) = ωρ`. -/
theorem Submission.rpn_pe_inv_norm_pow_set_bound : ∀ (m : ℕ) (S : Set (Eucl (m + 1))), MeasurableSet S → volume S ≠ ⊤ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) S ∧ ∫ t in S, (‖t‖ ^ m)⁻¹ ≤ ((m : ℝ) + 2) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal ^ ((m : ℝ) / ((m : ℝ) + 1)) * (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro m S hS hSfin
  -- Step 1: `f = (‖·‖ ^ m)⁻¹` is measurable and nonnegative.
  have hf_meas : Measurable (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) :=
    (measurable_norm.pow_const m).inv
  have hf_nonneg : ∀ t : Eucl (m + 1), 0 ≤ (‖t‖ ^ m)⁻¹ := fun t => by positivity
  -- Step 2: off `B_ρ(0)`, `f ≤ (ρ ^ m)⁻¹`; as `Lⁿ(S \ B_ρ(0)) < ∞`, `f` is integrable there.
  have hfar_le : ∀ ρ : ℝ, 0 < ρ → ∀ t ∈ S \ ball (0 : Eucl (m + 1)) ρ,
      (‖t‖ ^ m)⁻¹ ≤ (ρ ^ m)⁻¹ := by
    intro ρ hρ t ht
    have hρt : ρ ≤ ‖t‖ := by simpa using ht.2
    exact inv_anti₀ (pow_pos hρ m) (pow_le_pow_left₀ hρ.le hρt m)
  have hfar_fin : ∀ ρ : ℝ, volume (S \ ball (0 : Eucl (m + 1)) ρ) ≠ ⊤ := fun ρ =>
    ne_top_of_le_ne_top hSfin (measure_mono sdiff_subset)
  have hfar_int : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) (S \ ball (0 : Eucl (m + 1)) ρ) := by
    intro ρ hρ
    refine Measure.integrableOn_of_bounded (M := (ρ ^ m)⁻¹) (hfar_fin ρ)
      hf_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (hS.diff measurableSet_ball)] with t ht
    rw [Real.norm_of_nonneg (hf_nonneg t)]
    exact hfar_le ρ hρ t ht
  -- Step 3: with the ball integral, `f` is integrable on `S = (S ∩ B_ρ(0)) ∪ (S \ B_ρ(0))`.
  have hint : ∀ ρ : ℝ, 0 < ρ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) S := by
    intro ρ hρ
    have h : IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹)
        (S ∩ ball (0 : Eucl (m + 1)) ρ ∪ S \ ball (0 : Eucl (m + 1)) ρ) :=
      ((Submission.rpn_pe_inv_norm_pow_ball m ρ hρ).1.mono_set inter_subset_right).union
        (hfar_int ρ hρ)
    rwa [inter_union_sdiff] at h
  refine ⟨hint 1 one_pos, ?_⟩
  set ω := (volume (ball (0 : Eucl (m + 1)) 1)).toReal
  set L := (volume S).toReal
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hL_nonneg : 0 ≤ L := ENNReal.toReal_nonneg
  rcases hL_nonneg.eq_or_lt with hL0 | hL_pos
  · -- Step 4: if `Lⁿ(S) = 0`, both sides vanish.
    have hS0 : volume S = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 hL0.symm).resolve_right hSfin
    rw [Measure.restrict_eq_zero.2 hS0, integral_zero_measure, ← hL0,
      Real.zero_rpow (by positivity), mul_zero]
  · -- Step 5: the radius `ρ = (L / ω) ^ (1/(m+1))`, so that `L = ω ρ ^ (m + 1)`.
    set p : ℝ := 1 / ((m : ℝ) + 1) with hp
    set ρ : ℝ := (L / ω) ^ p with hρ
    have hLω : 0 < L / ω := div_pos hL_pos hω_pos
    have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hLω p
    have hL_eq : L = ω * ρ ^ (m + 1) := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hLω.le,
        show p * ((m + 1 : ℕ) : ℝ) = 1 by rw [hp]; push_cast; field_simp, Real.rpow_one]
      field_simp
    obtain ⟨hball_int, hball_eq⟩ := Submission.rpn_pe_inv_norm_pow_ball m ρ hρ_pos
    -- Step 6: split `∫_S f` along `B_ρ(0)`.
    rw [← integral_inter_add_sdiff (measurableSet_ball : MeasurableSet (ball (0 : Eucl (m + 1)) ρ))
      (hint ρ hρ_pos)]
    -- Step 7: the near part is at most `∫_{B_ρ(0)} f = (m + 1) ω ρ`.
    have hnear : ∫ t in S ∩ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ ≤ ((m : ℝ) + 1) * ω * ρ := by
      rw [← hball_eq]
      exact setIntegral_mono_set hball_int (ae_of_all _ hf_nonneg)
        (ae_of_all _ fun t ht => ht.2)
    -- Step 8: the far part is at most `Lⁿ(S \ B_ρ(0)) (ρ ^ m)⁻¹ ≤ L (ρ ^ m)⁻¹ = ω ρ`.
    have hfar : ∫ t in S \ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ ≤ ω * ρ := by
      calc ∫ t in S \ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹
          ≤ ∫ _ in S \ ball (0 : Eucl (m + 1)) ρ, (ρ ^ m)⁻¹ :=
            setIntegral_mono_on (hfar_int ρ hρ_pos) (integrableOn_const (hfar_fin ρ))
              (hS.diff measurableSet_ball) (hfar_le ρ hρ_pos)
        _ = volume.real (S \ ball (0 : Eucl (m + 1)) ρ) * (ρ ^ m)⁻¹ := by
            rw [setIntegral_const, smul_eq_mul]
        _ ≤ L * (ρ ^ m)⁻¹ := by
            gcongr
            exact measureReal_mono sdiff_subset hSfin
        _ = ω * ρ := by
            rw [hL_eq, pow_succ]
            field_simp
    -- Steps 9–10: the sum is `(m + 2) ω ρ = (m + 2) ω ^ (m/(m+1)) L ^ (1/(m+1))`.
    have hωρ : ω * ρ = ω ^ ((m : ℝ) / ((m : ℝ) + 1)) * L ^ p := by
      rw [hρ, Real.div_rpow hL_pos.le hω_pos.le,
        show (m : ℝ) / ((m : ℝ) + 1) = 1 - p by rw [hp]; field_simp; ring,
        Real.rpow_sub hω_pos, Real.rpow_one]
      ring
    calc _ ≤ ((m : ℝ) + 1) * ω * ρ + ω * ρ := add_le_add hnear hfar
      _ = ((m : ℝ) + 2) * (ω * ρ) := by ring
      _ = ((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) * L ^ p := by
        rw [hωρ, mul_assoc]
/-- The kernels `K(w) = w_j / (c|w|^{m+1})` on `ℝ^{m+1}` are locally integrable. This is Step 2 of
the potential estimate (Gilbarg–Trudinger §7.8) that replaces the BV argument of Simon Ch. 6,
Remark 2.35 in the proof of 8.1; there `c = nωₙ`. With `x / 0 = 0`, `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹`
everywhere, and `(|w|^m)⁻¹` is integrable on every ball about `0`
(`Submission.rpn_pe_inv_norm_pow_ball`). -/
theorem Submission.rpn_pe_kernel_locallyIntegrable : ∀ (m : ℕ) (j : Fin (m + 1)) (c : ℝ), LocallyIntegrable (fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1))) := by
  intro m j c
  -- Step 1: `K` is Borel measurable.
  have hmeas : Measurable fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1)) := by fun_prop
  -- Step 2: `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹`. If `c = 0` or `w = 0` the left side is `0`; otherwise
  -- `|w_j| ≤ |w|`.
  have hbound : ∀ t : Eucl (m + 1), ‖t j / (c * ‖t‖ ^ (m + 1))‖ ≤ |c|⁻¹ * (‖t‖ ^ m)⁻¹ := by
    intro t
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [PiLp.zero_apply, zero_div, norm_zero]
      positivity
    have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht
    rw [norm_div, norm_mul, norm_pow, norm_norm, Real.norm_eq_abs c]
    calc ‖t j‖ / (|c| * ‖t‖ ^ (m + 1)) ≤ ‖t‖ / (|c| * ‖t‖ ^ (m + 1)) := by
          gcongr
          exact PiLp.norm_apply_le t j
      _ = |c|⁻¹ * (‖t‖ ^ m)⁻¹ := by
          field_simp
          ring
  -- Step 3: around `x` use the ball `B_{|x|+1}(0)`, where `(|w|^m)⁻¹` is integrable.
  intro x
  refine ⟨ball (0 : Eucl (m + 1)) (‖x‖ + 1), isOpen_ball.mem_nhds (by simp), ?_⟩
  exact ((Submission.rpn_pe_inv_norm_pow_ball m (‖x‖ + 1) (by positivity)).1.const_mul |c|⁻¹).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ hbound)
/-- Convolution of a locally integrable kernel with a `C^∞` compactly supported function:
`ψ(y) = ∫ K(t) a(y - t) dt` is `C^∞`, and for all `y, v`, `t ↦ K(t) Da(y - t)v` is integrable with
`Dψ(y)v = ∫ K(t) Da(y - t)v dt`.  Here `ψ = K ⋆ a` for the pairing `lsmul ℝ ℝ`, so
`HasCompactSupport.contDiff_convolution_right` gives smoothness, `convolutionExists_right`
applied to the continuous compactly supported `z ↦ Da(z)v` gives integrability, and
`hasFDerivAt_convolution_right` with `convolution_precompR_apply` gives the derivative. -/
theorem Submission.rpn_pe_convolution_contDiff_fderiv :
    ∀ (n : ℕ) (K a : Eucl n → ℝ), LocallyIntegrable K → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a →
      HasCompactSupport a → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t, K t * a (y - t)) ∧
      ∀ y v : Eucl n, Integrable (fun t => K t * fderiv ℝ a (y - t) v) ∧
        fderiv ℝ (fun y => ∫ t, K t * a (y - t)) y v = ∫ t, K t * fderiv ℝ a (y - t) v := by
  intro n K a hK ha hsupp
  -- `ψ = K ⋆ a` for the scalar multiplication pairing (`convolution_lsmul`).
  have hψ : (fun y => ∫ t, K t * a (y - t)) =
      convolution K a (ContinuousLinearMap.lsmul ℝ ℝ) volume := rfl
  -- `a` is `C¹`, so `Da` is continuous.
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast le_top)
  have hDa : Continuous (fderiv ℝ a) := ha.continuous_fderiv (by simp)
  refine ⟨hψ ▸ hsupp.contDiff_convolution_right _ hK ha, fun y v => ⟨?_, ?_⟩⟩
  · -- `z ↦ Da(z)v` is continuous with compact support, so the convolution integrand is integrable.
    exact (hsupp.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hK (hDa.clm_apply continuous_const) y
  · -- `Dψ(y) = (K ⋆[precompR] Da)(y)`, evaluated at `v` by `convolution_precompR_apply`.
    rw [hψ, (hsupp.hasFDerivAt_convolution_right _ hK ha1 y).fderiv,
      convolution_precompR_apply _ hK (hsupp.fderiv (𝕜 := ℝ)) hDa]
    rfl
/-- The fundamental theorem of calculus along a ray: for `a` of class `C¹` with compact support
and `θ ≠ 0`, `∫_{(0,∞)} Da(y - rθ)θ dr = a(y)`.  The function `h(r) = a(y - rθ)` is `C¹` with
`h'(r) = -Da(y - rθ)θ`.  It has compact support because `r ↦ y - rθ` is a closed embedding.
So `HasCompactSupport.integral_Ioi_deriv_eq` gives `∫_{(0,∞)} h' = -h(0) = -a(y)`. -/
theorem Submission.rpn_pe_ray_ftc :
    ∀ (n : ℕ) (a : Eucl n → ℝ), ContDiff ℝ 1 a → HasCompactSupport a → ∀ y θ : Eucl n, θ ≠ 0 →
      ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • θ) θ = a y := by
  intro n a ha hsupp y θ hθ
  -- `h(r) = a(y - rθ)` is `C¹` and compactly supported (the line is a closed embedding as `θ ≠ 0`).
  have hh : ContDiff ℝ 1 (fun r : ℝ => a (y - r • θ)) :=
    ha.comp (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have hhsupp : HasCompactSupport (fun r : ℝ => a (y - r • θ)) :=
    hsupp.comp_isClosedEmbedding
      ((Homeomorph.subLeft y).isClosedEmbedding.comp (isClosedEmbedding_smul_left hθ))
  -- Chain rule: `h'(r) = Da(y - rθ)(-θ)`.
  have hderiv : ∀ r : ℝ, deriv (fun r : ℝ => a (y - r • θ)) r = -fderiv ℝ a (y - r • θ) θ := by
    intro r
    have hline : HasDerivAt (fun r : ℝ => y - r • θ) (-θ) r := by
      simpa using ((hasDerivAt_id r).smul_const θ).const_sub y
    exact (((ha.differentiable one_ne_zero) (y - r • θ)).hasFDerivAt.comp_hasDerivAt r
      hline).deriv.trans (map_neg _ _)
  -- FTC on `(0, ∞)`: `∫_{(0,∞)} h' = -h(0) = -a(y)`.
  have key := HasCompactSupport.integral_Ioi_deriv_eq hh hhsupp 0
  simp_rw [hderiv, integral_neg, zero_smul, sub_zero] at key
  exact neg_injective key

/-- **Representation formula (Gilbarg–Trudinger, §7.8, proof of Lemma 7.14).**  For `n = m + 1`,
`ω = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)`, the kernels `K_j(t) = t_j / (n ω |t|ⁿ)` satisfy
`∑_j ∫ K_j(t) ∂_j a(y - t) dt = a(y)`.  Expanding `t` in the standard basis, the sum is `∫ G` with
`G(t) = Da(y - t) t / (n ω |t|ⁿ)`.  In polar coordinates `r^m G(rθ) = Da(y - rθ) θ / (n ω)`, so
each ray integral is `a(y) / (n ω)` (fundamental theorem of calculus along the ray), and the unit
sphere has measure `n ω`. -/
theorem Submission.rpn_pe_kernel_representation : ∀ (m : ℕ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ y : Eucl (m + 1), ∑ j : Fin (m + 1), ∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) = a y := by
  intro m a ha hca y
  -- Step 1: `ω = Lⁿ(B₁(0)) ∈ (0, ∞)`, so `c = (m + 1) ω > 0`.
  set ω : ℝ := (volume (ball (0 : Eucl (m + 1)) 1)).toReal with hω
  set c : ℝ := ((m : ℝ) + 1) * ω with hc
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hc_pos : 0 < c := by positivity
  -- Step 2: `K_j` is locally integrable, so `t ↦ K_j(t) ∂_j a(y - t)` is integrable.
  have hint : ∀ j : Fin (m + 1), Integrable fun t : Eucl (m + 1) =>
      t j / (c * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) := fun j =>
    ((Submission.rpn_pe_convolution_contDiff_fderiv (m + 1) _ a
      (Submission.rpn_pe_kernel_locallyIntegrable m j c) ha hca).2 y _).1
  -- Step 3: move the sum inside the integral.
  rw [← integral_finsetSum _ fun j _ => hint j]
  -- Step 4: `Λ v = ∑_j v_j Λ e_j`, so `∑_j K_j(t) ∂_j a(y - t) = G(t)`.
  have hexp : ∀ (Λ : Eucl (m + 1) →L[ℝ] ℝ) (v : Eucl (m + 1)),
      Λ v = ∑ j : Fin (m + 1), v j * Λ (EuclideanSpace.single j (1 : ℝ)) := by
    intro Λ v
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  set G : Eucl (m + 1) → ℝ := fun t => fderiv ℝ a (y - t) t / (c * ‖t‖ ^ (m + 1)) with hG
  have hsum : (fun t : Eucl (m + 1) => ∑ j : Fin (m + 1),
      t j / (c * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ))) = G := by
    funext t
    simp only [hG]
    rw [hexp (fderiv ℝ a (y - t)) t, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- Step 5: `G` is integrable and the left side is `∫ G`.
  have hG_int : Integrable G := by
    rw [← hsum]
    exact integrable_finsetSum _ fun j _ => hint j
  rw [hsum]
  -- Step 6: polar coordinates.
  rw [Submission.rpn_pe_integral_eq_polar m G hG_int]
  -- Step 7: for `|θ| = 1` and `r > 0`, `r^m G(rθ) = Da(y - rθ) θ / c`; integrate along the ray.
  have hray : ∀ θ : sphere (0 : Eucl (m + 1)) 1,
      ∫ r in Ioi (0 : ℝ), r ^ m * G (r • (θ : Eucl (m + 1))) = a y / c := by
    intro θ
    calc ∫ r in Ioi (0 : ℝ), r ^ m * G (r • (θ : Eucl (m + 1)))
        = ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • (θ : Eucl (m + 1))) θ / c := by
          refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
          simp only [hG]
          rw [norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_of_nonneg hr.le, map_smul,
            smul_eq_mul]
          field_simp
          ring
      _ = (∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • (θ : Eucl (m + 1))) θ) / c := integral_div c _
      _ = a y / c := by
          rw [Submission.rpn_pe_ray_ftc (m + 1) a (ha.of_le (by norm_cast)) hca y θ
            (ne_zero_of_mem_unit_sphere θ)]
  -- Step 8: the inner integral is the constant `a(y) / c`, and `σ(S) = (m + 1) ω = c`.
  rw [integral_congr_ae (Eventually.of_forall hray), integral_const, smul_eq_mul,
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, measureReal_def, ← hω,
    show ((m + 1 : ℕ) : ℝ) * ω = c by rw [hc]; push_cast; ring, mul_div_cancel₀ _ hc_pos.ne']

/-- Sup bound for the kernel potentials (Step 5 of the potential estimate).  With
`ω = Lⁿ(B₁(0))`, `c = (m + 1) ω` and `K_j(t) = t_j / (c |t|^{m+1})`, every compactly supported
`a` with `|a| ≤ M` satisfies `|∫ K_j(t) a(y - t) dt| ≤ C M Lⁿ(spt a)^{1/(m+1)}` with
`C = (m + 2) ω^{m/(m+1)} / c`.  Proof: `|K_j(t) a(y - t)| ≤ (M / c) 1_{S_y}(t) |t|^{-m}` on
`S_y = {t : y - t ∈ spt a}`, a translate of `spt a`; integrate and apply
`rpn_pe_inv_norm_pow_set_bound` to `S_y`.  No measurability of `a` is needed. -/
theorem Submission.rpn_pe_kernel_sup_bound : ∀ m : ℕ, ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ (j : Fin (m + 1)) (y : Eucl (m + 1)), |∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * a (y - t)| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro m
  set ω : ℝ := (volume (ball (0 : Eucl (m + 1)) 1)).toReal
  set c : ℝ := ((m : ℝ) + 1) * ω
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Eucl (m + 1)) one_pos).ne'
      measure_ball_lt_top.ne
  have hc_pos : 0 < c := mul_pos (by positivity) hω_pos
  refine ⟨((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) / c, ?_⟩
  intro a ha M hM j y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- The translated support `S_y = {t : y - t ∈ spt a}` has the measure of `spt a`.
  set S : Set (Eucl (m + 1)) := tsupport a
  set Sy : Set (Eucl (m + 1)) := (fun t => y - t) ⁻¹' S
  have hSy_meas : MeasurableSet Sy :=
    ((isClosed_tsupport a).preimage (continuous_const.sub continuous_id)).measurableSet
  have hvol : volume Sy = volume S :=
    (Measure.measurePreserving_sub_left volume y).measure_preimage
      (isClosed_tsupport a).measurableSet.nullMeasurableSet
  have hSy_fin : volume Sy ≠ ⊤ := by
    rw [hvol]
    exact (IsCompact.measure_lt_top ha).ne
  obtain ⟨hint, hbound⟩ := Submission.rpn_pe_inv_norm_pow_set_bound m Sy hSy_meas hSy_fin
  rw [hvol] at hbound
  -- Pointwise domination by `(M / c) 1_{S_y}(t) |t|^{-m}`.
  have hg_int : Integrable (fun t => M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t) :=
    ((integrable_indicator_iff hSy_meas).2 hint).const_mul (M / c)
  have hdom : ∀ t : Eucl (m + 1), ‖t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)‖ ≤
      M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t := by
    intro t
    by_cases ht : t ∈ Sy
    · rw [indicator_of_mem ht, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hK : |t j / (c * ‖t‖ ^ (m + 1))| ≤ (‖t‖ ^ m)⁻¹ / c := by
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * ‖t‖ ^ (m + 1))]
        rcases (norm_nonneg t).eq_or_lt with h0 | hpos
        · rw [← h0, zero_pow (Nat.succ_ne_zero m), mul_zero, div_zero]
          positivity
        · rw [div_le_iff₀ (by positivity)]
          calc |t j| = ‖t j‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖t‖ := PiLp.norm_apply_le t j
            _ = (‖t‖ ^ m)⁻¹ / c * (c * ‖t‖ ^ (m + 1)) := by
              field_simp
              ring
      calc |t j / (c * ‖t‖ ^ (m + 1))| * |a (y - t)| ≤ (‖t‖ ^ m)⁻¹ / c * M :=
            mul_le_mul hK (hM _) (abs_nonneg _) (by positivity)
        _ = M / c * (‖t‖ ^ m)⁻¹ := by ring
    · have hyt : y - t ∉ tsupport a := ht
      rw [indicator_of_notMem ht, image_eq_zero_of_notMem_tsupport hyt]
      simp
  calc |∫ t, t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)|
      = ‖∫ t, t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t :=
        norm_integral_le_of_norm_le hg_int (Eventually.of_forall hdom)
    _ = M / c * ∫ t in Sy, (‖t‖ ^ m)⁻¹ := by
        rw [integral_const_mul, integral_indicator hSy_meas]
    _ ≤ M / c * (((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) *
          (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hbound (div_nonneg hM0 hc_pos.le)
    _ = ((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) / c * M *
          (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
        ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
