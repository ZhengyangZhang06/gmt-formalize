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

/-- Simon Ch. 6, proof of 4.8–4.9 (p. 158): the integral bounding the right side of 4.11, for a
differentiable approximation `g` of `f` (Simon's `f^{(σ)}`):
`∫ |D(χ ∘ g)| |ω| dμ ≤ c L_W μ(spt ω ∩ {t − h − δ < f < t + δ})` when `|ω| ≤ 1`,
`|g − f| ≤ δ` and `‖Dg‖ ≤ L_W` on `spt ω`, `|χ'| ≤ c` and `χ' = 0` off `(t − h, t)`.
Off `spt ω` the integrand vanishes.  On `spt ω` the chain rule gives
`‖D(χ ∘ g)(x)‖ ≤ |χ'(g x)| ‖Dg(x)‖`; this is `0` unless `t − h < g x < t`, and then
`t − h − δ < f x < t + δ` and the bound is `c L_W`.  Integrate the indicator bound. -/
theorem Submission.slicing_mb_cdb_grad_lintegral_le :
    ∀ (P m : ℕ) (μ : Measure (Eucl P)) (ω : DifferentialForm (Eucl P) m) (f g : Eucl P → ℝ) (LW : ℝ≥0) (χ : ℝ → ℝ) (t h c δ : ℝ), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → Differentiable ℝ g → Differentiable ℝ χ → (∀ x ∈ tsupport ω, |g x - f x| ≤ δ) → (∀ x ∈ tsupport ω, ‖fderiv ℝ g x‖₊ ≤ LW) → (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) → ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) * ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ ≤ ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ)) := by
  intro P m μ ω f g LW χ t h c δ hω hg hχ hgf hDg hc hband
  set E := tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ)
  set a : ℝ≥0∞ := ENNReal.ofReal c * (LW : ℝ≥0∞)
  -- `c ≥ |χ'(0)| ≥ 0`.
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- Pointwise bound of the integrand by `1_E · a`.
  have hpt : ∀ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (covectorEuclideanNorm (ω x)) ≤ E.indicator (fun _ => a) x := by
    intro x
    by_cases hxK : x ∈ tsupport ω
    · -- Chain rule: `D(χ ∘ g)(x) = Dχ(g x) ∘ Dg(x)`.
      have hchain : fderiv ℝ (fun y => χ (g y)) x = (fderiv ℝ χ (g x)).comp (fderiv ℝ g x) :=
        fderiv_fun_comp x (hχ (g x)) (hg x)
      by_cases hgx : g x ∈ Ioo (t - h) t
      · -- `t − h < g x < t` and `|g x − f x| ≤ δ` put `x` in `E`.
        have hxE : x ∈ E := by
          refine ⟨hxK, ?_⟩
          have hab := abs_le.mp (hgf x hxK)
          rw [mem_Ioo] at hgx
          rw [mem_preimage, mem_Ioo]
          constructor <;> linarith [hgx.1, hgx.2, hab.1, hab.2]
        rw [indicator_of_mem hxE]
        have hnorm : ‖fderiv ℝ (fun y => χ (g y)) x‖ ≤ c * LW := by
          rw [hchain]
          calc ‖(fderiv ℝ χ (g x)).comp (fderiv ℝ g x)‖
              ≤ ‖fderiv ℝ χ (g x)‖ * ‖fderiv ℝ g x‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ c * LW := by
              apply mul_le_mul _ _ (norm_nonneg _) hc0
              · rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
                exact hc _
              · exact_mod_cast hDg x hxK
        have h1 : (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) ≤ a := by
          calc (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞)
              = ENNReal.ofReal ‖fderiv ℝ (fun y => χ (g y)) x‖ := (ofReal_norm _).symm
            _ ≤ ENNReal.ofReal (c * LW) := ENNReal.ofReal_le_ofReal hnorm
            _ = a := by rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal]
        have h2 : ENNReal.ofReal (covectorEuclideanNorm (ω x)) ≤ 1 :=
          ENNReal.ofReal_le_one.mpr (hω x)
        calc (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (covectorEuclideanNorm (ω x))
            ≤ a * 1 := mul_le_mul' h1 h2
          _ = a := mul_one _
      · -- `χ'(g x) = 0`, so `Dχ(g x) = 0` and `D(χ ∘ g)(x) = 0`.
        have hfd : fderiv ℝ χ (g x) = 0 := by
          rw [← norm_eq_zero, ← norm_deriv_eq_norm_fderiv, hband _ hgx, norm_zero]
        rw [hchain, hfd]
        simp
    · -- Off `spt ω`, `ω x = 0`.
      have h0 : ω x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0]
  calc ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ
      ≤ ∫⁻ x, E.indicator (fun _ => a) x ∂μ := lintegral_mono hpt
    _ ≤ a * μ E := lintegral_indicator_const_le _ _
/-- Continuity from above for the shrinking level bands (parent proof, Step 6).  With
`δ_j = 1/(j+1)`, the sets `E_j = K ∩ f⁻¹((a − δ_j, b + δ_j))` are Borel (`K` is closed and
`f` is continuous on `K`), decrease in `j`, have intersection `K ∩ f⁻¹([a, b])`, and
`μ(E_0) ≤ μ(K) < ∞`; so `μ(E_j) → μ(K ∩ f⁻¹([a, b]))`. -/
theorem Submission.slicing_mb_cdb_band_measure_tendsto :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (K : Set (Eucl P)) (f : Eucl P → ℝ) (a b : ℝ),
      IsClosed K → ContinuousOn f K → μ K < ∞ →
        Tendsto
          (fun j : ℕ => μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))))
          atTop (𝓝 (μ (K ∩ f ⁻¹' Icc a b))) := by
  intro P μ K f a b hK hf hμK
  -- `E_j = K \ (K ∩ f⁻¹((a − δ_j, b + δ_j)ᶜ))` is Borel.
  have hmeas : ∀ j : ℕ,
      MeasurableSet (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))) := by
    intro j
    have hcl :
        IsClosed (K ∩ f ⁻¹' (Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))ᶜ) :=
      hf.preimage_isClosed_of_isClosed hK isOpen_Ioo.isClosed_compl
    have heq : K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) =
        K \ (K ∩ f ⁻¹' (Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))ᶜ) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [heq]
    exact hK.measurableSet.diff hcl.measurableSet
  -- `δ_j` decreases, so the bands decrease.
  have hanti : Antitone fun j : ℕ =>
      K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) := by
    intro i j hij x hx
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := Nat.one_div_le_one_div hij
    simp only [mem_inter_iff, mem_preimage, mem_Ioo] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  -- `⋂_j E_j = K ∩ f⁻¹([a, b])`.
  have hinter :
      ⋂ j : ℕ, K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) =
        K ∩ f ⁻¹' Icc a b := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Ioo, mem_Icc]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_, ?_⟩
      · by_contra! hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        linarith [(h j).2.1]
      · by_contra! hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        linarith [(h j).2.2]
    · rintro ⟨hxK, hax, hxb⟩ j
      have hδ : 0 < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
      exact ⟨hxK, by linarith, by linarith⟩
  -- `μ(E_0) ≤ μ(K) < ∞`; continuity from above.
  have hfin : ∃ j : ℕ,
      μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))) ≠ ∞ :=
    ⟨0, ((measure_mono inter_subset_left).trans_lt hμK).ne⟩
  have h := tendsto_measure_iInter_atTop (fun j => (hmeas j).nullMeasurableSet) hanti hfin
  rw [hinter] at h
  exact h
/-- Dominated convergence for the bounded continuous multipliers `χ(g_j)` against an integrable
density `F` (the limit `σ ↓ 0` in the cutoff defect bound of the slice mass estimate, Simon Ch. 6,
4.9–4.10): if `F` vanishes off `K` and `g_j → f` on `K`, then `∫ χ(g_j) F dν → ∫ χ(f) F dν`.
The integrands are dominated by `|F|` since `|χ| ≤ 1`, and converge everywhere: on `K` by
continuity of `χ`, off `K` because `F = 0`. -/
theorem Submission.slicing_mb_cdb_multiplier_integral_tendsto :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) (F : Eucl P → ℝ) (K : Set (Eucl P)) (f : Eucl P → ℝ)
      (g : ℕ → Eucl P → ℝ) (χ : ℝ → ℝ), Integrable F ν → (∀ x, x ∉ K → F x = 0) →
      (∀ j, Measurable (g j)) → (∀ x ∈ K, Tendsto (fun j => g j x) atTop (𝓝 (f x))) →
      Continuous χ → (∀ s, |χ s| ≤ 1) →
      Tendsto (fun j => ∫ x, χ (g j x) * F x ∂ν) atTop (𝓝 (∫ x, χ (f x) * F x ∂ν)) := by
  intro P ν F K f g χ hF hFK hg hgf hχ hχ1
  refine tendsto_integral_of_dominated_convergence (fun x => ‖F x‖) (fun j => ?_) hF.norm
    (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · -- `χ ∘ g j` is measurable and `F` is integrable.
    exact (hχ.measurable.comp (hg j)).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · -- `|χ| ≤ 1`.
    rw [norm_mul, Real.norm_eq_abs (χ (g j x))]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 _)
  · -- On `K` by continuity of `χ`; off `K` both sides vanish.
    by_cases hx : x ∈ K
    · exact ((hχ.tendsto (f x)).comp (hgf x hx)).mul_const (F x)
    · simp only [hFK x hx, mul_zero]
      exact tendsto_const_nhds
/-- The mollifier behind Simon's `f^{(σ)}` (Ch. 6, §4, p. 158; parent Step 4): a smooth,
nonnegative, compactly supported `ρ` vanishing off `B(0, σ)` with `∫ ρ = 1`.  Take the bump `φ`
centred at `0` with radii `σ/2 < σ`; then `support φ = B(0, σ)`, so `c = ∫ φ > 0` and
`ρ = c⁻¹ φ` works. -/
theorem Submission.slicing_mb_sa_mollifier_exists :
    ∀ (P : ℕ) (σ : ℝ), 0 < σ → ∃ ρ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧ (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) ∧
      ∫ y, ρ y = 1 := by
  intro P σ hσ
  -- The smooth bump `φ` centred at `0` with `support φ = B(0, σ)`.
  let φ : ContDiffBump (0 : Eucl P) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
  have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  -- Its mass `c = ∫ φ` is positive since `B(0, σ)` has positive Lebesgue measure.
  have hc : 0 < ∫ y, φ y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
    exact measure_ball_pos _ _ hσ
  refine ⟨fun y => (∫ y, φ y)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, fun y => mul_nonneg (inv_nonneg.2 hc.le) φ.nonneg,
    fun y hy => mul_eq_zero_of_right _ (φ.zero_of_le_dist (by rwa [dist_zero_right])), ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hc.ne']
/-- **Uniform error of a mollified Lipschitz function** (Simon Ch. 6, 4.11, p. 158: "use
`f^{(σ)}` in place of `f`").  If `F` is `L`-Lipschitz and `ρ ≥ 0` is continuous with compact
support, `ρ(y) = 0` for `|y| ≥ σ` and `∫ ρ = 1`, then `|∫ ρ(y) F(x − y) dy − F(x)| ≤ L σ`.
As `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`, and pointwise
`|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L |y| ≤ ρ(y) L σ`, since `ρ(y) ≠ 0` forces `|y| < σ`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_close : ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ (ρ : Eucl P → ℝ) (σ : ℝ), Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) → ∫ y, ρ y = 1 → ∀ x : Eucl P, |(∫ y, ρ y * F (x - y)) - F x| ≤ (L : ℝ) * σ := by
  intro P F L hF ρ σ hρc hρs hρ0 hρσ hρ1 x
  -- `ρ` and `y ↦ ρ(y) F(x − y)` are continuous with compact support, hence integrable.
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hgi : Integrable fun y => ρ y * F (x - y) :=
    (hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρs.mul_right
  -- Since `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`.
  have herr : (∫ y, ρ y * F (x - y)) - F x = ∫ y, ρ y * (F (x - y) - F x) := by
    simp_rw [mul_sub]
    rw [integral_sub hgi (hρi.mul_const (F x)), integral_mul_const, hρ1, one_mul]
  -- Pointwise `|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L σ`.
  have hpt : ∀ y, ‖ρ y * (F (x - y) - F x)‖ ≤ ρ y * ((L : ℝ) * σ) := by
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    -- `ρ(y) ≠ 0` forces `|y| < σ`.
    have hyσ : ‖y‖ ≤ σ := (not_le.mp fun h => hy (hρσ y h)).le
    have hlip : |F (x - y) - F x| ≤ (L : ℝ) * σ := by
      rw [← Real.dist_eq]
      calc dist (F (x - y)) (F x) ≤ (L : ℝ) * dist (x - y) x := hF.dist_le_mul _ _
        _ = (L : ℝ) * ‖y‖ := by rw [dist_self_sub_left]
        _ ≤ (L : ℝ) * σ := mul_le_mul_of_nonneg_left hyσ L.coe_nonneg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
    exact mul_le_mul_of_nonneg_left hlip (hρ0 y)
  -- Integrate the pointwise bound, using `∫ ρ = 1` once more.
  rw [herr, ← Real.norm_eq_abs]
  calc ‖∫ y, ρ y * (F (x - y) - F x)‖ ≤ ∫ y, ρ y * ((L : ℝ) * σ) :=
        norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall hpt)
    _ = (L : ℝ) * σ := by rw [integral_mul_const, hρ1, one_mul]
/-- Differentiation under the integral sign for the mollification of a globally Lipschitz `F`
by a continuous compactly supported `ρ`: `D(∫ ρ(y) F(· - y) dy)(x) = ∫ ρ(y) DF(x - y) dy`.
By Rademacher's theorem and the invariance of Lebesgue measure under `y ↦ x - y`, `F` is
differentiable at `x - y` for a.e. `y`; `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz on `ℝ^P`
with integrable majorant `L |ρ|`, so `hasFDerivAt_integral_of_dominated_loc_of_lip` applies
with `s = ℝ^P`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt :
    ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ ρ : Eucl P → ℝ, Continuous ρ →
      HasCompactSupport ρ → ∀ x : Eucl P,
        HasFDerivAt (fun x' : Eucl P => ∫ y, ρ y * F (x' - y))
          (∫ y, ρ y • fderiv ℝ F (x - y)) x := by
  intro P F L hF ρ hρc hρs x
  -- Rademacher, pulled back along the measure-preserving map `y ↦ x - y`.
  have hae : ∀ᵐ y : Eucl P, DifferentiableAt ℝ F (x - y) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      hF.ae_differentiableAt
  -- `y ↦ ρ(y) F(x' - y)` is continuous for every `x'`.
  have hcont : ∀ x' : Eucl P, Continuous fun y : Eucl P => ρ y * F (x' - y) := fun x' =>
    hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))
  -- `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz for every `y`.
  have hlip : ∀ y : Eucl P,
      LipschitzOnWith (Real.nnabs (L * |ρ y|)) (fun x' : Eucl P => ρ y * F (x' - y)) univ := by
    refine fun y => (LipschitzWith.of_dist_le_mul fun a b => ?_).lipschitzOnWith
    calc dist (ρ y * F (a - y)) (ρ y * F (b - y)) = |ρ y| * dist (F (a - y)) (F (b - y)) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      _ ≤ |ρ y| * (L * dist (a - y) (b - y)) := by gcongr; exact hF.dist_le_mul _ _
      _ = Real.nnabs (L * |ρ y|) * dist a b := by
          rw [dist_sub_right, Real.coe_nnabs, abs_mul, abs_abs, NNReal.abs_eq]; ring
  -- For a.e. `y`, the chain rule gives the derivative `ρ(y) DF(x - y)` at `x`.
  have hderiv : ∀ᵐ y : Eucl P,
      HasFDerivAt (fun x' : Eucl P => ρ y * F (x' - y)) (ρ y • fderiv ℝ F (x - y)) x := by
    filter_upwards [hae] with y hy
    have h := hy.hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_mul (ρ y)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip univ_mem
    (Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable)
    ((hcont x).integrable_of_hasCompactSupport hρs.mul_right)
    (hρc.measurable.smul ((measurable_fderiv ℝ F).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall hlip)
    ((hρc.abs.integrable_of_hasCompactSupport hρs.abs).const_mul _) hderiv).2

/-- Simon Ch. 6, 4.11 ("use `f^{(σ)}` in place of `f`") on a compact `K ⊆ W`: if `f` is
`L`-Lipschitz on the open set `W` and `‖Df‖ ≤ LW` a.e. on `W`, then some `C^∞` function `g` is
`δ`-close to `f` on `K` with `‖Dg‖ ≤ LW` on `K`.  Here `g = ρ ⋆ F` mollifies a McShane extension
`F` of `f|W` with a kernel supported in a ball small enough that `x - y ∈ W` whenever `x ∈ K` and
`ρ(y) ≠ 0`. -/
theorem Submission.slicing_mb_smooth_approx :
    ∀ (P : ℕ) (W : Set (Eucl P)), IsOpen W → ∀ (f : Eucl P → ℝ) (L : ℝ≥0),
      LipschitzOnWith L f W → ∀ LW : ℝ≥0,
      (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ W → ∀ δ : ℝ, 0 < δ →
      ∃ g : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∀ x ∈ K, |g x - f x| ≤ δ) ∧
        (∀ x ∈ K, ‖fderiv ℝ g x‖₊ ≤ LW) := by
  intro P W hW f L hf LW hLW K hK hKW δ hδ
  -- The closed `r`-neighbourhood of `K` lies in `W`.
  obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hW hKW
  -- McShane extension: `F` is `L`-Lipschitz on `ℝ^P` and `F = f` on `W`.
  obtain ⟨F, hFL, hfF⟩ := hf.extend_real
  -- The mollification radius: `σ ≤ r` keeps `x - y` in `W`, and `L σ ≤ δ`.
  obtain ⟨σ, hσ, hσr, hσδ⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ r ∧ (L : ℝ) * σ ≤ δ := by
    refine ⟨min r (δ / ((L : ℝ) + 1)), lt_min hr (div_pos hδ (by positivity)), min_le_left _ _, ?_⟩
    calc (L : ℝ) * min r (δ / ((L : ℝ) + 1)) ≤ (L : ℝ) * (δ / ((L : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) L.coe_nonneg
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [L.coe_nonneg]
  obtain ⟨ρ, hρ, hρc, hρ0, hρσ, hρ1⟩ := Submission.slicing_mb_sa_mollifier_exists P σ hσ
  have hρi : Integrable ρ (volume : Measure (Eucl P)) :=
    hρ.continuous.integrable_of_hasCompactSupport hρc
  refine ⟨fun x => ∫ y, ρ y * F (x - y), ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- `g = ρ ⋆ F` is `C^∞`: `ρ` is `C^∞` with compact support and `F` is continuous.
    have hconv : (fun x => ∫ y, ρ y * F (x - y)) =
        convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Eucl P)) := by
      funext x
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [hconv]
    exact hρc.contDiff_convolution_left _ hρ hFL.continuous.locallyIntegrable
  · -- `|g - F| ≤ L σ ≤ δ` everywhere, and `F = f` on `K ⊆ W`.
    rw [hfF (hKW hx)]
    exact (Submission.slicing_mb_sa_mollify_lipschitz_close P F L hFL ρ σ hρ.continuous hρc hρ0
      hρσ hρ1 x).trans hσδ
  · -- `Dg(x) = ∫ ρ(y) DF(x - y) dy`; for a.e. `y` with `ρ(y) ≠ 0`, `x - y ∈ W` and
    -- `‖DF(x - y)‖ = ‖Df(x - y)‖ ≤ LW` (`y ↦ x - y` preserves Lebesgue measure).
    have hDg : fderiv ℝ (fun x => ∫ y, ρ y * F (x - y)) x = ∫ y, ρ y • fderiv ℝ F (x - y) :=
      (Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt P F L hFL ρ hρ.continuous hρc
        x).fderiv
    rw [hDg, ← NNReal.coe_le_coe, coe_nnnorm]
    have hae : ∀ᵐ y ∂(volume : Measure (Eucl P)),
        x - y ∈ W → ‖fderiv ℝ f (x - y)‖₊ ≤ LW :=
      ((volume : Measure (Eucl P)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hLW
    have hbd : ∀ᵐ y ∂(volume : Measure (Eucl P)),
        ‖ρ y • fderiv ℝ F (x - y)‖ ≤ ρ y * LW := by
      filter_upwards [hae] with y hy
      rw [norm_smul, Real.norm_of_nonneg (hρ0 y)]
      rcases eq_or_ne (ρ y) 0 with h0 | h0
      · simp [h0]
      have hyσ : ‖y‖ < σ := not_le.mp fun h => h0 (hρσ y h)
      have hxy : x - y ∈ W := hrW (mem_cthickening_of_dist_le _ x r K hx (by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact hyσ.le.trans hσr))
      have hD : fderiv ℝ F (x - y) = fderiv ℝ f (x - y) :=
        (hfF.symm.eventuallyEq_of_mem (hW.mem_nhds hxy)).fderiv_eq
      rw [hD]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy hxy) (hρ0 y)
    calc ‖∫ y, ρ y • fderiv ℝ F (x - y)‖ ≤ ∫ y, ‖ρ y • fderiv ℝ F (x - y)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, ρ y * (LW : ℝ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hρi.mul_const _) hbd
      _ = LW := by rw [integral_mul_const, hρ1, one_mul]
/-- Simon Ch. 6, 4.11 (Leibniz rule, pointwise): `d(ψω)(x) = ψ(x) dω(x) + Dψ(x) ∧ ω(x)`, the
wedge `Dψ(x) ∧ ω(x)` being the alternatization of `h ↦ Dψ(x)(h) ω(x)`.  As `d = Alt ∘ D`
(Mathlib's `extDeriv`), this is the product rule `D(ψω)(x) = ψ(x) Dω(x) + Dψ(x) ⊗ ω(x)`
followed by linearity of `alternatizeUncurryFin`. -/
theorem Submission.slicing_mb_lb_extDeriv_smul :
    ∀ (P m : ℕ) (ψ : Eucl P → ℝ) (ω : DifferentialForm (Eucl P) m) (x : Eucl P), DifferentiableAt ℝ ψ x → DifferentiableAt ℝ ω x → exteriorDerivative (fun y => ψ y • ω y : DifferentialForm (Eucl P) m) x = ψ x • exteriorDerivative ω x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight (ω x)) := by
  intro P m ψ ω x hψ hω
  simp only [exteriorDerivative, extDeriv]
  rw [fderiv_fun_smul hψ hω, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- Multiplication by a smooth function `ψ` maps `𝒟ᵏ(U)` into itself: `ψ φ` is smooth, and
`spt (ψ φ) ⊆ spt φ`, which is compact and contained in `U`. -/
theorem Submission.slicing_mb_lb_smul_testForm :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (φ : TestFormOn U k) (ψ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ η : TestFormOn U k, ∀ x, (η : DifferentialForm (Eucl P) k) x =
        ψ x • (φ : DifferentialForm (Eucl P) k) x := by
  intro P k U φ ψ hψ
  obtain ⟨⟨hφ, hφc⟩, hφU⟩ := φ.2
  exact ⟨⟨ψ • (φ : DifferentialForm (Eucl P) k), ⟨hψ.smul hφ, hφc.smul_left⟩,
    (tsupport_smul_subset_right ψ _).trans hφU⟩, fun _ => rfl⟩
/-- The wedge `α ∧ ω` of a `C^∞` field `α` of covectors with a test form `ω ∈ 𝒟ᵐ(U)` is a test
form in `𝒟ᵐ⁺¹(U)`, given pointwise by `alternatizeUncurryFin ((α x).smulRight (ω x))`. -/
theorem Submission.slicing_mb_lb_wedge_testForm :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U m) (α : Eucl P → (Eucl P →L[ℝ] ℝ)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α →
      ∃ η : TestFormOn U (m + 1), ∀ x, (η : DifferentialForm (Eucl P) (m + 1)) x =
        ContinuousAlternatingMap.alternatizeUncurryFin
          ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by
  intro P m U ω α hα
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  -- `η` vanishes wherever `ω` does: `(α x).smulRight 0 = 0` and `alternatizeUncurryFin` is linear.
  have hsupp : Function.support (fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ⊆
      Function.support (ω : DifferentialForm (Eucl P) m) := by
    intro x hx h0
    apply hx
    simp only [h0, ContinuousLinearMap.smulRight_zero]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
  -- Hence `η` has compact support and `tsupport η ⊆ tsupport ω ⊆ U`; the formula holds by `rfl`.
  refine ⟨⟨fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)),
    ⟨?_, hωc.mono hsupp⟩, (closure_mono hsupp).trans hωU⟩, fun x => rfl⟩
  -- Smoothness: `x ↦ (α x).smulRight (ω x)` is `C^∞` (bounded bilinear in `(α x, ω x)`), and
  -- `alternatizeUncurryFin` is the continuous linear map `alternatizeUncurryFinCLM`.
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).contDiff.comp
    (hα.smulRight hωs)
/-- **Mass estimate from a normalized measure representation** (Simon Ch. 6, (2.7)).  If
`T(η) = ∫ ⟨η, v⟩ dμ` for every test form `η` and `|⟨α, v(x)⟩| ≤ |α|` for every `x` and every
`n`-covector `α` (Euclidean coefficient norm), then `|T(η)| ≤ ∫ |η| dμ` in `[0, ∞]`. -/
theorem Submission.slicing_mb_lb_repr_bound : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → (∀ (x : Eucl P) (α : Covector (Eucl P) n), |v x α| ≤ covectorEuclideanNorm α) → ∀ η : TestFormOn U n, ENNReal.ofReal |T η| ≤ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x)) ∂μ := by
  intro P n U T μ v hrep hv η
  -- Step 1: `T(η) = ∫ ⟨η(x), v(x)⟩ dμ(x)` by the representation (2.7).
  rw [(hrep η).2, ← Real.enorm_eq_ofReal_abs]
  -- Step 2: `‖∫ g dμ‖ₑ ≤ ∫⁻ ‖g‖ₑ dμ`, which needs no integrability hypothesis.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
  -- Steps 3–4: pointwise `‖⟨η(x), v(x)⟩‖ₑ = ofReal |⟨η(x), v(x)⟩| ≤ ofReal |η(x)|`.
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hv x _)
/-- Counting identity: for any family `u` of vectors of `ℝ^P` and any `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = k! ∑_{I strictly increasing} φ(u_{I 0}, …, u_{I (k-1)})²`,
where `I` ranges over all maps `Fin k → Fin P`. -/
theorem Submission.slicing_mb_wn_sq_sum_eq_factorial_mul :
    ∀ (P k : ℕ) (u : Fin P → Eucl P) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        (k.factorial : ℝ) * ∑ I : Fin k → Fin P,
          if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  classical
  set g : (Fin k → Fin P) → ℝ := fun I => (φ (fun i => u (I i))) ^ 2
  -- A non-injective `I` repeats a vector of `u ∘ I`, so `φ (u ∘ I) = 0`.
  have h0 : ∀ I : Fin k → Fin P, ¬Function.Injective I → g I = 0 := by
    intro I hI
    have hv : ¬Function.Injective (fun i => u (I i)) :=
      fun h => hI fun a b hab => h (by simp only [hab])
    simp only [g, φ.map_eq_zero_of_not_injective _ hv, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  -- `φ (u ∘ I ∘ σ) = sign σ • φ (u ∘ I)`, so the square is invariant under permutations.
  have hperm : ∀ (I : Fin k → Fin P) (σ : Equiv.Perm (Fin k)), g (I ∘ σ) = g I := by
    intro I σ
    have h : φ (fun i => u ((I ∘ σ) i)) = Equiv.Perm.sign σ • φ (fun i => u (I i)) :=
      φ.toAlternatingMap.map_perm (fun i => u (I i)) σ
    simp only [g, h]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h' <;> simp [h']
  -- Write both sides as sums over the injective, resp. strictly increasing, maps.
  have hL : ∑ I, g I = ∑ I ∈ Finset.univ.filter Function.Injective, g I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · exact h0 I h
  have hR : (∑ I : Fin k → Fin P, if StrictMono I then g I else 0) =
      ∑ I ∈ Finset.univ.filter StrictMono, g I := (Finset.sum_filter _ _).symm
  -- `(σ, β) ↦ β ∘ σ` is a bijection from permutations × strictly increasing maps onto the
  -- injective maps, with inverse `I ↦ ((sort I)⁻¹, I ∘ sort I)`.
  have hbij : ∑ I ∈ Finset.univ.filter Function.Injective, g I =
      ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))) ×ˢ Finset.univ.filter StrictMono,
        g (p.2 ∘ p.1) := by
    refine Finset.sum_nbij' (fun I => ((Tuple.sort I)⁻¹, I ∘ Tuple.sort I))
      (fun p => p.2 ∘ p.1) ?_ ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
      exact (Tuple.monotone_sort I).strictMono_of_injective (hI.comp (Tuple.sort I).injective)
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.injective.comp σ.injective
    · intro I _
      funext i
      simp
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      -- sorting `β ∘ σ` recovers the strictly increasing `β`
      have hsorted : (β ∘ σ) ∘ Tuple.sort (β ∘ σ) = β := by
        rw [Tuple.comp_perm_comp_sort_eq_comp_sort,
          (Tuple.sort_eq_refl_iff_monotone).2 hp.monotone]
        rfl
      have hσ : σ * Tuple.sort (β ∘ σ) = 1 := by
        ext i
        have := congrFun hsorted i
        simp only [Function.comp_apply] at this
        simpa using congrArg Fin.val (hp.injective this)
      have hinv : (Tuple.sort (β ∘ σ))⁻¹ = σ := by
        rw [inv_eq_iff_eq_inv]
        exact eq_inv_of_mul_eq_one_right hσ
      simp only [hinv, hsorted]
    · intro I _
      congr 1
      funext i
      simp
  -- Each permutation contributes `∑_β g β`, and there are `k!` permutations.
  rw [hL, hbij, hR, Finset.sum_product]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- Basis independence of the full coefficient sum (Parseval's identity, one slot at a time): for
orthonormal bases `u`, `v` of `ℝ^P` and a `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = ∑_I φ(v_{I 0}, …, v_{I (k-1)})²`, both sums over all index maps
`I : Fin k → Fin P`.  Induction on `k`: write `I = (i, J)` and `φ(w_I) = (φ.curryLeft w_i)(w_J)`,
replace `u` by `v` in the last `k` slots by the induction hypothesis for `φ.curryLeft (u i)`, then
in slot `0` by `OrthonormalBasis.norm_dual` for the functional `z ↦ (φ.curryLeft z)(v_J)`. -/
theorem Submission.slicing_mb_wn_sq_sum_onb_invariant :
    ∀ (P k : ℕ) (u v : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        ∑ I : Fin k → Fin P, (φ (fun i => v (I i))) ^ 2 := by
  intro P k u v
  induction k with
  | zero =>
    -- Both families are the empty tuple.
    intro φ
    exact Fintype.sum_congr _ _ fun I => by
      rw [Subsingleton.elim (fun i => u (I i)) (fun i => v (I i))]
  | succ k ih =>
    intro φ
    -- Split `I = Fin.cons i J`; then `φ(w_I) = (φ.curryLeft w_i)(w_J)`.
    have hsplit : ∀ w : OrthonormalBasis (Fin P) ℝ (Eucl P),
        ∑ I : Fin (k + 1) → Fin P, (φ (fun i => w (I i))) ^ 2 =
          ∑ i : Fin P, ∑ J : Fin k → Fin P, (φ.curryLeft (w i) (fun j => w (J j))) ^ 2 := by
      intro w
      rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Fin P).sum_comp]
      refine Fintype.sum_congr _ _ fun p => ?_
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    -- Slots `1, …, k`: the induction hypothesis for each `k`-covector `φ.curryLeft (u i)`.
    rw [hsplit u, hsplit v]
    simp_rw [ih]
    -- Slot `0`: for each `J`, Parseval for `ℓ_J z = (φ.curryLeft z)(v_J)` in the bases `u`, `v`.
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun J => ?_
    let ℓ : StrongDual ℝ (Eucl P) :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (fun j => v (J j))).comp φ.curryLeft
    have hu := u.norm_dual ℓ
    have hv := v.norm_dual ℓ
    simp only [ℓ, ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.apply_apply] at hu hv
    rw [← hu, ← hv]

/-- The Euclidean coefficient norm of a `k`-covector can be computed in any orthonormal basis
`u` of `ℝ^P` (Simon Ch. 6, 1.5–1.6 and Remark 2.6): `|φ|² = ∑_{I increasing} φ(u_I)²`.
With `e` the standard basis used by `covectorEuclideanNorm` and `N_w(φ) = ∑_{all I} φ(w_I)²`,
`k! |φ|² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`, and `k! ≠ 0`. -/
theorem Submission.slicing_mb_wn_norm_sq_eq_onb_sum :
    ∀ (P k : ℕ) (u : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      covectorEuclideanNorm φ ^ 2 =
        ∑ I : Fin k → Fin P, if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  -- `k! ∑_{I increasing} φ(e_I)² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`.
  have key := (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k
      (EuclideanSpace.basisFun (Fin P) ℝ) φ).symm.trans
    ((Submission.slicing_mb_wn_sq_sum_onb_invariant P k
      (EuclideanSpace.basisFun (Fin P) ℝ) u φ).trans
        (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k u φ))
  -- `|φ|² = ∑_{I increasing} φ(e_I)²`: the radicand is a sum of squares and zeros.
  rw [covectorEuclideanNorm, Real.sq_sqrt]
  · exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) key
  · exact Finset.sum_nonneg fun I _ => by split_ifs <;> positivity
/-- Every continuous linear functional `α` on `ℝ^P` has an adapted orthonormal basis `u`:
`α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`. -/
theorem Submission.slicing_mb_wn_adapted_onb :
    ∀ (P : ℕ) (α : Eucl P →L[ℝ] ℝ), ∃ u : OrthonormalBasis (Fin P) ℝ (Eucl P),
      ∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then ‖α‖ else 0 := by
  intro P α
  by_cases hα : α = 0
  · -- `α = 0`: the standard basis works, since `‖α‖ = 0`.
    exact ⟨EuclideanSpace.basisFun (Fin P) ℝ, fun j => by simp [hα]⟩
  -- The Riesz vector `a` of `α`: `α z = ⟪a, z⟫` and `‖a‖ = ‖α‖ > 0`.
  set a : Eucl P := (InnerProductSpace.toDual ℝ (Eucl P)).symm α
  have hαa : ∀ z, α z = inner ℝ a z := fun z => InnerProductSpace.toDual_symm_apply.symm
  have hna : ‖a‖ = ‖α‖ := LinearIsometryEquiv.norm_map _ _
  have hpos : 0 < ‖a‖ := hna ▸ norm_pos_iff.mpr hα
  have ha0 : a ≠ 0 := norm_pos_iff.mp hpos
  -- `a ≠ 0` forces `P ≥ 1`, so the index `0` exists.
  have hP : 0 < P := by
    have := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mpr ⟨a, ha0⟩
    rwa [finrank_euclideanSpace_fin] at this
  set i₀ : Fin P := ⟨0, hP⟩
  -- Extend the unit vector `‖a‖⁻¹ • a`, placed at index `i₀`, to an orthonormal basis `u`.
  obtain ⟨u, hu⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := Eucl P) (by simp) (v := fun _ => ‖a‖⁻¹ • a) (s := {i₀})
    (by
      rw [orthonormal_subsingleton_iff]
      intro i
      exact norm_smul_inv_norm ha0)
  have hu₀ : u i₀ = ‖a‖⁻¹ • a := hu i₀ (Set.mem_singleton _)
  have haU : a = ‖a‖ • u i₀ := by rw [hu₀, smul_inv_smul₀ hpos.ne']
  -- `α(uⱼ) = ‖a‖ ⟪u₀, uⱼ⟫`, which is `‖a‖ = ‖α‖` for `j = 0` and `0` otherwise.
  refine ⟨u, fun j => ?_⟩
  rw [hαa, haU, real_inner_smul_left]
  split_ifs with hj
  · have : j = i₀ := Fin.ext hj
    subst this
    rw [real_inner_self_eq_norm_sq, u.orthonormal.norm_eq_one, one_pow, mul_one, hna]
  · have : i₀ ≠ j := fun h => hj (by rw [← h])
    rw [u.orthonormal.inner_eq_zero this, mul_zero]
/-- Coefficient sum of `α ∧ γ` on a family adapted to `α`: if `α (u j)` is `c` for `j = 0` and
`0` otherwise, then `∑_{I increasing} ((α ∧ γ)(u_I))² ≤ c² ∑_{J increasing} γ(u_J)²`, where
`α ∧ γ = alternatizeUncurryFin (α.smulRight γ)`.  The family `u` need not be orthonormal. -/
theorem Submission.slicing_mb_wn_adapted_sum_le :
    ∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m) (u : Fin P → Eucl P) (c : ℝ), (∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then c else 0) → (∑ I : Fin (m + 1) → Fin P, if StrictMono I then (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2 else 0) ≤ c ^ 2 * ∑ I : Fin m → Fin P, if StrictMono I then (γ (fun i => u (I i))) ^ 2 else 0 := by
  intro P m α γ u c hα
  -- Steps 1–2: on a strictly increasing `I`, every term of the wedge formula with `i ≥ 1`
  -- vanishes, because `I i > I 0 ≥ 0` forces `α (u (I i)) = 0`.
  have hval : ∀ I : Fin (m + 1) → Fin P, StrictMono I →
      ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i)) =
        α (u (I 0)) * γ (fun j => u (I j.succ)) := by
    intro I hI
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
      Finset.sum_eq_zero fun i _ => ?_, add_zero]
    · simp only [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero,
        ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rfl
    · have h : ((I 0 : Fin P) : ℕ) < (I i.succ : ℕ) := hI (Fin.succ_pos i)
      have h0 : ((I i.succ : Fin P) : ℕ) ≠ 0 := by omega
      simp [hα, h0]
  -- Step 3: the summands of the left side vanish unless `I` is strictly increasing with
  -- `I 0 = 0`, where they equal `c ^ 2 * γ (u ∘ I ∘ succ) ^ 2`.
  have hL : ∀ I : Fin (m + 1) → Fin P,
      (if StrictMono I then
        (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2
        else 0) =
      if StrictMono I ∧ ((I 0 : Fin P) : ℕ) = 0 then
        c ^ 2 * (γ (fun j => u (I j.succ))) ^ 2 else 0 := by
    intro I
    by_cases hI : StrictMono I
    · rw [hval I hI, hα (I 0)]
      by_cases h0 : ((I 0 : Fin P) : ℕ) = 0 <;> simp [hI, h0, mul_pow]
    · simp [hI]
  rw [Finset.sum_congr rfl fun I _ => hL I, ← Finset.sum_filter, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  -- Steps 4–5: `I ↦ I ∘ succ` is injective on `{I | StrictMono I ∧ I 0 = 0}` and maps it into
  -- the strictly increasing `m`-tuples; the remaining summands are nonnegative squares.
  have hinj : Set.InjOn (fun (I : Fin (m + 1) → Fin P) (j : Fin m) => I j.succ)
      (Finset.univ.filter fun I : Fin (m + 1) → Fin P =>
        StrictMono I ∧ ((I 0 : Fin P) : ℕ) = 0) := by
    intro I hI I' hI' h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hI hI'
    funext i
    refine Fin.cases ?_ (fun j => congrFun h j) i
    exact Fin.ext (hI.2.trans hI'.2.symm)
  rw [← Finset.sum_filter,
    ← Finset.sum_image (f := fun J : Fin m → Fin P => (γ (fun i => u (J i))) ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun J _ _ => sq_nonneg _
  intro J hJ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
  obtain ⟨I, ⟨hI, _⟩, rfl⟩ := hJ
  exact hI.comp Fin.strictMono_succ

/-- The wedge estimate behind the bound on the right side of Simon Ch. 6, 4.11 (proof of 4.8–4.9):
for a covector `α` and an `m`-covector `γ` on `ℝ^P`, the Euclidean coefficient norm of
`α ∧ γ = alternatizeUncurryFin (α.smulRight γ)` is at most `‖α‖ |γ|`.  The coefficient norm can
be computed in any orthonormal basis.  In a basis `u` with `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for
`j ≠ 0`, the coefficients of `α ∧ γ` are `‖α‖` times coefficients of `γ` on pairwise distinct
multi-indices, so `|α ∧ γ|² ≤ ‖α‖² |γ|²`. -/
theorem Submission.slicing_mb_wedge_norm_le :
    ∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m),
      covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ)) ≤
        ‖α‖ * covectorEuclideanNorm γ := by
  intro P m α γ
  -- An orthonormal basis adapted to `α`: `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`.
  obtain ⟨u, hu⟩ := Submission.slicing_mb_wn_adapted_onb P α
  refine (sq_le_sq₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (norm_nonneg α) (covectorEuclideanNorm_nonneg γ))).1 ?_
  -- Both squared norms are sums over increasing multi-indices in `u`, and there
  -- `Σ_{I incr} (α ∧ γ)(u_I)² ≤ ‖α‖² Σ_{J incr} γ(u_J)²`.
  rw [mul_pow, Submission.slicing_mb_wn_norm_sq_eq_onb_sum P (m + 1) u,
    Submission.slicing_mb_wn_norm_sq_eq_onb_sum P m u]
  exact Submission.slicing_mb_wn_adapted_sum_le P m α γ u ‖α‖ hu

/-- **Boundary defect of a smooth multiplier** (Simon Ch. 6, 4.11, with the representation
estimate (2.7) and the wedge bound): if `(μ, v)` represents `T ∈ 𝒟ₘ₊₁(U)` with
`|⟨α, v⟩| ≤ |α|`, `ω ∈ 𝒟ᵐ(U)` and `ψ` is `C^∞`, then `η₁ = ψω` and `η₂ = ψ dω` are test forms
with `|∂T(η₁) − T(η₂)| ≤ ∫ |Dψ| |ω| dμ`.  The Leibniz rule `d(ψω) = ψ dω + Dψ ∧ ω` gives
`∂T(η₁) − T(η₂) = T(Dψ ∧ ω)`, bounded by the representation and `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|`. -/
theorem Submission.slicing_mb_leibniz_bound :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
      (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
      ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ (η₁ : TestFormOn U m) (η₂ : TestFormOn U (m + 1)),
        (∀ x, (η₁ : DifferentialForm (Eucl P) m) x = ψ x • (ω : DifferentialForm (Eucl P) m) x) ∧
        (∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x =
          ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∧
        ENNReal.ofReal |T.boundary η₁ - T η₂| ≤
          ∫⁻ x, (‖fderiv ℝ ψ x‖₊ : ℝ≥0∞) *
            ENNReal.ofReal (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x)) ∂μ := by
  intro P m U T μ v hrep hnorm ω ψ hψ
  -- The test forms `η₁ = ψ ω`, `η₂ = ψ dω` and `η₃ = Dψ ∧ ω` in `U`.
  obtain ⟨η₁, hη₁⟩ := Submission.slicing_mb_lb_smul_testForm P m U ω ψ hψ
  obtain ⟨η₂, hη₂⟩ :=
    Submission.slicing_mb_lb_smul_testForm P (m + 1) U (exteriorDerivativeTestOn U m ω) ψ hψ
  obtain ⟨η₃, hη₃⟩ :=
    Submission.slicing_mb_lb_wedge_testForm P m U ω (fderiv ℝ ψ) (hψ.fderiv_right (by simp))
  have hη₂' : ∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x =
      ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x := hη₂
  refine ⟨η₁, η₂, hη₁, hη₂', ?_⟩
  -- Leibniz rule: `dη₁ = ψ dω + Dψ ∧ ω = η₂ + η₃`.
  have hd : exteriorDerivativeTestOn U m η₁ = η₂ + η₃ := by
    apply Subtype.ext
    funext x
    have h₁ : (η₁ : DifferentialForm (Eucl P) m) =
        fun y => ψ y • (ω : DifferentialForm (Eucl P) m) y := funext hη₁
    change exteriorDerivative (η₁ : DifferentialForm (Eucl P) m) x =
      (η₂ : DifferentialForm (Eucl P) (m + 1)) x + (η₃ : DifferentialForm (Eucl P) (m + 1)) x
    rw [h₁, hη₂', hη₃, Submission.slicing_mb_lb_extDeriv_smul P m ψ
      (ω : DifferentialForm (Eucl P) m) x (hψ.differentiable (by simp) x)
      (ω.2.1.1.differentiable (by simp) x)]
  -- Hence `∂T(η₁) − T(η₂) = T(η₃)`.
  have hb : T.boundary η₁ - T η₂ = T η₃ := by
    rw [GeometricCurrentOn.boundary_apply, hd, map_add, add_sub_cancel_left]
  -- The representation bound for `T(η₃)`, then `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|` pointwise.
  rw [hb]
  refine (Submission.slicing_mb_lb_repr_bound P (m + 1) U T μ v hrep hnorm η₃).trans
    (lintegral_mono fun x => ?_)
  rw [hη₃, ← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Submission.slicing_mb_wedge_norm_le P m _ _)

/-- The cut-off defect bound in the proof of Simon Ch. 6, 4.9 for Lipschitz `f` (4.11 and the
bound of its right side, p. 158, with `f^{(σ)}` in place of `f`, then `σ ↓ 0`).  Let
`K = spt ω ⊆ W`, `|ω| ≤ 1`, `|v| ≤ 1` on covectors, `|Df| ≤ L_W` a.e. on the open `W ⊆ U`, and
`|χ| ≤ 1`, `|χ'| ≤ c`, `χ' = 0` off `(t - h, t)`.  Then
`|∫ χ(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ(f) ⟨dω, v₁⟩ dμ₁| ≤ c L_W μ(K ∩ {t - h ≤ f ≤ t})`, i.e.
`∂T(χ(f) ω) - T(χ(f) dω)` computed through the representations of `∂T` and `T`.  For smooth
`g_j` with `|g_j - f| ≤ 1/(j+1)` and `|Dg_j| ≤ L_W` on `K`, 4.11 for `ψ_j = χ ∘ g_j` gives the
bound with the band `K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)}`; let `j → ∞` by dominated
convergence on the left and continuity from above on the right. -/
theorem Submission.slicing_mb_cutoff_defect_bound :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) →
      (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
      ∀ (μ₁ : Measure (Eucl P)) (v₁ : Eucl P → NVector (Eucl P) (m + 1)),
      IsMeasureRepresentation T μ₁ v₁ →
      ∀ (μ₂ : Measure (Eucl P)) (v₂ : Eucl P → NVector (Eucl P) m),
      IsMeasureRepresentation T.boundary μ₂ v₂ →
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
      ∀ W : Set (Eucl P), IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Eucl P) m) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x) ≤ 1) →
      ∀ (χ : ℝ → ℝ) (t h c : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → (∀ s, |χ s| ≤ 1) →
      (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) →
      ENNReal.ofReal |∫ x, χ (f x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ -
        ∫ x, χ (f x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤
      ENNReal.ofReal c * (LW : ℝ≥0∞) *
        μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩ f ⁻¹' Icc (t - h) t) := by
  intro P m U T μ v hμv hμK hv μ₁ v₁ hμ₁ μ₂ v₂ hμ₂ f L hf W hW hWU LW hLW ω hωW hω1 χ t h c hχ
    hχ1 hχc hχ0
  -- `K = spt ω` is compact and `K ⊆ W ⊆ U`.
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) m)) := ω.property.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U := hωW.trans hWU
  -- Smooth `g_j` with `|g_j - f| ≤ 1/(j+1)` and `‖Dg_j‖ ≤ L_W` on `K`.
  choose g hg hgf hgD using fun j : ℕ =>
    Submission.slicing_mb_smooth_approx P W hW f L (hf.mono hWU) LW hLW _ hKc hωW
      (1 / ((j : ℝ) + 1)) (by positivity)
  -- 4.11 for `ψ_j = χ ∘ g_j`, evaluated through the representations of `∂T` and `T`; its right
  -- side is at most `c L_W μ(K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)})`.
  have key : ∀ j : ℕ,
      ENNReal.ofReal |∫ x, χ (g j x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ -
        ∫ x, χ (g j x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤
      ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩
        f ⁻¹' Ioo (t - h - 1 / ((j : ℝ) + 1)) (t + 1 / ((j : ℝ) + 1))) := by
    intro j
    obtain ⟨η₁, η₂, hη₁, hη₂, hle⟩ := Submission.slicing_mb_leibniz_bound P m U T μ v hμv hv ω
      (fun y => χ (g j y)) (hχ.comp (hg j))
    have e₁ : T.boundary η₁ =
        ∫ x, χ (g j x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ := by
      rw [(hμ₂ η₁).2]
      congr 1
      funext x
      rw [hη₁ x, map_smul, smul_eq_mul]
    have e₂ : T η₂ =
        ∫ x, χ (g j x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁ := by
      rw [(hμ₁ η₂).2]
      congr 1
      funext x
      rw [hη₂ x, map_smul, smul_eq_mul]
    rw [← e₁, ← e₂]
    exact hle.trans (Submission.slicing_mb_cdb_grad_lintegral_le P m μ _ f (g j) LW χ t h c
      (1 / ((j : ℝ) + 1)) hω1 ((hg j).differentiable (by simp)) (hχ.differentiable (by simp))
      (hgf j) (hgD j) hχc hχ0)
  -- `g_j → f` pointwise on `K`.
  have hconv : ∀ x ∈ tsupport (ω : DifferentialForm (Eucl P) m),
      Tendsto (fun j => g j x) atTop (𝓝 (f x)) := by
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact hgf j x hx
  -- Left side: dominated convergence in both integrals, whose densities vanish off `K`.
  have hL₂ := Submission.slicing_mb_cdb_multiplier_integral_tendsto P μ₂
    (fun x => v₂ x ((ω : DifferentialForm (Eucl P) m) x)) _ f g χ (hμ₂ ω).1
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun j => (hg j).continuous.measurable) hconv hχ.continuous hχ1
  have hL₁ := Submission.slicing_mb_cdb_multiplier_integral_tendsto P μ₁
    (fun x => v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x)) _ f g χ
    (hμ₁ (exteriorDerivativeTestOn U m ω)).1
    (fun x hx => by
      have hx' : x ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Eucl P) m)) :=
        fun h' => hx (tsupport_exteriorDerivative_subset _ h')
      simp [image_eq_zero_of_notMem_tsupport hx'])
    (fun j => (hg j).continuous.measurable) hconv hχ.continuous hχ1
  -- Right side: continuity from above for the bands, as `μ(K) < ∞`.
  have hR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c * (LW : ℝ≥0∞))
    (Submission.slicing_mb_cdb_band_measure_tendsto P μ _ f (t - h) t (isClosed_tsupport _)
      (hf.continuousOn.mono hKU) (hμK _ hKc hKU))
    (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  exact le_of_tendsto_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp (hL₂.sub hL₁).abs)
    hR key

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
