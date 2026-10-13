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

/-- Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): an integer
multiplicity `Y = τ(M, θ, ξ) ∈ 𝒟₀(U)` is a locally finite integer combination of point masses,
`Y(ω) = ∑_{x ∈ N} c(x) ω(x)` with `c(x) ≠ 0` on `N = M`.  `H⁰` is counting measure, so `H⁰`-null
sets are empty and sets of finite `H⁰` measure are finite.  As `θ ≥ 1` on `M` and `θ` is locally
`H⁰`-integrable, `M ∩ K` is finite for compact `K ⊆ U`; the orientation condition holds at every
point of `M`, where `ξ(x) = ±[[x]]`, so `c(x) = θ(x) ξ(x)(1) = ±θ(x)` is a nonzero integer, and the
integral over `M` reduces to the finite sum over `M ∩ spt ω`. -/
theorem Submission.br_zd_im_dirac_repr :
    ∀ (P : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U 0), IsIntegerMultiplicity Y → ∃ (N : Set (Eucl P)) (c : Eucl P → ℤ), N ⊆ U ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) ∧ (∀ x ∈ N, c x ≠ 0) ∧ ∀ ω : TestFormOn U 0, Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  classical
  rintro P U Y ⟨M, θ, ξ, hT, hθ, hY⟩
  set μ : Measure (Eucl P) := (μHE[0] : Measure (Eucl P)) with hμ
  -- `H⁰ = μH[0]` gives every point mass `1`.
  have hpt : ∀ x : Eucl P, μ {x} = 1 := fun x => by
    rw [hμ, Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  -- `H⁰`-null sets are empty.
  have hnull : ∀ E : Set (Eucl P), μ E = 0 → E = ∅ := by
    intro E hE
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have h1 := measure_mono (μ := μ) (singleton_subset_iff.2 hx)
    rw [hpt, hE] at h1
    exact absurd h1 (by simp)
  -- `H⁰` of a finset is its cardinality.
  have hcard : ∀ F : Finset (Eucl P), μ (F : Set (Eucl P)) = F.card := by
    intro F
    rw [← sum_measure_singleton]
    simp [hpt]
  -- Sets of finite `H⁰` measure are finite.
  have hfin : ∀ E : Set (Eucl P), μ E < ∞ → E.Finite := by
    intro E hE
    by_contra hinf
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hE.ne
    obtain ⟨F, hFE, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have h1 := measure_mono (μ := μ) hFE
    rw [hcard, hFcard] at h1
    exact absurd (h1.trans_lt hn) (lt_irrefl _)
  -- Integrals over finsets are finite sums.
  have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ), IntegrableOn g (F : Set (Eucl P)) μ := by
    intro F g
    rw [← biUnion_of_singleton (F : Set (Eucl P)), Finset.set_biUnion_coe,
      integrableOn_finset_iUnion]
    exact fun x _ => integrableOn_singleton (hx := by rw [hpt]; exact ENNReal.one_lt_top)
  have hsum : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      ∫ x in (F : Set (Eucl P)), g x ∂μ = ∑ x ∈ F, g x := by
    intro F g
    rw [setIntegral_finset F (hint F g)]
    simp only [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
  -- `θ ≥ 1` on `M`.
  have hθ1 : ∀ x ∈ M, (1 : ℝ) ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθ x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hpos)
  -- Local finiteness: `H⁰(M ∩ K) ≤ ∫_{M ∩ K} θ dH⁰ < ∞`.
  have hlocfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (M ∩ K).Finite := by
    intro K hK hKU
    apply hfin
    have hMK : NullMeasurableSet (M ∩ K) μ :=
      hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
    have h1 : IntegrableOn (fun _ => (1 : ℝ)) (M ∩ K) μ := by
      refine (hT.integrableOn K hK hKU).mono' aestronglyMeasurable_const ?_
      filter_upwards [ae_restrict_mem₀ hMK] with x hx
      simpa using hθ1 x hx.1
    rcases (integrableOn_const_iff (by simp)).1 h1 with h | h
    · simp at h
    · exact h
  -- Orientation at every point of `M`: its failure set is `H⁰`-null in `M`, hence empty.
  set ε : NVector (Eucl P) 0 := simpleNVector (![] : Fin 0 → Eucl P) with hε
  have horient : ∀ x ∈ M, ξ x = ε ∨ ξ x = -ε := by
    have h := hT.orients
    rw [Filter.Eventually, mem_ae_iff] at h
    have h2 := Measure.le_restrict_apply (μ := μ) (s := M) _ |>.trans_eq h
    rw [nonpos_iff_eq_zero] at h2
    have h3 := hnull _ h2
    intro x hx
    have hx' : x ∉ {x | ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
        (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)}ᶜ := by
      intro hmem
      have : x ∈ ({x | ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
        (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)}ᶜ ∩ M) := ⟨hmem, hx⟩
      rw [h3] at this
      exact this
    rw [Set.notMem_compl_iff] at hx'
    obtain ⟨τ, -, -, hτ⟩ := hx'
    rwa [Subsingleton.elim τ ![]] at hτ
  -- The unit `0`-covector `1`: every `0`-covector is `α = α(![]) • 1`.
  set one0 : Covector (Eucl P) 0 :=
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) 1 with hone0
  have hdecomp : ∀ (α : Covector (Eucl P) 0), α = α ![] • one0 := by
    intro α
    ext v
    rw [Subsingleton.elim v ![]]
    simp [one0]
  have hpair : ∀ (w : NVector (Eucl P) 0) (α : Covector (Eucl P) 0), w α = α ![] * w one0 := by
    intro w α
    conv_lhs => rw [hdecomp α]
    rw [map_smul, smul_eq_mul]
  -- The coefficients `c(x) = ⌊θ(x) ξ(x)(1)⌋`, equal to `±θ(x) ∈ ℤ ∖ {0}` on `M`.
  let c : Eucl P → ℤ := fun x => ⌊θ x * ξ x one0⌋
  have hcM : ∀ x ∈ M, (c x : ℝ) = θ x * ξ x one0 ∧ c x ≠ 0 := by
    intro x hx
    obtain ⟨k, hk⟩ := hθ x hx
    have hk1 : (1 : ℝ) ≤ k := hk ▸ hθ1 x hx
    have hk1' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
    have hεone : ε one0 = 1 := by simp [ε, one0]
    rcases horient x hx with h | h
    · have he : θ x * ξ x one0 = ((k : ℤ) : ℝ) := by rw [h, hεone, hk]; simp
      refine ⟨by simp only [c, he, Int.floor_intCast], ?_⟩
      simp only [c, he, Int.floor_intCast]
      omega
    · have he : θ x * ξ x one0 = (Int.cast (-(k : ℤ)) : ℝ) := by
        rw [h, neg_apply, hεone, hk]; simp
      refine ⟨by simp only [c, he, Int.floor_intCast], ?_⟩
      simp only [c, he, Int.floor_intCast]
      omega
  refine ⟨M, c, hT.subset, hlocfin, fun x hx => (hcM x hx).2, ?_⟩
  -- The integral over `M` is the finite sum over `S = M ∩ spt ω`.
  intro ω
  set f : DifferentialForm (Eucl P) 0 := (ω : DifferentialForm (Eucl P) 0) with hf
  have hKc : IsCompact (tsupport f) := ω.property.1.2
  have hKU : tsupport f ⊆ U := ω.property.2
  have hSfin : (M ∩ tsupport f).Finite := hlocfin _ hKc hKU
  set S : Finset (Eucl P) := hSfin.toFinset with hS
  have hSM : (S : Set (Eucl P)) = M ∩ tsupport f := hSfin.coe_toFinset
  have hzero : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  rw [hY ω, tauAction]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := (S : Set (Eucl P))) hT.nullMeasurableSet
    (by rw [hSM]; exact inter_subset_left) (Eventually.of_forall fun x hx => ?_)]
  · rw [hsum, finsum_mem_eq_sum_of_subset _ (t := S) ?_ (by rw [hSM]; exact inter_subset_left)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hxM : x ∈ M := by
        have : x ∈ (S : Set (Eucl P)) := hx
        rw [hSM] at this
        exact this.1
      rw [hpair, (hcM x hxM).1]
      ring
    · rintro x ⟨hxM, hx0⟩
      rw [hSM]
      refine ⟨hxM, subset_tsupport _ ?_⟩
      intro hfx
      apply hx0
      simp [hfx]
  · have hx' : x ∉ tsupport f := fun h => hx.2 (by rw [hSM]; exact ⟨hx.1, h⟩)
    have h0 : (ω : DifferentialForm (Eucl P) 0) x = 0 := hzero x hx'
    simp [h0]

/-- The mass lower bound for a locally finite Dirac sum (the `0`-dimensional step in the proof of
Simon Ch. 6, 6.3): if `Y(ω) = ∑ᶠ_{x ∈ N} c(x) ω(x)` with `N ∩ K` finite for compact `K ⊆ U`, then
`∑_{x ∈ S} |c(x)| ≤ M_W(Y)` for every finite `S ⊆ N ∩ W`, `W ⊆ U` open.  Test with
`ω = ∑_{x ∈ S} sign(c(x)) φₓ`, where the bumps `φₓ` (`φₓ(x) = 1`) have pairwise disjoint
supports `B(x, δ) ⊆ W` meeting `N` only in `x`: then `|ω| ≤ 1` and `Y(ω) = ∑_{x ∈ S} |c(x)|`. -/
theorem Submission.br_zd_dirac_massOn_ge :
    ∀ (P : ℕ) (U W N : Set (Eucl P)) (Y : GeometricCurrentOn U 0) (c : Eucl P → ℤ), IsOpen W →
      W ⊆ U → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) →
      (∀ ω : TestFormOn U 0,
        Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) →
      ∀ S : Finset (Eucl P), (↑S : Set (Eucl P)) ⊆ N ∩ W →
        ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) ≤ Y.massOn W := by
  classical
  intro P U W N Y c hW hWU hN hY S hS
  -- A common radius `δ > 0`: for `x ∈ S`, `B̄(x, 2δ) ⊆ W` and `N ∩ B̄(x, 2δ) = {x}`.
  have hloc : ∀ x ∈ S, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      closedBall x (2 * δ) ⊆ W ∧ ∀ y ∈ N, dist y x ≤ 2 * δ → y = x := by
    intro x hx
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW x (hS hx).2
    have hfin : (N ∩ closedBall x (r / 2)).Finite :=
      hN _ (isCompact_closedBall x (r / 2))
        (((closedBall_subset_ball (half_lt_self hr)).trans hrW).trans hWU)
    obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.mp
      (hfin.subset (sdiff_subset (t := {x}))).isClosed.isOpen_compl x (by simp)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (r / 4) (ε / 4) by positivity)]
      with δ ⟨hδ0, hδ⟩
    have h1 : δ < r / 4 := hδ.trans_le (min_le_left _ _)
    have h2 : δ < ε / 4 := hδ.trans_le (min_le_right _ _)
    refine ⟨(closedBall_subset_ball (by linarith)).trans hrW, fun y hyN hyx => ?_⟩
    by_contra hne
    exact hεF (mem_ball.2 (by linarith)) ⟨⟨hyN, mem_closedBall.2 (by linarith)⟩, hne⟩
  obtain ⟨δ, hδS, hδ : 0 < δ⟩ :=
    (((Filter.eventually_all_finset S).2 hloc).and self_mem_nhdsWithin).exists
  -- Bumps `φ x` with `φ x = 1` on `B̄(x, δ/2)`, support `B(x, δ)`, and signs `s x` of `c x`.
  let φ : (x : Eucl P) → ContDiffBump x := fun x => ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let s : Eucl P → ℝ := fun x => if 0 ≤ (c x : ℝ) then 1 else -1
  have hφ0 : ∀ x y, δ ≤ dist y x → φ x y = 0 := fun x y h => (φ x).zero_of_le_dist h
  have hφ1 : ∀ x, φ x x = 1 := fun x =>
    (φ x).one_of_mem_closedBall (mem_closedBall_self (half_pos hδ).le)
  -- The balls `B(x, δ)`, `x ∈ S`, are pairwise disjoint.
  have hsep : ∀ x ∈ S, ∀ x' ∈ S, x' ≠ x → ∀ y, dist y x < δ → δ ≤ dist y x' := by
    intro x hx x' hx' hne y hy
    by_contra h
    refine hne ((hδS x hx).2 x' (hS hx').1 ?_)
    have := dist_triangle x' y x
    rw [dist_comm x' y] at this
    linarith
  let h : Eucl P → ℝ := fun y => ∑ x ∈ S, s x * φ x y
  have hh0 : ∀ y, h y ≠ 0 → ∃ x ∈ S, dist y x < δ := by
    intro y hy
    by_contra hcon
    exact hy (Finset.sum_eq_zero fun x hx => by
      rw [hφ0 x y (not_lt.1 fun h' => hcon ⟨x, hx, h'⟩), mul_zero])
  have hhS : ∀ x ∈ S, h x = s x := by
    intro x hx
    rw [show h x = ∑ x' ∈ S, s x' * φ x' x from rfl,
      Finset.sum_eq_single_of_mem x hx fun x' hx' hne =>
        by rw [hφ0 x' x (hsep x hx x' hx' hne x (by simpa using hδ)), mul_zero],
      hφ1, mul_one]
  have hh1 : ∀ y, |h y| ≤ 1 := by
    intro y
    by_cases hy : h y = 0
    · simp [hy]
    obtain ⟨x, hx, hyx⟩ := hh0 y hy
    rw [show h y = ∑ x' ∈ S, s x' * φ x' y from rfl,
      Finset.sum_eq_single_of_mem x hx fun x' hx' hne =>
        by rw [hφ0 x' y (hsep x hx x' hx' hne y hyx), mul_zero], abs_mul]
    have hs : |s x| = 1 := by simp only [s]; split_ifs <;> simp
    rw [hs, one_mul, abs_of_nonneg (φ x).nonneg]
    exact (φ x).le_one
  -- The test form `ω = h • 𝟙`, where `𝟙` is the `0`-covector with value `1`.
  let e : Covector (Eucl P) 0 :=
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) (1 : ℝ)
  let f : DifferentialForm (Eucl P) 0 := fun y => h y • e
  have hfe : ∀ y, f y ![] = h y := fun y => by simp [f, e]
  set B : Set (Eucl P) := ⋃ x ∈ S, closedBall x δ
  have hB : IsCompact B := S.isCompact_biUnion fun x _ => isCompact_closedBall x δ
  have hBW : B ⊆ W := iUnion₂_subset fun x hx =>
    (closedBall_subset_closedBall (by linarith)).trans (hδS x hx).1
  have hfB : ∀ y, y ∉ B → f y = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨x, hx, hyx⟩ := hh0 y fun h0 => hne (by simp [f, h0])
    exact hy (mem_iUnion₂.2 ⟨x, hx, mem_closedBall.2 hyx.le⟩)
  have hfsupp : tsupport f ⊆ B :=
    closure_minimal (fun y hy => by_contra fun hyB => hy (hfB y hyB)) hB.isClosed
  have hfsmooth : IsSmoothForm f :=
    (ContDiff.sum fun x _ => contDiff_const.mul (φ x).contDiff).smul contDiff_const
  have hfcpt : HasCompactSupport f := HasCompactSupport.intro hB hfB
  let ω : TestFormOn U 0 := ⟨f, show IsTestForm f ∧ tsupport f ⊆ U from
    ⟨⟨hfsmooth, hfcpt⟩, hfsupp.trans (hBW.trans hWU)⟩⟩
  have hadm : ω ∈ massAdmissibleOn U 0 W := by
    refine show tsupport f ⊆ W ∧ ∀ y, covectorEuclideanNorm (f y) ≤ 1 from
      ⟨hfsupp.trans hBW, fun y => ?_⟩
    -- For a `0`-covector `α`, the coefficient norm is `|α(![])|`.
    rw [covectorEuclideanNorm, Fintype.sum_unique, ite_eq_left (Subsingleton.strictMono _),
      show (fun i => EuclideanSpace.basisFun (Fin P) ℝ ((default : Fin 0 → Fin P) i)) = ![] from
        Subsingleton.elim _ _, hfe, Real.sqrt_sq_eq_abs]
    exact hh1 y
  -- Only the points of `S` contribute to `Y(ω) = ∑ᶠ_{y ∈ N} c(y) h(y)`, and `h = s` on `S`.
  have hval : Y ω = ∑ x ∈ S, |(c x : ℝ)| := by
    rw [hY]
    change ∑ᶠ y ∈ N, (c y : ℝ) * f y ![] = _
    simp_rw [hfe]
    rw [finsum_mem_eq_sum_of_inter_support_eq (fun y => (c y : ℝ) * h y) (t := S) ?_]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [hhS x hx]
      simp only [s]
      split_ifs with h0
      · rw [mul_one, abs_of_nonneg h0]
      · rw [mul_neg_one, abs_of_neg (not_le.1 h0)]
    · ext y
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      constructor
      · rintro ⟨hyN, hy⟩
        refine ⟨?_, hy⟩
        obtain ⟨x, hx, hyx⟩ := hh0 y (right_ne_zero_of_mul hy)
        rw [(hδS x hx).2 y hyN (by linarith)]
        exact hx
      · rintro ⟨hyS, hy⟩
        exact ⟨(hS hyS).1, hy⟩
  calc ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) = ENNReal.ofReal (Y ω) := by rw [hval]
    _ ≤ Y.massOn W := Y.le_massOn hadm

/-- Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): a finite
integer combination of point masses `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`, `D ⊆ U`, is the integer
multiplicity current `τ(M, θ, ξ)` with `M = {x ∈ D : a(x) ≠ 0}`, `θ = |a|` and `ξ = ±1` the sign
of `a`.  `Y` is continuous since convergence of test forms gives pointwise convergence.  `M` is
finite, so it is `H⁰`-measurable and countably `0`-rectifiable and `H⁰`-integrals over it are
finite sums; at `x ∈ M`, for small `r` the blow-up `η_{x,r}(M)` meets the support of a given
`f ∈ C_c` only in `0`, so the weighted tangent space is `{0}`, spanned by the empty frame. -/
theorem Submission.br_zd_finite_dirac_im :
    ∀ (P : ℕ) (U : Set (Eucl P)) (D : Finset (Eucl P)) (a : Eucl P → ℤ),
      (↑D : Set (Eucl P)) ⊆ U → ∃ Y : GeometricCurrentOn U 0, IsIntegerMultiplicity Y ∧
        ∀ ω : TestFormOn U 0,
          Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  classical
  intro P U D a hDU
  -- `H⁰{x} = 1`, so `H⁰`-integrals over finite sets are finite sums.
  have hpt : ∀ x : Eucl P, (μHE[0] : Measure (Eucl P)) {x} = 1 := fun x => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      IntegrableOn g (F : Set (Eucl P)) (μHE[0] : Measure (Eucl P)) := by
    intro F g
    rw [← biUnion_of_singleton (F : Set (Eucl P)), Finset.set_biUnion_coe,
      integrableOn_finset_iUnion]
    exact fun x _ => integrableOn_singleton (hx := by rw [hpt]; exact ENNReal.one_lt_top)
  have hsum : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      ∫ x in (F : Set (Eucl P)), g x ∂(μHE[0] : Measure (Eucl P)) = ∑ x ∈ F, g x := by
    intro F g
    rw [setIntegral_finset F (hint F g)]
    simp only [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
  -- The current `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`: if `ω_j → 0`, then `ω_j(x) → 0` for every `x`
  -- (uniformly on the common compact support `K`, and `ω_j(x) = 0` off `K`).
  let L : TestFormOn U 0 →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]
      map_add' := fun ω η => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun t ω => by simp [Finset.mul_sum, mul_left_comm] }
  have hcont : ∀ ωs : ℕ → TestFormOn U 0, TestFormOnConverges ωs 0 →
      Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    rintro ωs ⟨K, -, -, hsupp, -, hconv⟩
    have hx : ∀ x, Tendsto (fun j => (ωs j : DifferentialForm (Eucl P) 0) x ![]) atTop (𝓝 0) := by
      intro x
      by_cases hxK : x ∈ K
      · have hev : Continuous fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Eucl P)
            (Covector (Eucl P) 0) => T ![] ![] := by fun_prop
        simpa [Function.comp_def] using (hev.tendsto _).comp ((hconv 0).tendsto_at hxK)
      · have h0 : ∀ j, (ωs j : DifferentialForm (Eucl P) 0) x = 0 := fun j =>
          image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp j h)
        simp [h0]
    simpa [L] using tendsto_finsetSum D fun x _ => (hx x).const_mul (a x : ℝ)
  obtain ⟨Y, hY⟩ : ∃ Y : GeometricCurrentOn U 0, ∀ ω : TestFormOn U 0,
      Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] :=
    ⟨⟨L, hcont⟩, fun ω => rfl⟩
  refine ⟨Y, ?_, hY⟩
  -- The triple: `M = {a ≠ 0}`, `θ = |a|`, `ξ = -ε` on `N = {a < 0}` and `ξ = ε` elsewhere, where
  -- `⟨α, ε⟩ = α(![])`; then `θ(x) ⟨α, ξ(x)⟩ = a(x) α(![])` on `M`.
  set M : Finset (Eucl P) := D.filter (fun x => a x ≠ 0) with hM
  set N : Finset (Eucl P) := D.filter (fun x => a x < 0) with hN
  let ε : NVector (Eucl P) 0 := simpleNVector ![]
  let θ : Eucl P → ℝ := fun x => |(a x : ℝ)|
  let ξ : Eucl P → NVector (Eucl P) 0 := fun x => if x ∈ N then -ε else ε
  have hMmeas : MeasurableSet (M : Set (Eucl P)) := M.finite_toSet.measurableSet
  have hterm : ∀ x ∈ M, ∀ α : Covector (Eucl P) 0, θ x * ξ x α = (a x : ℝ) * α ![] := by
    intro x hx α
    have hxD : x ∈ D := (Finset.mem_filter.1 hx).1
    by_cases hneg : a x < 0
    · have hxN : x ∈ N := Finset.mem_filter.2 ⟨hxD, hneg⟩
      have ha : (a x : ℝ) < 0 := by exact_mod_cast hneg
      simp only [θ, ξ, ε, hxN, ↓reduceIte, neg_apply, simpleNVector_apply,
        abs_of_neg ha]
      ring
    · have hxN : x ∉ N := fun h => hneg (Finset.mem_filter.1 h).2
      have ha : (0 : ℝ) ≤ a x := by exact_mod_cast not_lt.1 hneg
      simp only [θ, ξ, ε, hxN, ↓reduceIte, simpleNVector_apply, abs_of_nonneg ha]
  refine ⟨M, θ, ξ,
    { subset := fun x hx => hDU (Finset.mem_filter.1 hx).1
      nullMeasurableSet := hMmeas.nullMeasurableSet
      countablyRectifiable := ?_
      pos := fun x hx => abs_pos.2 (Int.cast_ne_zero.2 (Finset.mem_filter.1 hx).2)
      integrableOn := fun K _ _ => (hint M θ).mono_set inter_subset_left
      aestronglyMeasurable := ?_
      orients := ?_ }, fun x _ => ⟨(a x).natAbs, by simp [θ, Nat.cast_natAbs, Int.cast_abs]⟩, ?_⟩
  · -- `M` is countable, hence covered by the ranges of countably many constant maps.
    obtain ⟨g, hg⟩ := countable_iff_exists_subset_range.1 M.finite_toSet.countable
    refine ⟨∅, measure_empty, fun j _ => g j, fun j => ⟨0, LipschitzWith.const _⟩, fun y hy => ?_⟩
    obtain ⟨j, rfl⟩ := hg hy
    exact Or.inr (mem_iUnion.2 ⟨j, 0, rfl⟩)
  · -- `ξ` is constant off and on the finite set `N`.
    exact (StronglyMeasurable.ite N.finite_toSet.measurableSet stronglyMeasurable_const
      stronglyMeasurable_const).aestronglyMeasurable
  · -- Every `x ∈ M` is oriented by the empty frame, spanning the weighted tangent space `{0}`.
    refine ae_restrict_of_forall_mem hMmeas fun x hx =>
      ⟨![], ⟨fun i => i.elim0, fun i => i.elim0⟩, ?_, ?_⟩
    · rw [range_eq_empty, Submodule.span_empty]
      refine ⟨finrank_bot ℝ (Eucl P), fun f => ?_⟩
      have hbot : ∫ y in ((⊥ : Submodule ℝ (Eucl P)) : Set (Eucl P)), f y
          ∂(μHE[0] : Measure (Eucl P)) = f 0 := by
        simp
      rw [hbot]
      -- `f = 0` off `B_R(0)`, and the points of `M \ {x}` have distance `≥ d` from `x`; so for
      -- `0 < r < d / R` only `y = x` contributes to `∑_{y ∈ M} f(η_{x,r}(y)) θ(y)`.
      obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
      obtain ⟨d, hd, hdM⟩ := Metric.isOpen_iff.mp
        (M.erase x).finite_toSet.isClosed.isOpen_compl x (by simp)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (div_pos hd hR)] with r ⟨hr0, hrd⟩
      have hinj : Function.Injective (blowUpMap x r) := fun y z h => by
        simpa [blowUpMap, hr0.ne'] using h
      have hback : ∀ y, x + r • blowUpMap x r y = y := fun y => by
        simp [blowUpMap, smul_smul, hr0.ne']
      rw [← Finset.coe_image, hsum, Finset.sum_image fun y _ z _ h => hinj h]
      simp only [hback]
      rw [Finset.sum_eq_single x (fun y hy hyx => ?_) (fun h => absurd hx h)]
      · simp [blowUpMap, mul_comm]
      · have hyd : d ≤ ‖y - x‖ := by
          rw [← dist_eq_norm]
          by_contra h
          exact hdM (mem_ball.2 (not_le.1 h)) (Finset.mem_erase.2 ⟨hyx, hy⟩)
        rw [lt_div_iff₀ hR] at hrd
        rw [hfR, zero_mul]
        rw [blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0, le_inv_mul_iff₀ hr0]
        linarith
    · by_cases hxN : x ∈ N
      · exact Or.inr (by simp [ξ, ε, hxN])
      · exact Or.inl (by simp [ξ, ε, hxN])
  · -- `τ(M, θ, ξ)(ω) = ∑_{x ∈ M} a(x) ω(x) = ∑_{x ∈ D} a(x) ω(x)`, as `a = 0` on `D \ M`.
    intro ω
    rw [hY, tauAction, hsum, Finset.sum_congr rfl fun x hx => hterm x hx _, hM,
      Finset.sum_filter_of_ne]
    intro x _ hne ha
    exact hne (by simp [ha])

/-- The case `n = 0` of Simon Ch. 6, 8.2 (p. 176, "trivial in case `n = 0`"), on a set `W` with
`closure W` compact (used for 6.3): let `X_j ⇀ X` and, on test forms supported in `W`, let
`X_j(ω) = ∑ᶠ_{x ∈ N_j} c_j(x) ω(x)` with integers `c_j ≠ 0` on `N_j`, `N_j ∩ W` finite and
`∑_{x ∈ N_j ∩ W} |c_j(x)| ≤ Λ`.  Then on such forms `X(ω) = ∑_{x ∈ D} a(x) ω(x)` for a finite
`D ⊆ W` and integers `a`.  Each `N_j ∩ W` has at most `Q = ⌊Λ⌋₊` points, with `|c_j| ≤ ⌊Λ⌋`;
padding with `0`-weighted copies of `0` gives configurations of length `Q` in a compact set, a
subsequence converges, limit points outside `W` contribute `0` and equal ones are grouped. -/
theorem Submission.br_zd_dirac_local_limit : ∀ (P : ℕ) (U W : Set (Eucl P)) (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0) (N : ℕ → Set (Eucl P)) (c : ℕ → Eucl P → ℤ) (Λ : ℝ), IsCompact (closure W) → WeaklyConvergesOn Xj X → (∀ j, ∀ x ∈ N j, c j x ≠ 0) → (∀ j, (N j ∩ W).Finite) → (∀ j (S : Finset (Eucl P)), (↑S : Set (Eucl P)) ⊆ N j ∩ W → ∑ x ∈ S, |(c j x : ℝ)| ≤ Λ) → (∀ j (ω : TestFormOn U 0), tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W → Xj j ω = ∑ᶠ x ∈ N j, (c j x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) → ∃ (D : Finset (Eucl P)) (a : Eucl P → ℤ), (↑D : Set (Eucl P)) ⊆ W ∧ ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W → X ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  intro P U W Xj X N c Λ hW hconv hc hfin hbound hrepr
  classical
  -- `ω°(x) = ω(x)(![])` is continuous and vanishes off `tsupport ω`.
  have hcont : ∀ ω : TestFormOn U 0,
      Continuous fun x => (ω : DifferentialForm (Eucl P) 0) x ![] := fun ω =>
    ω.property.1.1.continuous.eval_const _
  have hvan : ∀ (ω : TestFormOn U 0) (x : Eucl P),
      x ∉ tsupport (ω : DifferentialForm (Eucl P) 0) →
        (ω : DifferentialForm (Eucl P) 0) x ![] = 0 := fun ω x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  -- Step 1: on forms supported in `W`, `X_j(ω) = ∑_{x ∈ A_j} c_j(x) ω°(x)`, `A_j = N_j ∩ W`.
  let A : ℕ → Finset (Eucl P) := fun j => (hfin j).toFinset
  have hA : ∀ j x, x ∈ A j ↔ x ∈ N j ∧ x ∈ W := fun j x => by simp [A]
  have hXj : ∀ j (ω : TestFormOn U 0), tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W →
      Xj j ω = ∑ x ∈ A j, (c j x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
    intro j ω hω
    rw [hrepr j ω hω]
    refine finsum_mem_eq_sum_of_subset _ ?_ fun x hx => ((hA j x).1 hx).1
    rintro x ⟨hxN, hx0⟩
    refine (hA j x).2 ⟨hxN, by_contra fun hxW => hx0 ?_⟩
    simp [hvan ω x fun h => hxW (hω h)]
  -- Step 2: `#A_j ≤ Q = ⌊Λ⌋₊` (as `|c_j| ≥ 1` on `N_j`) and `|c_j| ≤ m = ⌊Λ⌋` on `A_j`.
  have hΛ : 0 ≤ Λ := by simpa using hbound 0 ∅ (by simp)
  obtain ⟨Q, hcard⟩ : ∃ Q : ℕ, ∀ j, (A j).card ≤ Q := by
    refine ⟨⌊Λ⌋₊, fun j => Nat.le_floor ?_⟩
    calc ((A j).card : ℝ) = ∑ x ∈ A j, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ A j, |(c j x : ℝ)| := Finset.sum_le_sum fun x hx => by
          exact_mod_cast Int.one_le_abs (hc j x ((hA j x).1 hx).1)
      _ ≤ Λ := hbound j (A j) fun x hx => (hA j x).1 hx
  obtain ⟨m, hm, hcoef⟩ : ∃ m : ℤ, 0 ≤ m ∧ ∀ j, ∀ x ∈ A j, |c j x| ≤ m := by
    refine ⟨⌊Λ⌋, Int.floor_nonneg.2 hΛ, fun j x hx => Int.le_floor.2 ?_⟩
    simpa using hbound j {x} (by simpa using (hA j x).1 hx)
  -- Step 3: pad each configuration to length `Q` by points `0` with coefficient `0`.
  have pad : ∀ (n : ℕ) (B : Finset (Eucl P)), B.card ≤ n → ∀ d : Eucl P → ℤ,
      ∃ (p : Fin n → Eucl P) (b : Fin n → ℤ), (∀ ℓ, p ℓ ∈ B ∨ p ℓ = 0) ∧
        (∀ ℓ, b ℓ = 0 ∨ ∃ x ∈ B, b ℓ = d x) ∧
        ∀ g : Eucl P → ℝ, ∑ x ∈ B, (d x : ℝ) * g x = ∑ ℓ, (b ℓ : ℝ) * g (p ℓ) := by
    intro n
    induction n with
    | zero =>
      intro B hB d
      obtain rfl : B = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hB)
      exact ⟨Fin.elim0, Fin.elim0, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0, fun g => by simp⟩
    | succ n ih =>
      intro B hB d
      rcases B.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact ⟨fun _ => 0, fun _ => 0, fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun g => by simp⟩
      obtain ⟨p, b, hp, hb, hpb⟩ :=
        ih (B.erase x) (by rw [Finset.card_erase_of_mem hx]; omega) d
      refine ⟨Fin.cons x p, Fin.cons (d x) b, fun ℓ => ?_, fun ℓ => ?_, fun g => ?_⟩
      · refine Fin.cases (by simp [hx]) (fun i => ?_) ℓ
        simpa using (hp i).imp_left Finset.mem_of_mem_erase
      · refine Fin.cases (Or.inr ⟨x, hx, by simp⟩) (fun i => ?_) ℓ
        simpa using (hb i).imp_right fun ⟨z, hz, h⟩ => ⟨z, Finset.mem_of_mem_erase hz, h⟩
      · rw [← Finset.add_sum_erase B _ hx, hpb g, Fin.sum_univ_succ]
        simp
  choose p b hp hb hpb using fun j => pad Q (A j) (hcard j) (c j)
  -- Step 4: `(p_j, b_j) ∈ (closure W ∪ {0})^Q × [-m, m]^Q`, which is compact; extract a
  -- subsequence `ψ` with `(p_{ψ i}, b_{ψ i}) → (y, β)`.
  have hK : IsCompact ((Set.univ.pi fun _ : Fin Q => closure W ∪ {0}) ×ˢ
      (Set.univ.pi fun _ : Fin Q => Set.Icc (-m) m)) :=
    (isCompact_univ_pi fun _ => hW.union isCompact_singleton).prod
      (isCompact_univ_pi fun _ => (Set.finite_Icc _ _).isCompact)
  have hmem : ∀ j, (p j, b j) ∈ (Set.univ.pi fun _ : Fin Q => closure W ∪ {0}) ×ˢ
      (Set.univ.pi fun _ : Fin Q => Set.Icc (-m) m) := by
    refine fun j => ⟨fun ℓ _ => ?_, fun ℓ _ => ?_⟩
    · exact (hp j ℓ).imp (fun h => subset_closure ((hA j _).1 h).2) id
    · show b j ℓ ∈ Set.Icc (-m) m
      rcases hb j ℓ with h | ⟨x, hx, h⟩
      · rw [h]
        exact ⟨neg_nonpos.2 hm, hm⟩
      · rw [h]
        exact abs_le.1 (hcoef j x hx)
  obtain ⟨⟨y, β⟩, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq hmem
  -- Step 5: `X(ω) = ∑_ℓ β_ℓ ω°(y_ℓ)` by continuity of `(p, b) ↦ ∑_ℓ b_ℓ ω°(p_ℓ)`.
  have hX : ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W →
      X ω = ∑ ℓ, (β ℓ : ℝ) * (ω : DifferentialForm (Eucl P) 0) (y ℓ) ![] := by
    intro ω hω
    have hΦ : Continuous fun q : (Fin Q → Eucl P) × (Fin Q → ℤ) =>
        ∑ ℓ, (q.2 ℓ : ℝ) * (ω : DifferentialForm (Eucl P) 0) (q.1 ℓ) ![] :=
      continuous_finsetSum _ fun ℓ _ =>
        ((continuous_of_discreteTopology (f := fun z : ℤ => (z : ℝ))).comp
          ((continuous_apply ℓ).comp continuous_snd)).mul
          ((hcont ω).comp ((continuous_apply ℓ).comp continuous_fst))
    refine tendsto_nhds_unique ((hconv ω).comp hψ.tendsto_atTop) ?_
    refine ((hΦ.tendsto (y, β)).comp hlim).congr fun i => ?_
    simp only [Function.comp_apply]
    rw [hXj (ψ i) ω hω, hpb (ψ i)]
  -- Steps 6–7: limit points outside `W` contribute `0`; group the others by position.
  let s : Finset (Fin Q) := Finset.univ.filter fun ℓ => y ℓ ∈ W
  refine ⟨s.image y, fun z => ∑ ℓ ∈ s.filter fun ℓ => y ℓ = z, β ℓ, ?_, fun ω hω => ?_⟩
  · intro z hz
    rw [Finset.coe_image] at hz
    obtain ⟨ℓ, hℓ, rfl⟩ := hz
    simpa [s] using hℓ
  · rw [hX ω hω, ← Finset.sum_subset (Finset.subset_univ s) fun ℓ _ hℓ => ?_,
      ← Finset.sum_fiberwise_of_maps_to fun ℓ hℓ => Finset.mem_image_of_mem y hℓ]
    · refine Finset.sum_congr rfl fun z _ => ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ℓ hℓ => by rw [(Finset.mem_filter.1 hℓ).2]
    · have hyW : y ℓ ∉ W := by simpa [s] using hℓ
      rw [hvan ω (y ℓ) fun h => hyW (hω h), mul_zero]

/-- **Integrability of the integrands of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  For a
rectifiable triple `(M, θ, ξ)` in `U`: (a) `x ↦ θ(x) ⟨b, ξ(x)⟩` is `Hᵏ`-integrable on `M ∩ K` for
every compact `K ⊆ U` and `k`-covector `b`; (b) `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hᵏ`-integrable on `M`
for every continuous compactly supported `ω` with `spt ω ⊆ U`.  Since `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ`
orthonormal, `|⟨α, ξ⟩| ≤ ‖α‖` `Hᵏ⌞M`-a.e.; `θ` is integrable on `M ∩ K`, and the integrand of
(b) vanishes on `M \ spt ω`. -/
theorem Submission.ltg_tau_integrable : ∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ → (∀ (K : Set (Eucl P)) (b : Covector (Eucl P) k), IsCompact K → K ⊆ U → IntegrableOn (fun x => θ x * ξ x b) (M ∩ K) (μHE[k] : Measure (Eucl P))) ∧ ∀ ω : Eucl P → Covector (Eucl P) k, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U → IntegrableOn (fun x => θ x * ξ x (ω x)) M (μHE[k] : Measure (Eucl P)) := by
  intro P k U M θ ξ hT
  -- Step 1: for `Hᵏ⌞M`-a.e. `x`, `|ξ(x)(α)| ≤ ‖α‖` for every covector `α`
  -- (`|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`; the empty product for `k = 0`).
  have hunit : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) k, ‖ξ x α‖ ≤ ‖α‖ := by
    filter_upwards [hT.orients] with x hx α
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hs : ‖simpleNVector τ α‖ ≤ ‖α‖ :=
      calc ‖simpleNVector τ α‖ = ‖α τ‖ := rfl
        _ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h | h
    · rw [h]; exact hs
    · rw [h, neg_apply, norm_neg]; exact hs
  -- Step 2: `x ↦ ξ(x)(ω(x))` is a.e.-strongly measurable for `Hᵏ⌞M` whenever `ω` is
  -- (continuous evaluation `(w, α) ↦ w(α)` composed with `(ξ, ω)`).
  have hmeas : ∀ ω : Eucl P → Covector (Eucl P) k,
      AEStronglyMeasurable ω ((μHE[k] : Measure (Eucl P)).restrict M) →
      AEStronglyMeasurable (fun x => ξ x (ω x)) ((μHE[k] : Measure (Eucl P)).restrict M) := by
    intro ω hω
    have hev : Continuous fun p : NVector (Eucl P) k × Covector (Eucl P) k => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hev.comp_aestronglyMeasurable (hT.aestronglyMeasurable.prodMk hω)
  -- Steps 3–4: for compact `K ⊆ U` and `‖ω‖ ≤ C`, `θ` is integrable on `M ∩ K` and
  -- `ξ(·)(ω(·))` is measurable and a.e. bounded by `C` there, so the product is integrable.
  have hK : ∀ (K : Set (Eucl P)) (ω : Eucl P → Covector (Eucl P) k) (C : ℝ), IsCompact K →
      K ⊆ U → AEStronglyMeasurable ω ((μHE[k] : Measure (Eucl P)).restrict M) →
      (∀ x, ‖ω x‖ ≤ C) →
      IntegrableOn (fun x => θ x * ξ x (ω x)) (M ∩ K) (μHE[k] : Measure (Eucl P)) := by
    intro K ω C hKc hKU hω hC
    have hle : (μHE[k] : Measure (Eucl P)).restrict (M ∩ K) ≤
        (μHE[k] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono Set.inter_subset_left le_rfl
    have hθ : Integrable θ ((μHE[k] : Measure (Eucl P)).restrict (M ∩ K)) :=
      hT.integrableOn K hKc hKU
    refine hθ.mul_bdd (c := C) ((hmeas ω hω).mono_measure hle) ?_
    filter_upwards [ae_mono hle hunit] with x hx
    exact (hx (ω x)).trans (hC x)
  -- Part (a): the constant field `b`, bounded by `‖b‖`.
  refine ⟨fun K b hKc hKU => hK K (fun _ => b) ‖b‖ hKc hKU aestronglyMeasurable_const
    (fun _ => le_rfl), ?_⟩
  -- Part (b): integrable on `M ∩ spt ω` (Step 4) and zero on `M \ spt ω` (Step 5), with `M`
  -- null-measurable.
  intro ω hωc hωs hωU
  obtain ⟨C, hC⟩ := hωc.bounded_above_of_compact_support hωs
  refine (hK (tsupport ω) ω C hωs hωU hωc.aestronglyMeasurable hC).of_ae_sdiff_eq_zero
    hT.nullMeasurableSet (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∉ tsupport ω := fun h => hx.2 ⟨hx.1, h⟩
  rw [image_eq_zero_of_notMem_tsupport hx', map_zero, mul_zero]
/-- Finitely many covectors separate `k`-vectors (Simon Ch. 6, §1): `Λᵏ(ℝ^P)` is
finite-dimensional, and `k`-vectors (continuous linear functionals on it) agreeing on a basis
agree.  Evaluation on tuples of standard basis vectors embeds `Λᵏ(ℝ^P)` linearly into
`ℝ^(Fin k → Fin P)` (a multilinear map is determined by its values on basis vectors). -/
theorem Submission.ltg_covector_separating :
    ∀ (P k : ℕ), ∃ (L : ℕ) (b : Fin L → Covector (Eucl P) k),
      ∀ w w' : NVector (Eucl P) k, (∀ l, w (b l) = w' (b l)) → w = w' := by
  intro P k
  -- Evaluation on `k`-tuples of standard basis vectors of `ℝ^P`.
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  let ev : Covector (Eucl P) k →ₗ[ℝ] (Fin k → Fin P) → ℝ :=
    { toFun := fun α I => α fun j => e (I j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- `ev` is injective, so `Λᵏ(ℝ^P)` is finite-dimensional.
  have hinj : Function.Injective ev := fun α β h =>
    ContinuousAlternatingMap.toAlternatingMap_injective <|
      Module.Basis.ext_alternating e fun v _ => congrFun h v
  have : FiniteDimensional ℝ (Covector (Eucl P) k) := FiniteDimensional.of_injective ev hinj
  -- Linear functionals agreeing on a basis are equal.
  let b := Module.finBasis ℝ (Covector (Eucl P) k)
  exact ⟨Module.finrank ℝ (Covector (Eucl P) k), b, fun w w' h =>
    ContinuousLinearMap.coe_injective (b.ext h)⟩
/-- Nonnegative multiples of unit simple `k`-vectors are rigid (the orientations
`ξ = ±τ₁ ∧ ⋯ ∧ τₖ` of Simon Ch. 6, 3.1): if `τ, τ'` are orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₖ`,
`w' = ±τ'₁ ∧ ⋯ ∧ τ'ₖ`, `a, a' ≥ 0` and `a w = a' w'`, then `a = a'`, and `w = w'` when `a ≠ 0`.
Evaluate on the dual covectors `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩`, `α_σ(v) = det(⟨σᵢ, vⱼ⟩)` (1.1):
with `d = det(⟨τᵢ, τ'ⱼ⟩)`, `α_τ(τ) = α_τ'(τ') = 1` and `α_τ(τ') = α_τ'(τ) = d` give
`a = a' |d|` and `a |d| = a'`. -/
theorem Submission.ltg_simple_unit_rigidity :
    ∀ (P k : ℕ) (τ τ' : Fin k → Eucl P) (w w' : NVector (Eucl P) k) (a a' : ℝ),
      Orthonormal ℝ τ → Orthonormal ℝ τ' → (w = simpleNVector τ ∨ w = -simpleNVector τ) →
      (w' = simpleNVector τ' ∨ w' = -simpleNVector τ') → 0 ≤ a → 0 ≤ a' → a • w = a' • w' →
      a = a' ∧ (a ≠ 0 → w = w') := by
  intro P k τ τ' w w' a a' hτ hτ' hw hw' ha ha' h
  -- The dual covector `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩` evaluates as `det(⟨σᵢ, vⱼ⟩)`.
  let α : (Fin k → Eucl P) → Covector (Eucl P) k :=
    fun σ => wedgeCovectors k fun i => innerSL ℝ (σ i)
  have hα : ∀ σ v : Fin k → Eucl P,
      α σ v = (Matrix.of fun i j => inner ℝ (σ i) (v j)).det := fun σ v => by
    simp only [α, wedgeCovectors_apply_det, innerSL_apply_apply]
  -- `α_σ(σ) = det 1 = 1` for orthonormal `σ`, and `α_τ'(τ) = α_τ(τ')` by transposition.
  have hone : ∀ σ : Fin k → Eucl P, Orthonormal ℝ σ → α σ σ = 1 := fun σ hσ => by
    have h1 : (Matrix.of fun i j => inner ℝ (σ i) (σ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [orthonormal_iff_ite.mp hσ, Matrix.one_apply]
    rw [hα, h1, Matrix.det_one]
  have hswap : α τ' τ = α τ τ' := by
    rw [hα, hα, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact real_inner_comm _ _
  -- Signs: `w = s • simpleNVector τ` and `w' = s' • simpleNVector τ'` with `|s| = |s'| = 1`.
  have hsign : ∀ (σ : Fin k → Eucl P) (v : NVector (Eucl P) k),
      (v = simpleNVector σ ∨ v = -simpleNVector σ) →
        ∃ s : ℝ, |s| = 1 ∧ v = s • simpleNVector σ := by
    rintro σ v (rfl | rfl)
    · exact ⟨1, abs_one, (one_smul ℝ _).symm⟩
    · refine ⟨-1, by simp, ?_⟩
      ext β
      simp
  obtain ⟨s, hs, rfl⟩ := hsign τ w hw
  obtain ⟨s', hs', rfl⟩ := hsign τ' w' hw'
  -- Evaluate `a • w = a' • w'` at `α_τ` and `α_τ'` and take absolute values:
  -- `a = a' |d|` and `a |d| = a'`, where `d = α_τ(τ')`.
  have e1 := congrArg (fun v : NVector (Eucl P) k => |v (α τ)|) h
  have e2 := congrArg (fun v : NVector (Eucl P) k => |v (α τ')|) h
  simp only [smul_apply, simpleNVector_apply, smul_eq_mul, hone τ hτ, hone τ' hτ', hswap,
    abs_mul, abs_of_nonneg ha, abs_of_nonneg ha', hs, hs', mul_one, one_mul] at e1 e2
  -- `a = a'`: trivial if `a = 0`; otherwise `a |d|² = a` forces `|d| = 1`.
  have haa : a = a' := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [← e2, ha0, zero_mul]
    · have hd : |α τ τ'| * |α τ τ'| = 1 :=
        mul_left_cancel₀ ha0 (by rw [← mul_assoc, e2, ← e1, mul_one])
      have hd' : |α τ τ'| = 1 := by nlinarith [abs_nonneg (α τ τ')]
      rw [← e2, hd', mul_one]
  -- `w = w'`: cancel the nonzero scalar `a` in `a • w = a • w'`.
  refine ⟨haa, fun ha0 => ?_⟩
  rw [← haa] at h
  exact smul_right_injective _ ha0 h

/-- Uniqueness of `τ(M, θ, ξ)` on an open set (Simon Ch. 6, 3.1): if two rectifiable triples
define the same current on test forms supported in an open `O ⊆ U`, then
`Hᵏ((M₁ Δ M₂) ∩ O) = 0`, and `θ₁ = θ₂`, `ξ₁ = ξ₂` `Hᵏ`-a.e. on `M₁ ∩ O`.  For a covector `b`,
testing with `φ b` and the fundamental lemma give `1_{M₁} θ₁ ξ₁(b) = 1_{M₂} θ₂ ξ₂(b)` a.e. on
`O`; finitely many separating covectors upgrade this to `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂`, and
rigidity of nonnegative multiples of unit simple `k`-vectors concludes. -/
theorem Submission.ltg_tau_unique_on_open :
    ∀ (P k : ℕ) (U O : Set (Eucl P)), IsOpen O → O ⊆ U →
      ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M₁ θ₁ ξ₁ → IsRectifiableTriple U k M₂ θ₂ ξ₂ →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M₁ θ₁ ξ₁ ω = tauAction k M₂ θ₂ ξ₂ ω) →
      (μHE[k] : Measure (Eucl P)) (symmDiff M₁ M₂ ∩ O) = 0 ∧
        ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ O)), θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x := by
  intro P k U O hO hOU M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ hT₁ hT₂ hτ
  -- The scalar density `g^b = 1_M θ ξ(b)` of a triple is locally integrable on `O`, and
  -- `∫ φ g^b dHᵏ = τ(M, θ, ξ)(φ b)` for smooth `φ` with compact support in `O`.
  have key : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ → ∀ b : Covector (Eucl P) k,
      LocallyIntegrableOn (M.indicator fun y => θ y * ξ y b) O (μHE[k] : Measure (Eucl P)) ∧
      ∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ O →
        Integrable (fun x => φ x • M.indicator (fun y => θ y * ξ y b) x)
          (μHE[k] : Measure (Eucl P)) ∧
        ∫ x, φ x • M.indicator (fun y => θ y * ξ y b) x ∂(μHE[k] : Measure (Eucl P)) =
          tauAction k M θ ξ (fun x => φ x • b) := by
    intro M θ ξ hT b
    have hI := Submission.ltg_tau_integrable P k U M θ ξ hT
    refine ⟨?_, fun φ hφ hφc hφO => ?_⟩
    · rw [locallyIntegrableOn_iff hO.isLocallyClosed]
      intro K hKO hK
      exact (integrableOn_indicator_iff hT.nullMeasurableSet).2 (hI.1 K b hK (hKO.trans hOU))
    · have hint := hI.2 (fun x => φ x • b) (hφ.continuous.smul continuous_const)
        hφc.smul_right ((tsupport_smul_subset_left φ fun _ => b).trans (hφO.trans hOU))
      have heq : (fun x => φ x • M.indicator (fun y => θ y * ξ y b) x) =
          M.indicator fun x => θ x * ξ x (φ x • b) := by
        funext x
        by_cases hx : x ∈ M
        · simp only [Set.indicator_of_mem hx, map_smul, smul_eq_mul]
          ring
        · simp [Set.indicator_of_notMem hx]
      rw [heq]
      exact ⟨(integrable_indicator_iff₀ hT.nullMeasurableSet).2 hint,
        integral_indicator₀ hT.nullMeasurableSet⟩
  -- Fundamental lemma: for each covector `b`, `g₁^b = g₂^b` a.e. on `O`.
  have hG : ∀ b : Covector (Eucl P) k, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      M₁.indicator (fun y => θ₁ y * ξ₁ y b) x - M₂.indicator (fun y => θ₂ y * ξ₂ y b) x = 0 := by
    intro b
    obtain ⟨hl₁, hi₁⟩ := key M₁ θ₁ ξ₁ hT₁ b
    obtain ⟨hl₂, hi₂⟩ := key M₂ θ₂ ξ₂ hT₂ b
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hl₁.sub hl₂) fun φ hφ hφc hφO => ?_
    obtain ⟨hint₁, he₁⟩ := hi₁ φ hφ hφc hφO
    obtain ⟨hint₂, he₂⟩ := hi₂ φ hφ hφc hφO
    -- The test form `φ b ∈ 𝒟ᵏ(U)`, supported in `O`.
    have hsmooth : IsSmoothForm (fun x => φ x • b : DifferentialForm (Eucl P) k) := by
      unfold IsSmoothForm
      exact hφ.smul contDiff_const
    have hts : tsupport (fun x => φ x • b : DifferentialForm (Eucl P) k) ⊆ O :=
      (tsupport_smul_subset_left φ fun _ => b).trans hφO
    let ω : TestFormOn U k := ⟨fun x => φ x • b, ⟨hsmooth, hφc.smul_right⟩, hts.trans hOU⟩
    simp_rw [smul_sub]
    rw [integral_sub hint₁ hint₂, he₁, he₂]
    exact sub_eq_zero.2 (hτ ω hts)
  -- Finitely many covectors separate `k`-vectors: `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` a.e. on `O`.
  obtain ⟨L, bs, hsep⟩ := Submission.ltg_covector_separating P k
  have hind : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k)
      (x : Eucl P) (b : Covector (Eucl P) k),
      (M.indicator θ x • ξ x) b = M.indicator (fun y => θ y * ξ y b) x := by
    intro M θ ξ x b
    by_cases hx : x ∈ M <;> simp [hx]
  have hW : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      M₁.indicator θ₁ x • ξ₁ x = M₂.indicator θ₂ x • ξ₂ x := by
    have hall : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), ∀ l, x ∈ O →
        M₁.indicator (fun y => θ₁ y * ξ₁ y (bs l)) x -
          M₂.indicator (fun y => θ₂ y * ξ₂ y (bs l)) x = 0 :=
      ae_all_iff.2 fun l => hG (bs l)
    filter_upwards [hall] with x hx hxO
    refine hsep _ _ fun l => ?_
    rw [hind, hind]
    exact sub_eq_zero.1 (hx l hxO)
  -- `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` for an orthonormal frame `τ`, a.e. on `M`.
  have hor : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ M →
        ∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
          (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
    intro M θ ξ hT
    filter_upwards [(ae_restrict_iff'₀ hT.nullMeasurableSet).1 hT.orients] with x hx hxM
    obtain ⟨τ, hτo, -, hξ⟩ := hx hxM
    exact ⟨τ, hτo, hξ⟩
  -- Pointwise rigidity, using `θᵢ > 0` on `Mᵢ`: a.e. on `O`, `x ∈ M₁ ↔ x ∈ M₂`, and on `M₁`
  -- `θ₁ = θ₂`, `ξ₁ = ξ₂`.
  have hpt : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      (x ∈ M₁ ↔ x ∈ M₂) ∧ (x ∈ M₁ → θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x) := by
    filter_upwards [hW, hor M₁ θ₁ ξ₁ hT₁, hor M₂ θ₂ ξ₂ hT₂] with x hWx h1x h2x hxO
    have hW' := hWx hxO
    by_cases h1 : x ∈ M₁ <;> by_cases h2 : x ∈ M₂
    · obtain ⟨τ, hτo, hξτ⟩ := h1x h1
      obtain ⟨τ', hτo', hξτ'⟩ := h2x h2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2] at hW'
      obtain ⟨hθ, hξ⟩ := Submission.ltg_simple_unit_rigidity P k τ τ' (ξ₁ x) (ξ₂ x) (θ₁ x)
        (θ₂ x) hτo hτo' hξτ hξτ' (hT₁.pos x h1).le (hT₂.pos x h2).le hW'
      exact ⟨iff_of_true h1 h2, fun _ => ⟨hθ, hξ (hT₁.pos x h1).ne'⟩⟩
    · -- On `M₁ \ M₂`, `θ₁ ξ₁ = 0 = 0 ξ₁` would force `θ₁ = 0`.
      obtain ⟨τ, hτo, hξτ⟩ := h1x h1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, zero_smul] at hW'
      exact absurd (Submission.ltg_simple_unit_rigidity P k τ τ (ξ₁ x) (ξ₁ x) (θ₁ x) 0 hτo hτo
        hξτ hξτ (hT₁.pos x h1).le le_rfl (by rw [hW', zero_smul])).1 (hT₁.pos x h1).ne'
    · obtain ⟨τ, hτo, hξτ⟩ := h2x h2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_smul] at hW'
      exact absurd (Submission.ltg_simple_unit_rigidity P k τ τ (ξ₂ x) (ξ₂ x) (θ₂ x) 0 hτo hτo
        hξτ hξτ (hT₂.pos x h2).le le_rfl (by rw [← hW', zero_smul])).1 (hT₂.pos x h2).ne'
    · exact ⟨iff_of_false h1 h2, fun h => absurd h h1⟩
  refine ⟨?_, ?_⟩
  · -- `(M₁ Δ M₂) ∩ O` lies in the exceptional null set.
    rw [ae_iff] at hpt
    refine measure_mono_null ?_ hpt
    rintro x ⟨hxs, hxO⟩ hcon
    rcases Set.mem_symmDiff.1 hxs with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact h2 ((hcon hxO).1.1 h1)
    · exact h1 ((hcon hxO).1.2 h2)
  · rw [ae_restrict_iff'₀ (hT₁.nullMeasurableSet.inter hO.measurableSet.nullMeasurableSet)]
    filter_upwards [hpt] with x hx hxMO
    exact (hx hxMO.2).2 hxMO.1
/-- Gluing compatible integer multiplicity triples along a countable open cover (Simon Ch. 6,
6.3): if `U ⊆ ⋃ᵢ Vᵢ` with `Vᵢ` open, `(Mᵢ, θᵢ, ξᵢ)` are triples in `U` with `θᵢ ∈ ℕ` on `Mᵢ`, and any
two agree `Hᵏ`-a.e. on `Vᵢ ∩ Vⱼ`, then one triple `(M₀, θ₀, ξ₀)` with `θ₀ ∈ ℕ` on `M₀` agrees with
each `(Mᵢ, θᵢ, ξᵢ)` `Hᵏ`-a.e. on `Vᵢ`.  The hypothesis (TL) is locality of weighted approximate
tangent spaces.  `M₀ = ⋃ᵢ Mᵢ ∩ Dᵢ` with `Dᵢ = Vᵢ \ ⋃_{j<i} Vⱼ`, and on `Dᵢ` the triple is
`(Mᵢ, θᵢ, ξᵢ)`. -/
theorem Submission.ltg_glue_triples :
    ∀ (P k : ℕ) (U : Set (Eucl P)), (∀ (A A' : Set (Eucl P)) (ϑ ϑ' : Eucl P → ℝ) (x : Eucl P) (W : Set (Eucl P)), IsOpen W → x ∈ W → (μHE[k] : Measure (Eucl P)) (symmDiff A A' ∩ W) = 0 → (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (A ∩ W)), ϑ y = ϑ' y) → ϑ x = ϑ' x → ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k A ϑ x L → HasWeightedApproximateTangentSpaceAt k A' ϑ' x L) → ∀ (V M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) k), (∀ i, IsOpen (V i)) → U ⊆ ⋃ i, V i → (∀ i, IsRectifiableTriple U k (M i) (θ i) (ξ i)) → (∀ i, ∀ x ∈ M i, ∃ n : ℕ, θ i x = n) → (∀ i j, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) (M j) ∩ (V i ∩ V j)) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ (V i ∩ V j))), θ i x = θ j x ∧ ξ i x = ξ j x) → ∃ (M₀ : Set (Eucl P)) (θ₀ : Eucl P → ℝ) (ξ₀ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ n : ℕ, θ₀ x = n) ∧ ∀ i, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) M₀ ∩ V i) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ V i)), θ i x = θ₀ x ∧ ξ i x = ξ₀ x := by
  classical
  intro P k U TL V M θ ξ hV hUV hM hint hcompat
  -- Step 1: disjointification `D i = V i \ ⋃_{j<i} V j`.
  set D : ℕ → Set (Eucl P) := fun i => V i ∩ ⋂ j, ⋂ (_ : j < i), (V j)ᶜ with hD_def
  have hD_mem : ∀ x i, x ∈ D i ↔ x ∈ V i ∧ ∀ j < i, x ∉ V j := by
    intro x i
    simp only [hD_def, mem_inter_iff, mem_iInter, mem_compl_iff]
  have hD_meas : ∀ i, MeasurableSet (D i) := fun i =>
    (hV i).measurableSet.inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hV j).measurableSet.compl)
  have hDV : ∀ i, D i ⊆ V i := fun i x hx => ((hD_mem x i).1 hx).1
  -- Step 2: the least index `ι x` of a set `V j` containing `x`.
  let ι : Eucl P → ℕ := fun x => if h : ∃ j, x ∈ V j then Nat.find h else 0
  have hι_V : ∀ x i, x ∈ V i → x ∈ D (ι x) ∧ ι x ≤ i := by
    intro x i hx
    have h : ∃ j, x ∈ V j := ⟨i, hx⟩
    have hιx : ι x = Nat.find h := dite_eq_left h
    rw [hιx]
    exact ⟨(hD_mem x _).2 ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩, Nat.find_min' h hx⟩
  have hι_D : ∀ x i, x ∈ D i → ι x = i := by
    intro x i hx
    obtain ⟨hxV, hlt⟩ := (hD_mem x i).1 hx
    obtain ⟨hxD, hle⟩ := hι_V x i hxV
    rcases lt_or_eq_of_le hle with h | h
    · exact absurd ((hD_mem x _).1 hxD).1 (hlt _ h)
    · exact h
  -- Step 3: the glued triple.
  set M₀ : Set (Eucl P) := ⋃ i, M i ∩ D i with hM₀_def
  set θ₀ : Eucl P → ℝ := fun x => θ (ι x) x with hθ₀_def
  set ξ₀ : Eucl P → NVector (Eucl P) k := fun x => ξ (ι x) x with hξ₀_def
  have hθ₀_D : ∀ x i, x ∈ D i → θ₀ x = θ i x := by
    intro x i hx
    simp only [hθ₀_def, hι_D x i hx]
  have hξ₀_D : ∀ x i, x ∈ D i → ξ₀ x = ξ i x := by
    intro x i hx
    simp only [hξ₀_def, hι_D x i hx]
  have hM₀_D : ∀ x i, x ∈ D i → (x ∈ M₀ ↔ x ∈ M i) := by
    intro x i hx
    constructor
    · intro h
      obtain ⟨j, hjM, hjD⟩ := mem_iUnion.1 h
      rw [← hι_D x i hx, hι_D x j hjD]
      exact hjM
    · intro h
      exact mem_iUnion.2 ⟨i, h, hx⟩
  have hM₀_mem : ∀ x ∈ M₀, ∃ i, x ∈ M i ∧ x ∈ D i := by
    intro x hx
    obtain ⟨i, hiM, hiD⟩ := mem_iUnion.1 hx
    exact ⟨i, hiM, hiD⟩
  -- Step 4: agreement of the carriers on each `V i`.
  have hagree_set : ∀ i, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) M₀ ∩ V i) = 0 := by
    intro i
    refine measure_mono_null ?_ (measure_iUnion_null fun j => (hcompat i j).1)
    rintro x ⟨hxs, hxV⟩
    obtain ⟨hxD, -⟩ := hι_V x i hxV
    have hiff := hM₀_D x (ι x) hxD
    refine mem_iUnion.2 ⟨ι x, ?_, hxV, hDV _ hxD⟩
    rw [mem_symmDiff] at hxs ⊢
    rcases hxs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun h => h2 (hiff.2 h)⟩
    · exact Or.inr ⟨hiff.1 h1, h2⟩
  -- Step 5: agreement of weights and orientations on each `M i ∩ V i`.
  have hnm : ∀ i, NullMeasurableSet (M i) (μHE[k] : Measure (Eucl P)) :=
    fun i => (hM i).nullMeasurableSet
  have hagree_fun : ∀ i, ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ V i)),
      θ i x = θ₀ x ∧ ξ i x = ξ₀ x := by
    intro i
    have hall : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), ∀ j, x ∈ M i ∩ (V i ∩ V j) →
        θ i x = θ j x ∧ ξ i x = ξ j x := by
      rw [ae_all_iff]
      intro j
      exact (ae_restrict_iff'₀ ((hnm i).inter
        ((hV i).measurableSet.inter (hV j).measurableSet).nullMeasurableSet)).1 (hcompat i j).2
    rw [ae_restrict_iff'₀ ((hnm i).inter (hV i).measurableSet.nullMeasurableSet)]
    filter_upwards [hall] with x hx hxMV
    obtain ⟨hxD, -⟩ := hι_V x i hxMV.2
    obtain ⟨h1, h2⟩ := hx (ι x) ⟨hxMV.1, hxMV.2, hDV _ hxD⟩
    exact ⟨h1.trans (hθ₀_D x _ hxD).symm, h2.trans (hξ₀_D x _ hxD).symm⟩
  -- Steps 6–10: the triple conditions.
  have hpiece_nm : ∀ i, NullMeasurableSet (M i ∩ D i) (μHE[k] : Measure (Eucl P)) :=
    fun i => (hnm i).inter (hD_meas i).nullMeasurableSet
  -- Not found by instance search; the topologies agree definitionally.
  have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) k) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (NVector (Eucl P) k) _
  refine ⟨M₀, θ₀, ξ₀, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun i => ⟨hagree_set i, hagree_fun i⟩⟩
  · -- subset
    intro x hx
    obtain ⟨i, hiM, -⟩ := hM₀_mem x hx
    exact (hM i).subset hiM
  · -- nullMeasurableSet
    exact NullMeasurableSet.iUnion hpiece_nm
  · -- countablyRectifiable
    exact (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion M
      (fun i => (hM i).countablyRectifiable)).mono (iUnion_mono fun i => inter_subset_left)
  · -- pos
    intro x hx
    obtain ⟨i, hiM, hiD⟩ := hM₀_mem x hx
    rw [hθ₀_D x i hiD]
    exact (hM i).pos x hiM
  · -- integrableOn: a compact `K ⊆ U` meets only `D 0, …, D N`
    intro K hK hKU
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (hKU.trans hUV)
    set N : ℕ := t.sup id with hN
    have hsub : M₀ ∩ K ⊆ ⋃ j ∈ Finset.range (N + 1), M j ∩ K ∩ D j := by
      rintro x ⟨hxM, hxK⟩
      obtain ⟨i, hiM, hiD⟩ := hM₀_mem x hxM
      obtain ⟨l, hlt, hxl⟩ := mem_iUnion₂.1 (ht hxK)
      have hil : i ≤ l := by
        rw [← hι_D x i hiD]
        exact (hι_V x l hxl).2
      have hlN : l ≤ N := Finset.le_sup (f := id) hlt
      exact mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le (hil.trans hlN)),
        ⟨hiM, hxK⟩, hiD⟩
    refine IntegrableOn.mono_set ?_ hsub
    refine integrableOn_finset_iUnion.2 fun j _ => ?_
    have hj : IntegrableOn (θ j) (M j ∩ K ∩ D j) (μHE[k] : Measure (Eucl P)) :=
      ((hM j).integrableOn K hK hKU).mono_set inter_subset_left
    refine hj.congr_fun_ae ?_
    filter_upwards [ae_restrict_mem₀ (((hnm j).inter hK.measurableSet.nullMeasurableSet).inter
      (hD_meas j).nullMeasurableSet)] with x hx
    exact (hθ₀_D x j hx.2).symm
  · -- aestronglyMeasurable
    rw [hM₀_def, aestronglyMeasurable_iUnion_iff]
    intro i
    refine ((hM i).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)).congr ?_
    filter_upwards [ae_restrict_mem₀ (hpiece_nm i)] with x hx
    exact (hξ₀_D x i hx.2).symm
  · -- orients: transfer the tangent space from `(M i, θ i)` by (TL) with `W = V i`
    rw [hM₀_def, ae_restrict_iUnion_iff]
    intro i
    filter_upwards [ae_restrict_mem₀ (hpiece_nm i),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hM i).orients]
      with x hx ⟨τ, hτ, htan, hsign⟩
    refine ⟨τ, hτ, ?_, ?_⟩
    · exact TL (M i) M₀ (θ i) θ₀ x (V i) (hV i) (hDV i hx.2) (hagree_set i)
        ((hagree_fun i).mono fun y hy => hy.1) (hθ₀_D x i hx.2).symm _ htan
    · rw [hξ₀_D x i hx.2]
      exact hsign
  · -- integrality
    intro x hx
    obtain ⟨i, hiM, hiD⟩ := hM₀_mem x hx
    rw [hθ₀_D x i hiD]
    exact hint i x hiM
/-- Locality of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1 (‡)), the locality step in the proof of 6.3: on
forms `ω` with `tsupport ω ⊆ V`, `V` open, `τ(M, θ, ξ)(ω)` only depends on `M ∩ V` up to
`Hᵏ`-null sets and on `θ, ξ` up to `Hᵏ ⌞ (M ∩ V)`-null sets.  Both integrands vanish off `V`,
so `∫_M = ∫_{M ∩ V}` and `∫_{M'} = ∫_{M' ∩ V}`; these agree since `M ∩ V`, `M' ∩ V` are
`Hᵏ`-a.e. equal and the integrands agree a.e. on `M ∩ V`.  No integrability is needed. -/
theorem Submission.ltg_tau_congr_on_open :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (ξ ξ' : Eucl P → NVector (Eucl P) k)
      (V : Set (Eucl P)), IsOpen V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ x = θ' x ∧ ξ x = ξ' x) →
      ∀ ω : DifferentialForm (Eucl P) k, tsupport ω ⊆ V →
        tauAction k M θ ξ ω = tauAction k M' θ' ξ' ω := by
  intro P k M M' θ θ' ξ ξ' V hV hMM' hθξ ω hω
  -- Both integrands vanish off `V`, since `ω = 0` off `tsupport ω ⊆ V`.
  have hvan : ∀ (η : Eucl P → ℝ) (ζ : Eucl P → NVector (Eucl P) k) (x : Eucl P), x ∉ V →
      η x * ζ x (ω x) = 0 := by
    intro η ζ x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), map_zero, mul_zero]
  -- Hence `∫_A = ∫_{A ∩ V}` for both integrands.
  have hcut : ∀ (A : Set (Eucl P)) (η : Eucl P → ℝ) (ζ : Eucl P → NVector (Eucl P) k),
      ∫ x in A, η x * ζ x (ω x) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ x in A ∩ V, η x * ζ x (ω x) ∂(μHE[k] : Measure (Eucl P)) := by
    intro A η ζ
    rw [inter_comm, ← Measure.restrict_restrict hV.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan η ζ)]
  -- `M ∩ V` and `M' ∩ V` differ by subsets of the null set `(M ∆ M') ∩ V`.
  have hset : M ∩ V =ᵐ[(μHE[k] : Measure (Eucl P))] M' ∩ V := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ hMM'
      rintro x ⟨⟨hxM, hxV⟩, hx⟩
      exact ⟨Or.inl ⟨hxM, fun hxM' => hx ⟨hxM', hxV⟩⟩, hxV⟩
    · refine measure_mono_null ?_ hMM'
      rintro x ⟨⟨hxM', hxV⟩, hx⟩
      exact ⟨Or.inr ⟨hxM', fun hxM => hx ⟨hxM, hxV⟩⟩, hxV⟩
  -- The integrands agree `Hᵏ ⌞ (M ∩ V)`-a.e.
  have hae : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)),
      θ x * ξ x (ω x) = θ' x * ξ' x (ω x) := by
    filter_upwards [hθξ] with x hx
    rw [hx.1, hx.2]
  calc tauAction k M θ ξ ω
      = ∫ x in M ∩ V, θ x * ξ x (ω x) ∂(μHE[k] : Measure (Eucl P)) := hcut M θ ξ
    _ = ∫ x in M ∩ V, θ' x * ξ' x (ω x) ∂(μHE[k] : Measure (Eucl P)) := integral_congr_ae hae
    _ = ∫ x in M' ∩ V, θ' x * ξ' x (ω x) ∂(μHE[k] : Measure (Eucl P)) :=
        setIntegral_congr_set hset
    _ = tauAction k M' θ' ξ' ω := (hcut M' θ' ξ').symm

/-- **Local-to-global for `τ(M, θ, ξ)` via a smooth partition of unity** (Simon Ch. 6, 3.1 (‡);
used in the local-to-global step of the proof of 6.3).  If every `x ∈ U` has an open
`V_x ∋ x` such that `X ∈ 𝒟ₖ(U)` agrees with `τ(M, θ, ξ)` on the test forms supported in `V_x`,
then `X = τ(M, θ, ξ)` on `𝒟ᵏ(U)`.
Cover the compact `K = spt ω ⊆ U` by finitely many `V_y` (`y ∈ K`), take a smooth partition of
unity `χ_y` on `K` subordinate to them and split `ω = ∑_y χ_y ω`: each `χ_y ω ∈ 𝒟ᵏ(U)` has support
in `V_y`, so `X(χ_y ω) = τ(χ_y ω)`; conclude by linearity of `X` and of the integral, each
`θ ⟨χ_y ω, ξ⟩` being `Hᵏ`-integrable on `M` by `Submission.ltg_tau_integrable`. -/
theorem Submission.ltg_tau_local_to_global :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U k) (M : Set (Eucl P))
      (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ →
      (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ ∀ ω : TestFormOn U k,
        tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = tauAction k M θ ξ ω) →
      ∀ ω : TestFormOn U k, X ω = tauAction k M θ ξ ω := by
  intro P k U X M θ ξ hT hloc ω
  classical
  -- 1. `f := ω` is smooth with compact support `K := tsupport f ⊆ U`.
  obtain ⟨f, hf⟩ := ω
  have ⟨⟨hfs, hfc⟩, hfU⟩ : IsTestForm f ∧ tsupport f ⊆ U := hf
  -- 2. Finitely many of the neighbourhoods `V y` (`y ∈ K`) cover `K`.
  choose! V hVo hyV hXV using hloc
  obtain ⟨t, htK⟩ := hfc.isCompact.elim_finite_subcover (fun y : tsupport f => V y)
    (fun y => hVo y (hfU y.2)) (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyV y (hfU hy)⟩)
  -- 3. A smooth partition of unity `χ` on `K` subordinate to `(V y)_{y ∈ t}`.
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Eucl P)) (isClosed_tsupport f)
    (fun i : t => V (i : tsupport f)) (fun i => hVo _ (hfU (i : tsupport f).2)) fun y hy => by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (htK hy)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hyi⟩
  -- 4. The pieces `g i := χ i • f` are test forms in `U`, supported in `V i`.
  let g : t → DifferentialForm (Eucl P) k := fun i x => χ i x • f x
  have hg : ∀ i, IsTestForm (g i) ∧ tsupport (g i) ⊆ U := fun i =>
    ⟨⟨(contMDiff_iff_contDiff.mp (χ i).contMDiff).smul hfs,
      hfc.mono (Function.support_smul_subset_right (fun x => χ i x) f)⟩,
      (tsupport_smul_subset_right _ _).trans hfU⟩
  have hgV : ∀ i, tsupport (g i) ⊆ V (i : tsupport f) := fun i =>
    (tsupport_smul_subset_left _ _).trans (hχ i)
  -- 5. `f = ∑ i, g i`: on `K` because `∑ i, χ i = 1` there, off `K` because `f = 0` there.
  have hsum : ∀ x, ∑ i : t, g i x = f x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have h1 : ∑ i : t, χ i x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact χ.sum_eq_one hx
      simp only [g]
      rw [← Finset.sum_smul, h1, one_smul]
    · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [g, h0]
  have hω : (⟨f, hf⟩ : TestFormOn U k) = ∑ i : t, (⟨g i, hg i⟩ : TestFormOn U k) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    rw [Finset.sum_apply]
    exact (hsum x).symm
  -- 6. Linearity of `X`, and local agreement `X (g i) = τ (g i)` on each piece.
  have hX : X ⟨f, hf⟩ = ∑ i : t, tauAction k M θ ξ (g i) := by
    rw [hω]
    refine (map_sum X.toCurrent _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact hXV (i : tsupport f) (hfU (i : tsupport f).2) ⟨g i, hg i⟩ (hgV i)
  -- 7. Linearity of the integral (each piece is integrable by `tau_integrable`) and of `ξ x`.
  have hint : ∀ i ∈ (Finset.univ : Finset t),
      Integrable (fun x => θ x * ξ x (g i x)) ((μHE[k] : Measure (Eucl P)).restrict M) :=
    fun i _ => (Submission.ltg_tau_integrable P k U M θ ξ hT).2 (g i) (hg i).1.1.continuous
      (hg i).1.2 (hg i).2
  rw [hX]
  unfold tauAction
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Finset.mul_sum, ← map_sum (ξ x) (fun i => g i x) Finset.univ, hsum x]
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the
proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to
`Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets, `V ∋ x` open.  If `B_δ(x) ⊆ V` and
`f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off
`W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and
`(M', θ')` agree for all small `r`. -/
theorem Submission.br_weightedTangent_congr :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P) (V : Set (Eucl P)),
      IsOpen V → x ∈ V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ y = θ' y) → θ x = θ' x →
      ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k M' θ' x L := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k M M' θ θ' x V hV hxV hMM' hθθ' hθx L hL
  -- `η_r(y) = r⁻¹ (y - x)` maps `Hᵏ`-null sets to `Hᵏ`-null sets: `Hᵏ(η_r Z) = r⁻ᵏ Hᵏ(Z)`.
  have hnull : ∀ r : ℝ, r ≠ 0 → ∀ Z : Set (Eucl P), (μHE[k] : Measure (Eucl P)) Z = 0 →
      (μHE[k] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- A measurable `N ⊇ {θ ≠ θ'}` with `Hᵏ(N ∩ M ∩ V) = 0`.
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hθθ')
  rw [Measure.restrict_apply hNmeas] at hN0
  refine ⟨hL.1, fun f => ?_⟩
  rw [← hθx]
  refine (hL.2 f).congr' ?_
  -- `f = 0` off `B_R(0)` and `B_δ(x) ⊆ V`; the blow-up integrals agree for `0 < r < δ / R`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hcont : Continuous fun y : Eucl P => x + r • y :=
    continuous_const.add (continuous_const_smul r)
  -- `W = η_r(V)` is open and the integrands `f(y) g(x + r y)` vanish off `W`.
  set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' V with hW
  have hWmeas : MeasurableSet W := (hV.preimage hcont).measurableSet
  have hvan : ∀ g : Eucl P → ℝ, ∀ y, y ∉ W → f y * g (x + r • y) = 0 := by
    intro g y hy
    have hfy : f y = 0 := by
      apply hfR
      have h1 : x + r • y ∉ ball x δ := fun h => hy (hδV h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, not_lt] at h1
      rw [lt_div_iff₀ hR] at hrR
      exact le_of_lt (lt_of_mul_lt_mul_left (hrR.trans_le h1) hr0.le)
    rw [hfy, zero_mul]
  -- Cutting by `W`: `∫_{η_r(S)} = ∫_{W ∩ η_r(S)}`.
  have hcut : ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ y in W ∩ blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
    intro S g
    rw [← Measure.restrict_restrict hWmeas,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan g)]
  -- `W ∩ η_r(M) = W ∩ η_r(M')` up to the null set `η_r((M ∆ M') ∩ V)`.
  have hset : W ∩ blowUpMap x r '' M =ᵐ[(μHE[k] : Measure (Eucl P))] W ∩ blowUpMap x r '' M' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inl ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inr ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
  -- `θ(x + r y) = θ'(x + r y)` a.e. on `W ∩ η_r(M)`, off the null set `η_r(N ∩ M ∩ V)`.
  have hae : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (W ∩ blowUpMap x r '' M)),
      f y * θ (x + r • y) = f y * θ' (x + r • y) := by
    have hN'meas : MeasurableSet ((fun y => x + r • y) ⁻¹' N) :=
      hNmeas.preimage hcont.measurable
    rw [ae_iff]
    refine measure_mono_null (t := (fun y => x + r • y) ⁻¹' N) ?_ ?_
    · intro y hy
      by_contra hyN
      apply hy
      have hθy : θ (x + r • y) = θ' (x + r • y) := by
        by_contra hne
        exact hyN (hNsub hne)
      rw [hθy]
    · rw [Measure.restrict_apply hN'meas]
      refine measure_mono_null ?_ (hnull r hr0.ne' _ hN0)
      rintro y ⟨hyN, hyW, z, hzM, rfl⟩
      refine ⟨z, ⟨?_, hzM, ?_⟩, rfl⟩
      · simpa [hinv r hr0.ne' z] using hyN
      · simpa [hW, hinv r hr0.ne' z] using hyW
  calc ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P))
      = ∫ y in W ∩ blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        hcut M θ
    _ = ∫ y in W ∩ blowUpMap x r '' M, f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        integral_congr_ae hae
    _ = ∫ y in W ∩ blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
        rw [Measure.restrict_congr_set hset]
    _ = ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        (hcut M' θ').symm

/-- Integer multiplicity is local (the patching step in the proof of Simon Ch. 6, 6.3): if every
`x ∈ U` has an open `V ∋ x` on which `X` agrees with an integer multiplicity current, then `X` is
integer multiplicity.  By Lindelöf countably many such `V_i`, with `Y_i = τ(M_i, θ_i, ξ_i)`, cover
`U`.  Two of these triples agree up to null sets on `V_i ∩ V_j`, where both represent `X`, so they
glue to one integer multiplicity triple `(M₀, θ₀, ξ₀)` that agrees with each on its `V_i`; then
`X = τ(M₀, θ₀, ξ₀)` on forms supported in some `V_i`, hence on all forms. -/
theorem Submission.br_isIntegerMultiplicity_of_local :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y ∧
          ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = Y ω) →
      IsIntegerMultiplicity X := by
  intro P k U _ X hloc
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · -- `U = ∅`: `X = τ(∅, 0, 0)`, since the local hypothesis is vacuous.
    have hT : IsRectifiableTriple (∅ : Set (Eucl P)) k ∅ 0 0 :=
      { subset := subset_rfl
        nullMeasurableSet := nullMeasurableSet_empty
        countablyRectifiable :=
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
        pos := fun x hx => absurd hx (notMem_empty x)
        integrableOn := fun K _ _ => by simp
        aestronglyMeasurable := by simp
        orients := by simp }
    exact ⟨∅, 0, 0, hT, fun x hx => absurd hx (notMem_empty x),
      Submission.ltg_tau_local_to_global P k ∅ X ∅ 0 0 hT fun x hx => absurd hx (notMem_empty x)⟩
  -- For each `x ∈ U` choose `V_x` and `Y_x`.
  choose! Vx hVo hxV hVU Y hY hXY using hloc
  -- Lindelöf: a countable subfamily `V_{f i}` (`i ∈ ℕ`) covers `U`.
  obtain ⟨T, hTU, hTc, hTV⟩ := TopologicalSpace.isOpen_biUnion_countable U Vx hVo
  have hcovT : U ⊆ ⋃ x ∈ T, Vx x := by
    rw [hTV]
    exact fun x hx => mem_biUnion hx (hxV x hx)
  obtain ⟨f, rfl⟩ : ∃ f : ℕ → Eucl P, T = range f := by
    refine hTc.exists_eq_range ?_
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (hcovT hx)
    exact ⟨y, hy⟩
  have hfU : ∀ i, f i ∈ U := fun i => hTU (mem_range_self i)
  have hcover : U ⊆ ⋃ i, Vx (f i) := by
    intro x hx
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.mp (hcovT hx)
    exact mem_iUnion.mpr ⟨i, hxy⟩
  -- `Y_{f i} = τ(M_i, θ_i, ξ_i)` with integer multiplicity triples.
  have hY' : ∀ i, ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ ∧ (∀ x ∈ M, ∃ n : ℕ, θ x = n) ∧
        ∀ ω : TestFormOn U k, Y (f i) ω = tauAction k M θ ξ ω :=
    fun i => hY (f i) (hfU i)
  choose M θ ξ hT hθ hrep using hY'
  -- On `V_{f i} ∩ V_{f j}` both triples represent `X`, so they agree there up to null sets.
  have hcompat : ∀ i j, (μHE[k] : Measure (Eucl P))
        (symmDiff (M i) (M j) ∩ (Vx (f i) ∩ Vx (f j))) = 0 ∧
      ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ (Vx (f i) ∩ Vx (f j)))),
        θ i x = θ j x ∧ ξ i x = ξ j x := fun i j =>
    Submission.ltg_tau_unique_on_open P k U (Vx (f i) ∩ Vx (f j))
      ((hVo _ (hfU i)).inter (hVo _ (hfU j))) (inter_subset_left.trans (hVU _ (hfU i)))
      (M i) (M j) (θ i) (θ j) (ξ i) (ξ j) (hT i) (hT j) fun ω hω => by
        rw [← hrep i ω, ← hrep j ω, ← hXY _ (hfU i) ω (hω.trans inter_subset_left),
          ← hXY _ (hfU j) ω (hω.trans inter_subset_right)]
  -- Glue them (tangent spaces transfer by `br_weightedTangent_congr`).
  obtain ⟨M₀, θ₀, ξ₀, hT₀, hθ₀, hagree⟩ :=
    Submission.ltg_glue_triples P k U (Submission.br_weightedTangent_congr P k)
      (fun i => Vx (f i)) M θ ξ (fun i => hVo _ (hfU i)) hcover hT hθ hcompat
  -- `X = Y_{f i} = τ(M_i, θ_i, ξ_i) = τ(M₀, θ₀, ξ₀)` on forms supported in `V_{f i}`.
  refine ⟨M₀, θ₀, ξ₀, hT₀, hθ₀, Submission.ltg_tau_local_to_global P k U X M₀ θ₀ ξ₀ hT₀ ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  refine ⟨Vx (f i), hVo _ (hfU i), hxi, fun ω hω => ?_⟩
  rw [hXY _ (hfU i) ω hω, hrep i ω]
  exact Submission.ltg_tau_congr_on_open P k (M i) M₀ (θ i) θ₀ (ξ i) ξ₀ (Vx (f i))
    (hVo _ (hfU i)) (hagree i).1 (hagree i).2 ω hω

/-- The case `n = 0` of Simon Ch. 6, 3.11 and 8.2 (p. 176, "trivial in case `n = 0`"), used for
6.3: a weak limit `X` of integer multiplicity `X_j ∈ 𝒟₀(U)` with `sup_j M_W(X_j) < ∞` for every
`W ⊂⊂ U` is integer multiplicity.  Each `X_j` is a locally finite integer Dirac sum
`∑ᶠ_{x ∈ N_j} c_j(x) ω(x)`.  Near `x₀ ∈ U` take `W = B_{ε/2}(x₀) ⊂⊂ U`; testing with signed bumps,
`∑_{x ∈ S} |c_j(x)| ≤ Λ = sup_j M_W(X_j)` for finite `S ⊆ N_j ∩ W`, so on forms supported in `W` the
limit `X` is a finite integer Dirac sum, which is an integer multiplicity current.  These local
representations patch together. -/
theorem Submission.br_zero_dim_weak_limit_isIntegerMultiplicity : ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0), (∀ j, IsIntegerMultiplicity (Xj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, (Xj j).massOn W) < ∞) → WeaklyConvergesOn Xj X → IsIntegerMultiplicity X := by
  intro P U hU Xj X hXj hmass hconv
  -- Each `X_j` is a locally finite integer Dirac sum `∑ᶠ_{x ∈ N_j} c_j(x) ω(x)`.
  choose N c hNU hNfin hc hrepr using fun j => Submission.br_zd_im_dirac_repr P U (Xj j) (hXj j)
  refine Submission.br_isIntegerMultiplicity_of_local P 0 U hU X fun x₀ hx₀ => ?_
  -- `W = B_{ε/2}(x₀)` with `B_ε(x₀) ⊆ U`, so `closure W = B̄_{ε/2}(x₀)` is compact and lies in `U`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set W : Set (Eucl P) := ball x₀ (ε / 2)
  have hclW : closure W = closedBall x₀ (ε / 2) := closure_ball x₀ (half_pos hε).ne'
  have hWK : IsCompact (closure W) := by
    rw [hclW]
    exact isCompact_closedBall x₀ (ε / 2)
  have hclWU : closure W ⊆ U := by
    rw [hclW]
    exact (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hWU : W ⊆ U := subset_closure.trans hclWU
  -- `Λ = sup_j M_W(X_j) < ∞` bounds the weights `∑_{x ∈ S} |c_j(x)|` of the `X_j` in `W`.
  have hΛ : (⨆ j, (Xj j).massOn W) < ∞ := hmass W ⟨isOpen_ball, hWK, hclWU⟩
  obtain ⟨D, a, hDW, hXD⟩ := Submission.br_zd_dirac_local_limit P U W Xj X N c
    (⨆ j, (Xj j).massOn W).toReal hWK hconv hc
    (fun j => (hNfin j _ hWK hclWU).subset (inter_subset_inter_right _ subset_closure))
    (fun j S hS => (ENNReal.ofReal_le_iff_le_toReal hΛ.ne).1
      ((Submission.br_zd_dirac_massOn_ge P U W (N j) (Xj j) (c j) isOpen_ball hWU (hNfin j)
        (hrepr j) S hS).trans (le_iSup (fun j => (Xj j).massOn W) j)))
    (fun j ω _ => hrepr j ω)
  -- On forms supported in `W`, `X` is a finite integer Dirac sum, i.e. integer multiplicity.
  obtain ⟨Y, hY, hYD⟩ := Submission.br_zd_finite_dirac_im P U D a (hDW.trans hWU)
  exact ⟨W, isOpen_ball, mem_ball_self (half_pos hε), hWU, Y, hY,
    fun ω hω => (hXD ω hω).trans (hYD ω).symm⟩
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Y) < ∞` and `|ω(x)| ≤ C` everywhere (Euclidean
coefficient norm) with `C > 0`, then `|Y(ω)| ≤ C · M(Y)`. -/
theorem Submission.br_la_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U n) (ω : TestFormOn U n) (C : ℝ),
      0 < C → (∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      Y.mass ≠ ∞ → |Y ω| ≤ C * Y.mass.toReal := by
  intro P n U Y ω C hC hω hY
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- If `|η| ≤ C` pointwise, then `C⁻¹ η` is mass-admissible, hence `Y(η) ≤ C · M(Y)`.
  have hone : ∀ η : TestFormOn U n,
      (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ C) →
        Y η ≤ C * Y.mass.toReal := by
    intro η hη
    have hadm : C⁻¹ • η ∈ massAdmissibleOn U n U := by
      refine ⟨(C⁻¹ • η).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (C⁻¹ • (η : DifferentialForm (Eucl P) n) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hC), inv_mul_le_iff₀ hC, mul_one]
      exact hη x
    have hle : ENNReal.ofReal (Y (C⁻¹ • η)) ≤ Y.mass := Y.le_massOn hadm
    rwa [ENNReal.ofReal_le_iff_le_toReal hY, map_smul, smul_eq_mul, inv_mul_le_iff₀ hC] at hle
  -- Apply this to `ω` and to `-ω`, using `|-ω(x)| = |ω(x)|` and `Y(-ω) = -Y(ω)`.
  have hneg := hone (-ω) fun x => by
    change covectorEuclideanNorm (-(ω : DifferentialForm (Eucl P) n) x) ≤ C
    rw [covectorEuclideanNorm_neg]
    exact hω x
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hneg
  exact abs_le.mpr ⟨by linarith, hone ω hω⟩
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

/-- **Flat decompositions with vanishing masses converge weakly** (the step "Evidently (1), (2)
give `P_k(ω) → T(ω)`" in the proof of Simon Ch. 6, 6.2, p. 169).  Let `X − P_k = ∂R_k + S_k` with
`M(R_k), M(S_k) → 0`, and fix `ω` with `|ω| ≤ C₁` and `|dω| ≤ C₂`.  Since `∂R_k(ω) = R_k(dω)`,
once both masses are finite `|X(ω) − P_k(ω)| ≤ |R_k(dω)| + |S_k(ω)| ≤ C₂ M(R_k) + C₁ M(S_k)`,
and the right-hand side tends to `0`. -/
theorem Submission.br_la_weaklyConvergesOn_of_flat_decomposition : ∀ (P m : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U (m + 1)) (Pk S : ℕ → GeometricCurrentOn U (m + 1)) (R : ℕ → GeometricCurrentOn U (m + 2)), (∀ (k : ℕ) (ω : TestFormOn U (m + 1)), X ω - Pk k ω = (R k).boundary ω + S k ω) → Tendsto (fun k => (R k).mass) atTop (𝓝 0) → Tendsto (fun k => (S k).mass) atTop (𝓝 0) → WeaklyConvergesOn Pk X := by
  intro P m U X Pk S R hdec hR hS ω
  -- `|ω| ≤ C₁` and `|dω| ≤ C₂` everywhere, where `dω ∈ 𝒟^{m+2}(U)`.
  obtain ⟨C₁, hC₁, hω⟩ := Submission.br_la_testForm_covectorNorm_bounded P (m + 1) U ω
  obtain ⟨C₂, hC₂, hdω⟩ := Submission.br_la_testForm_covectorNorm_bounded P (m + 2) U
    (exteriorDerivativeTestOn U (m + 1) ω)
  -- `M(R_k), M(S_k) → 0` in `[0, ∞]`: eventually finite, with real values tending to `0`.
  have hRfin : ∀ᶠ k in atTop, (R k).mass ≠ ∞ :=
    hR.eventually (eventually_ne_nhds ENNReal.zero_ne_top)
  have hSfin : ∀ᶠ k in atTop, (S k).mass ≠ ∞ :=
    hS.eventually (eventually_ne_nhds ENNReal.zero_ne_top)
  have hRreal : Tendsto (fun k => (R k).mass.toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hR
  have hSreal : Tendsto (fun k => (S k).mass.toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS
  -- For large `k`: `|X(ω) − P_k(ω)| = |R_k(dω) + S_k(ω)| ≤ C₂ M(R_k) + C₁ M(S_k)`.
  have hbound : ∀ᶠ k in atTop,
      ‖X ω - Pk k ω‖ ≤ C₂ * (R k).mass.toReal + C₁ * (S k).mass.toReal := by
    filter_upwards [hRfin, hSfin] with k hRk hSk
    rw [hdec k ω, GeometricCurrentOn.boundary_apply, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add
      (Submission.br_la_abs_apply_le_mul_mass P (m + 2) U (R k)
        (exteriorDerivativeTestOn U (m + 1) ω) C₂ hC₂ hdω hRk)
      (Submission.br_la_abs_apply_le_mul_mass P (m + 1) U (S k) ω C₁ hC₁ hω hSk))
  -- Squeeze: `X(ω) − P_k(ω) → 0`, hence `P_k(ω) → X(ω)`.
  have hlim : Tendsto (fun k => C₂ * (R k).mass.toReal + C₁ * (S k).mass.toReal) atTop
      (𝓝 0) := by
    simpa using (hRreal.const_mul C₂).add (hSreal.const_mul C₁)
  simpa using (tendsto_const_nhds (x := X ω)).sub (squeeze_zero_norm' hbound hlim)
/-- Currents of degree `n > P` in `ℝ^P` vanish (step 1 of the proof of Simon Ch. 6, 6.2): any `n`
vectors of `ℝ^P` are linearly dependent, so every `n`-covector is `0`, every test form is `0`, and
`X(ω) = X(0) = 0`. -/
theorem Submission.br_la_apply_eq_zero_of_lt_degree :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U n), P < n →
      ∀ ω : TestFormOn U n, X ω = 0 := by
  intro P n U X hPn ω
  -- `ω(x)(v) = 0`: `v` is linearly dependent, since otherwise `n ≤ finrank ℝ^P = P`.
  have hω : ω = 0 := by
    apply Subtype.ext
    funext x
    ext v
    refine AlternatingMap.map_linearDependent
      ((ω : DifferentialForm (Eucl P) n) x).toAlternatingMap v fun hv => ?_
    have hle := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hle
    exact absurd hle (Nat.not_le.2 hPn)
  change X.toCurrent ω = 0
  rw [hω, map_zero]
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
theorem Submission.br_top_dim_lattice_approximation : ∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1) → ℤ) (Pk : ℕ → GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), (∀ k, 0 < ρ k) ∧ (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧ WeaklyConvergesOn Pk X ∧ (⨆ k, (Pk k).boundary.mass) < ∞ := by
  classical
  intro m X hX hXm hXb
  let _ : MeasureSpace (Eucl (m + 1)) := measureSpaceOfInnerProductSpace
  let _ : NormedAddCommGroup (Eucl (m + 1)) := inferInstance
  let _ : NormedSpace ℝ (Eucl (m + 1)) := inferInstance
  have hSMm : ∀ I : Fin m → Fin (m + 1), StrictMono I → ∃ k, I = Fin.succAbove k := by
    intro I hI
    obtain ⟨k, hk⟩ : ∃ k, k ∉ Set.range I := by
      by_contra hcon
      push Not at hcon
      have := Fintype.card_le_of_surjective I hcon
      simp at this
    choose J hJ using fun b => Fin.exists_succAbove_eq (fun hb : I b = k => hk ⟨b, hb⟩)
    have hJm : StrictMono J := fun a b hab => by
      have h := hI hab
      rw [← hJ a, ← hJ b] at h
      exact Fin.succAbove_lt_succAbove_iff.1 h
    refine ⟨k, funext fun b => ?_⟩
    rw [← hJ b, hJm.eq_id]; rfl
  have hCNm : ∀ κ : Covector (Eucl (m + 1)) m, covectorEuclideanNorm κ ≤
      Real.sqrt (∑ k : Fin (m + 1),
        (κ (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))) ^ 2) := by
    intro κ
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.image
      (fun k : Fin (m + 1) => (Fin.succAbove k : Fin m → Fin (m + 1)))) (fun I hI => ?_)
      (fun _ _ _ => sq_nonneg _)).trans ((Finset.sum_image_le_of_nonneg
        (fun _ _ => sq_nonneg _)).trans (le_of_eq ?_))
    · obtain ⟨k, rfl⟩ := hSMm I (Finset.mem_filter.1 hI).2
      exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
    · simp only [EuclideanSpace.basisFun_apply]
  have hCN1 : ∀ (κ : Covector (Eucl (m + 1)) m) (k : Fin (m + 1)),
      |κ (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))| ≤ covectorEuclideanNorm κ := by
    intro κ k
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun I : Fin m → Fin (m + 1) => if StrictMono I then
      (κ fun i => EuclideanSpace.basisFun (Fin (m + 1)) ℝ (I i)) ^ 2 else 0)
      (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ (Fin.succAbove k))
    simpa only [Fin.strictMono_succAbove, ite_true, EuclideanSpace.basisFun_apply] using this
  have hCNn : ∀ α : Covector (Eucl (m + 1)) (m + 1),
      covectorEuclideanNorm α = |α (fun i => EuclideanSpace.single i (1 : ℝ))| := by
    intro α
    unfold covectorEuclideanNorm
    rw [Finset.sum_eq_single (id : Fin (m + 1) → Fin (m + 1))]
    · simp only [strictMono_id, ite_true, EuclideanSpace.basisFun_apply, id, Real.sqrt_sq_eq_abs]
    · intro I _ hI; exact ite_eq_right_iff.2 fun h => absurd h.eq_id hI
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨Δ, hΔ, hΔe, hΔτ⟩ : ∃ Δ : Covector (Eucl (m + 1)) (m + 1),
      (∀ (α : Covector (Eucl (m + 1)) (m + 1)) v,
        α v = α (fun i => EuclideanSpace.single i (1 : ℝ)) * Δ v) ∧
      Δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 ∧
      ∀ τ : Fin (m + 1) → Eucl (m + 1), Orthonormal ℝ τ → Δ τ = 1 ∨ Δ τ = -1 := by
    have hdet : ∀ v, wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j) v =
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.det v := by
      intro v
      rw [wedgeCovectors_apply_det, Module.Basis.det_apply]
      congr 1
    have hb : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis =
        fun i => EuclideanSpace.single i (1 : ℝ) := by
      funext i; simp
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), fun α v => ?_, ?_,
      fun τ hτ => ?_⟩
    · have := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis α.toAlternatingMap)
      simp only [AlternatingMap.smul_apply, ContinuousAlternatingMap.coe_toAlternatingMap,
        smul_eq_mul, hb] at this
      rw [hdet]; exact this
    · rw [hdet, ← hb, Module.Basis.det_self]
    · rw [hdet]
      have hsp := hτ.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
      have := OrthonormalBasis.det_to_matrix_orthonormalBasis_real
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (OrthonormalBasis.mk hτ hsp.ge)
      rwa [OrthonormalBasis.coe_mk] at this
  have hDL : ∀ i k : Fin (m + 1), wedgeCovectors m (fun j => EuclideanSpace.proj (Fin.succAbove i j))
      (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ)) = if i = k then 1 else 0 := by
    intro i k
    rw [wedgeCovectors_apply_det]
    split_ifs with hik
    · subst hik
      convert Matrix.det_one (n := Fin m) (R := ℝ)
      ext a c
      simp [Matrix.one_apply]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
      refine Matrix.det_eq_zero_of_row_eq_zero z fun c => ?_
      simp [hz, Ne.symm (Fin.succAbove_ne k c)]
  have hκ : ∀ v : Eucl (m + 1), ∃ κ : Covector (Eucl (m + 1)) m, ∀ k : Fin (m + 1),
      κ (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ)) = (-1 : ℝ) ^ (k : ℕ) * v k := by
    intro v
    refine ⟨∑ i : Fin (m + 1), ((-1 : ℝ) ^ (i : ℕ) * v i) •
      wedgeCovectors m (fun j => EuclideanSpace.proj (Fin.succAbove i j)), fun k => ?_⟩
    simp [hDL]
  have he : ∏ i : Fin (m + 1), ‖(EuclideanSpace.single i (1 : ℝ) : Eucl (m + 1))‖ = 1 := by
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one]
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, X.boundary.mass.toReal = Mb := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := hMb ▸ ENNReal.toReal_nonneg
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  obtain ⟨u, hu_meas, hu_Z, hu_loc, hE1⟩ : ∃ u : Eucl (m + 1) → ℝ, Measurable u ∧
      (∀ x, ∃ k : ℤ, u x = k) ∧ (∀ K, IsCompact K → IntegrableOn u K volume) ∧
      ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1),
        X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    obtain ⟨M, θ, ξ, hT, hθ, hXT⟩ := hX
    obtain ⟨M', hM'M, hM'm, hM'ae⟩ :=
      (hvol ▸ hT.nullMeasurableSet : NullMeasurableSet M volume).exists_measurable_subset_ae_eq
    have hrM : volume.restrict M' = volume.restrict M := Measure.restrict_congr_set hM'ae
    have hor : ∀ᵐ x ∂(volume.restrict M'), ξ x Δ = 1 ∨ ξ x Δ = -1 := by
      have h := hT.orients
      rw [hvol, ← hrM] at h
      filter_upwards [h] with x hx
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      rcases hξ with h | h <;> rw [h]
      · exact hΔτ τ hτ
      · rcases hΔτ τ hτ with h' | h' <;> simp [h']
    have hθm : AEStronglyMeasurable θ (volume.restrict M') := by
      have hU : M' = ⋃ k : ℕ, M' ∩ closedBall 0 k := by
        rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
      rw [hU, aestronglyMeasurable_iUnion_iff]
      intro k
      have h := hT.integrableOn _ (isCompact_closedBall 0 k) (subset_univ _)
      rw [hvol] at h
      exact (h.mono_set (inter_subset_inter_left _ hM'M)).1
    have hsm : AEStronglyMeasurable (fun x => ξ x Δ) (volume.restrict M') := by
      have h := hT.aestronglyMeasurable
      rw [hvol, ← hrM] at h
      exact (ContinuousLinearMap.apply ℝ ℝ Δ).continuous.comp_aestronglyMeasurable h
    have hu₀m : AEStronglyMeasurable (M'.indicator (fun x => θ x * ξ x Δ)) volume :=
      (aestronglyMeasurable_indicator_iff hM'm).2 (hθm.mul hsm)
    have hu₀Z : ∀ᵐ x ∂volume, M'.indicator (fun x => θ x * ξ x Δ) x ∈
        Set.range (Int.cast : ℤ → ℝ) := by
      filter_upwards [(ae_restrict_iff' hM'm).1 hor] with x hx
      by_cases hxM : x ∈ M'
      · rw [indicator_of_mem hxM]
        obtain ⟨k, hk⟩ := hθ x (hM'M hxM)
        rcases hx hxM with h1 | h1 <;> rw [h1, hk]
        · exact ⟨k, by simp⟩
        · exact ⟨-k, by simp⟩
      · rw [indicator_of_notMem hxM]; exact ⟨0, by simp⟩
    have hũm : Measurable (hu₀m.mk _) := hu₀m.stronglyMeasurable_mk.measurable
    have hu_ae : (fun x => if hu₀m.mk _ x ∈ Set.range (Int.cast : ℤ → ℝ) then hu₀m.mk _ x
        else 0) =ᵐ[volume] M'.indicator (fun x => θ x * ξ x Δ) := by
      filter_upwards [hu₀m.ae_eq_mk, hu₀Z] with x h1 h2
      rw [← h1]; simp only [h2, ite_true]
    refine ⟨fun x => if hu₀m.mk _ x ∈ Set.range (Int.cast : ℤ → ℝ) then hu₀m.mk _ x else 0,
      Measurable.ite (hũm (Set.countable_range _).measurableSet) hũm measurable_const,
      fun x => ?_, fun K hK => ?_, fun ω => ?_⟩
    · dsimp only; split_ifs with h
      · obtain ⟨k, hk⟩ := h; exact ⟨k, hk.symm⟩
      · exact ⟨0, by simp⟩
    · refine IntegrableOn.congr_fun_ae ?_ (ae_restrict_of_ae hu_ae.symm)
      rw [IntegrableOn, integrable_indicator_iff hM'm, IntegrableOn,
        Measure.restrict_restrict hM'm]
      have h := hT.integrableOn K hK (subset_univ _)
      rw [hvol] at h
      refine (h.mono_set (inter_subset_inter_left _ hM'M)).mul_bdd
        (hsm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) ?_ (c := 1)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hor] with x hx
      rcases hx with hx | hx <;> simp [hx]
    · rw [hXT ω]
      unfold tauAction
      rw [hvol, ← hrM, ← integral_indicator hM'm]
      refine integral_congr_ae ?_
      filter_upwards [hu_ae] with x hx
      rw [hx]
      by_cases hxM : x ∈ M'
      · rw [indicator_of_mem hxM, indicator_of_mem hxM]
        have h : ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) =
            (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
              (fun i => EuclideanSpace.single i (1 : ℝ)) * ξ x Δ := by
          rw [← smul_eq_mul, ← map_smul]; congr 1; ext v
          rw [hΔ ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) v]; rfl
        rw [h]; ring
      · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, zero_mul]
  have dual : ∀ (w : Eucl (m + 1) → ℝ) (c : ℝ), Measurable w →
      (∀ K, IsCompact K → IntegrableOn w K volume) →
      (∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
          HasCompactSupport φ → (∀ x, |φ x| ≤ 1) → ∫ x, w x * φ x ≤ c) →
      ∫⁻ x, ‖w x‖ₑ ≤ ENNReal.ofReal c := by
    intro w c hw hloc H
    have stepA : ∀ K, IsCompact K → ∫⁻ x in K, ‖w x‖ₑ ≤ ENNReal.ofReal c := by
      intro K hK
      obtain ⟨W, hWo, hKW, -, hWc⟩ :=
        exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
      have hWL : W ⊆ closure W := subset_closure
      have hwL : IntegrableOn w (closure W) volume := hloc _ hWc
      let ν := (volume.restrict (closure W)).withDensity (fun x => ‖w x‖ₑ)
      have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hwL.2.ne
      -- smooth Urysohn approximation of `1_A` up to a set of small `ν`-measure
      have approx : ∀ A, MeasurableSet A → A ⊆ K → ∀ ε : ℝ, 0 < ε →
          ∃ ψ : Eucl (m + 1) → ℝ, ∃ S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
            (∀ x, ψ x ∈ Icc (0 : ℝ) 1) ∧ Function.support ψ ⊆ W ∧ MeasurableSet S ∧
            S ⊆ closure W ∧ (∀ x, |ψ x - A.indicator 1 x| ≤ S.indicator 1 x) ∧
            ∫ x in S, |w x| ≤ 2 * ε := by
        intro A hA hAK ε hε
        have hε' : ENNReal.ofReal ε ≠ 0 := by simpa using hε
        obtain ⟨F, hFA, hFc, hνF⟩ := hA.exists_isClosed_sdiff_lt (μ := ν) (measure_ne_top ν A) hε'
        obtain ⟨U, hAU, hUo, -, hνU⟩ := hA.exists_isOpen_sdiff_lt (μ := ν) (measure_ne_top ν A) hε'
        obtain ⟨ψ, hψd, hψr, hψs, hψ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
          (hUo.inter hWo) hFc (subset_inter (hFA.trans hAU) ((hFA.trans hAK).trans hKW))
        have hψI : ∀ x, ψ x ∈ Icc (0 : ℝ) 1 := fun x => hψr (mem_range_self x)
        have hSm : MeasurableSet ((U ∩ W) \ F) :=
          (hUo.inter hWo).measurableSet.diff hFc.measurableSet
        refine ⟨ψ, (U ∩ W) \ F, hψd, hψI, hψs.subset.trans inter_subset_right, hSm,
          fun x hx => hWL hx.1.2, fun x => ?_, ?_⟩
        · by_cases hxS : x ∈ (U ∩ W) \ F
          · rw [indicator_of_mem hxS, Pi.one_apply, abs_le]
            have := hψI x
            by_cases hxA : x ∈ A
            · rw [indicator_of_mem hxA, Pi.one_apply]; constructor <;> linarith [this.1, this.2]
            · rw [indicator_of_notMem hxA]; constructor <;> linarith [this.1, this.2]
          · rw [indicator_of_notMem hxS]
            by_cases hxF : x ∈ F
            · rw [(hψ1 x).1 hxF, indicator_of_mem (hFA hxF)]; simp
            · have hxUW : x ∉ U ∩ W := fun h => hxS ⟨h, hxF⟩
              have hψ0 : ψ x = 0 := by rw [← Function.notMem_support, hψs]; exact hxUW
              rw [hψ0, indicator_of_notMem (fun h => hxUW ⟨hAU h, hKW (hAK h)⟩)]; simp
        · have hνS : ν ((U ∩ W) \ F) = ∫⁻ x in (U ∩ W) \ F, ‖w x‖ₑ := by
            rw [withDensity_apply _ hSm, Measure.restrict_restrict hSm,
              inter_eq_left.2 (fun x hx => hWL hx.1.2)]
          have hle : ν ((U ∩ W) \ F) < ENNReal.ofReal (2 * ε) := by
            calc ν ((U ∩ W) \ F) ≤ ν ((U \ A) ∪ (A \ F)) := by
                  apply measure_mono
                  rintro x ⟨⟨hxU, -⟩, hxF⟩
                  by_cases hxA : x ∈ A
                  · exact Or.inr ⟨hxA, hxF⟩
                  · exact Or.inl ⟨hxU, hxA⟩
              _ ≤ ν (U \ A) + ν (A \ F) := measure_union_le _ _
              _ < ENNReal.ofReal ε + ENNReal.ofReal ε := ENNReal.add_lt_add hνU hνF
              _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε.le hε.le]; ring_nf
          have h1 := integral_norm_eq_lintegral_enorm (μ := volume.restrict ((U ∩ W) \ F))
            hw.aestronglyMeasurable
          simp only [Real.norm_eq_abs] at h1
          rw [h1, ← hνS]
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle.le
      have hAm : MeasurableSet (K ∩ {x | 0 < w x}) :=
        hK.measurableSet.inter (measurableSet_lt measurable_const hw)
      have hBm : MeasurableSet (K ∩ {x | w x < 0}) :=
        hK.measurableSet.inter (measurableSet_lt hw measurable_const)
      have hwK : IntegrableOn w K volume := hloc K hK
      have hId : ∀ x, w x * ((K ∩ {x | 0 < w x}).indicator 1 x - (K ∩ {x | w x < 0}).indicator 1 x)
          = K.indicator (fun x => |w x|) x := by
        intro x
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK]
          rcases lt_trichotomy (w x) 0 with h | h | h
          · rw [indicator_of_notMem (fun hx => absurd hx.2 (not_lt.2 h.le)),
              indicator_of_mem (show x ∈ K ∩ {x | w x < 0} from ⟨hxK, h⟩), abs_of_neg h]; simp
          · rw [h]; simp
          · rw [indicator_of_mem (show x ∈ K ∩ {x | 0 < w x} from ⟨hxK, h⟩),
              indicator_of_notMem (fun hx => absurd hx.2 (not_lt.2 h.le)), abs_of_pos h]; simp
        · rw [indicator_of_notMem hxK, indicator_of_notMem (fun hx => hxK hx.1),
            indicator_of_notMem (fun hx => hxK hx.1)]; simp
      have hIK : ∫ x in K, |w x| ≤ c := by
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨ψA, SA, hψAd, hψAI, hψAs, hSAm, hSAL, hψAS, hSAe⟩ :=
          approx _ hAm inter_subset_left (ε / 4) (by positivity)
        obtain ⟨ψB, SB, hψBd, hψBI, hψBs, hSBm, hSBL, hψBS, hSBe⟩ :=
          approx _ hBm inter_subset_left (ε / 4) (by positivity)
        have hφs : ∀ x, x ∉ W → ψA x - ψB x = 0 := by
          intro x hxW
          rw [Function.notMem_support.1 (fun h => hxW (hψAs h)),
            Function.notMem_support.1 (fun h => hxW (hψBs h)), sub_zero]
        have hφsupp : Function.support (fun x => ψA x - ψB x) ⊆ W :=
          fun x hx => by_contra fun hxW => hx (hφs x hxW)
        have hφ1 : ∀ x, |ψA x - ψB x| ≤ 1 := fun x => by
          have a := hψAI x; have b := hψBI x
          rw [abs_le]; constructor <;> linarith [a.1, a.2, b.1, b.2]
        have hH := H _ (hψAd.sub hψBd)
          (HasCompactSupport.of_support_subset_isCompact hWc (hφsupp.trans hWL)) hφ1
        have hint1 : Integrable (fun x => w x * (ψA x - ψB x)) volume := by
          refine ((show IntegrableOn (fun x => |w x|) (closure W) volume from hwL.abs).integrable_indicator
            isClosed_closure.measurableSet).mono'
            (hw.mul (hψAd.continuous.sub hψBd.continuous).measurable).aestronglyMeasurable
            (Eventually.of_forall fun x => ?_)
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem (hWL hxW), Real.norm_eq_abs, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hφ1 x)
          · rw [hφs x hxW, mul_zero, norm_zero]
            exact indicator_nonneg (fun _ _ => abs_nonneg _) _
        have hint2 : Integrable (fun x => w x * ((K ∩ {x | 0 < w x}).indicator 1 x -
            (K ∩ {x | w x < 0}).indicator 1 x)) volume := by
          simp_rw [hId]
          exact (show IntegrableOn (fun x => |w x|) K volume from hwK.abs).integrable_indicator
            hK.measurableSet
        have hintS : Integrable (fun x => SA.indicator (fun x => |w x|) x +
            SB.indicator (fun x => |w x|) x) volume :=
          ((show IntegrableOn (fun x => |w x|) SA volume from (hwL.mono_set hSAL).abs).integrable_indicator
            hSAm).add ((show IntegrableOn (fun x => |w x|) SB volume from
              (hwL.mono_set hSBL).abs).integrable_indicator hSBm)
        have m := integral_mono (hint2.sub hint1) hintS (fun x => by
          show w x * (_ - _) - w x * (ψA x - ψB x) ≤ _
          have e : w x * ((K ∩ {x | 0 < w x}).indicator 1 x - (K ∩ {x | w x < 0}).indicator 1 x) -
              w x * (ψA x - ψB x) = w x * (-(ψA x - (K ∩ {x | 0 < w x}).indicator 1 x) +
              (ψB x - (K ∩ {x | w x < 0}).indicator 1 x)) := by ring
          rw [e]
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          calc |w x| * |-(ψA x - (K ∩ {x | 0 < w x}).indicator 1 x) +
                (ψB x - (K ∩ {x | w x < 0}).indicator 1 x)|
              ≤ |w x| * (SA.indicator 1 x + SB.indicator 1 x) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add (hψAS x) (hψBS x))
            _ = SA.indicator (fun x => |w x|) x + SB.indicator (fun x => |w x|) x := by
                simp only [mul_add, Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero])
        have e1 := integral_sub hint2 hint1
        have e2 := integral_add ((show IntegrableOn (fun x => |w x|) SA volume from
          (hwL.mono_set hSAL).abs).integrable_indicator hSAm) ((show IntegrableOn (fun x => |w x|) SB
          volume from (hwL.mono_set hSBL).abs).integrable_indicator hSBm)
        simp only [Pi.sub_apply] at m
        rw [integral_indicator hSAm, integral_indicator hSBm] at e2
        have hK_eq : ∫ x in K, |w x| = ∫ x, w x * ((K ∩ {x | 0 < w x}).indicator 1 x -
            (K ∩ {x | w x < 0}).indicator 1 x) := by
          simp_rw [hId]; rw [integral_indicator hK.measurableSet]
        linarith only [hK_eq, e1, m, e2, hH, hSAe, hSBe]
      rw [← ofReal_integral_norm_eq_lintegral_enorm hwK]
      exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hIK)
    rw [← setLIntegral_univ, ← iUnion_closedBall_nat (0 : Eucl (m + 1)),
      ← withDensity_apply _ (MeasurableSet.iUnion fun _ => measurableSet_closedBall),
      Monotone.measure_iUnion fun i j hij => closedBall_subset_closedBall (by exact_mod_cast hij)]
    refine iSup_le fun j => ?_
    rw [withDensity_apply _ measurableSet_closedBall]
    exact stepA _ (isCompact_closedBall 0 j)
  have hu_int : Integrable u volume := by
    have H : ∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, |φ x| ≤ 1) → ∫ x, u x * φ x ≤ X.mass.toReal := by
      intro φ hφ hφc hφ1
      let ω' : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1) :=
        ⟨fun x => φ x • Δ, ⟨hφ.smul contDiff_const, hφc.smul_right⟩, subset_univ _⟩
      have hval : ∀ x, (φ x • Δ) (fun i => EuclideanSpace.single i (1 : ℝ)) = φ x := fun x => by
        rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hΔe, mul_one]
      have hadm : ω' ∈ massAdmissibleOn univ (m + 1) univ :=
        ⟨subset_univ _, fun x => by rw [hCNn]; exact (congrArg abs (hval x)).trans_le (hφ1 x)⟩
      have hXω : X ω' = ∫ x, u x * φ x := by
        rw [hE1]
        exact integral_congr_ae (Eventually.of_forall fun x => congrArg (u x * ·) (hval x))
      rw [← hXω]
      exact (ENNReal.ofReal_le_iff_le_toReal hXm.ne).1 (GeometricCurrentOn.le_massOn _ hadm)
    exact ⟨hu_meas.aestronglyMeasurable, (dual u _ hu_meas hu_loc H).trans_lt ENNReal.ofReal_lt_top⟩
  have hωh : ∀ {d : ℕ} (ω : TestFormOn (univ : Set (Eucl (m + 1))) d) (w : Fin d → Eucl (m + 1)),
      Continuous (fun x => (ω : DifferentialForm (Eucl (m + 1)) d) x w) ∧
      HasCompactSupport (fun x => (ω : DifferentialForm (Eucl (m + 1)) d) x w) := fun ω w =>
    ⟨ω.property.1.1.continuous.eval_const w,
      ω.property.1.2.comp_left (g := fun α : Covector (Eucl (m + 1)) _ => α w) rfl⟩
  have hV : ∀ ψ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      (∀ x, |ψ x| ≤ 1) → ∀ v : Eucl (m + 1), ‖v‖ ≤ 1 →
      ∫ x, u x * fderiv ℝ ψ x v ≤ Mb := by
    intro ψ hψ hψc hψ1 v hv
    obtain ⟨κ, hκv⟩ := hκ v
    have hωs : IsSmoothForm (fun x => ψ x • κ) := hψ.smul contDiff_const
    have hdω : ∀ x, exteriorDerivative (fun x => ψ x • κ) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ ψ x v := by
      intro x
      rw [exteriorDerivative_apply ((hωs.differentiable (by simp)).differentiableAt)]
      have hd : ∀ k : Fin (m + 1), fderiv ℝ (fun y => (ψ y • κ)
          (Fin.removeNth k fun i => EuclideanSpace.single i (1 : ℝ))) x =
          ((-1 : ℝ) ^ (k : ℕ) * v k) • fderiv ℝ ψ x := by
        intro k
        have h1 : (fun y => (ψ y • κ) (Fin.removeNth k fun i => EuclideanSpace.single i (1 : ℝ))) =
            fun y => ψ y * ((-1 : ℝ) ^ (k : ℕ) * v k) := by
          funext y
          rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← hκv k]; rfl
        rw [h1, fderiv_mul_const ((hψ.differentiable (by simp)) x)]
      have hsum : ∑ k : Fin (m + 1), v k • (EuclideanSpace.single k (1 : ℝ) : Eucl (m + 1)) = v := by
        conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr v]
        simp
      conv_rhs => rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd, smul_apply, smul_eq_mul, zsmul_eq_mul, map_smul, smul_eq_mul]
      have h2 : ((((-1 : ℤ) ^ (k : ℕ) : ℤ) : ℝ)) * (-1 : ℝ) ^ (k : ℕ) = 1 := by
        push_cast; rw [← mul_pow]; norm_num
      beta_reduce
      linear_combination (v k * fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ))) * h2
    let ω' : TestFormOn (univ : Set (Eucl (m + 1))) m :=
      ⟨fun x => ψ x • κ, ⟨hωs, hψc.smul_right⟩, subset_univ _⟩
    have hXω : X.boundary ω' = ∫ x, u x * fderiv ℝ ψ x v := by
      rw [GeometricCurrentOn.boundary_apply, hE1]
      congr 1; funext x; rw [← hdω x]; rfl
    have hadm : ω' ∈ massAdmissibleOn univ m univ := by
      refine ⟨subset_univ _, fun x => (hCNm _).trans ?_⟩
      refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
      have h1 : ∀ k : Fin (m + 1), (((ψ x • κ : Covector (Eucl (m + 1)) m))
          (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))) ^ 2 = ψ x ^ 2 * v k ^ 2 := by
        intro k
        have hs : ((-1 : ℝ) ^ (k : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hκv k, mul_pow, mul_pow, hs, one_mul]
      have h2 : ∑ k : Fin (m + 1), v k ^ 2 = ‖v‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        simp [Real.norm_eq_abs, sq_abs]
      have hψ2 : ψ x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hψ1 x)
      have hv2 : ‖v‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
      change ∑ k : Fin (m + 1), (((ψ x • κ : Covector (Eucl (m + 1)) m))
          (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))) ^ 2 ≤ 1
      simp only [h1, ← Finset.mul_sum, h2]
      exact (mul_le_mul hψ2 hv2 (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [← hXω, ← hMb]
    exact (ENNReal.ofReal_le_iff_le_toReal hXb.ne).1 (GeometricCurrentOn.le_massOn _ hadm)
  have hTr : ∀ h : Eucl (m + 1), ∫⁻ x, ‖u (x + h) - u x‖ₑ ≤
      ENNReal.ofReal (‖h‖ * Mb) := by
    intro h
    have hw : Measurable (fun x => u (x + h) - u x) :=
      (hu_meas.comp (measurable_add_const h)).sub hu_meas
    have hwI : Integrable (fun x => u (x + h) - u x) volume :=
      (hu_int.comp_add_right h).sub hu_int
    suffices H : ∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
        HasCompactSupport φ → (∀ x, |φ x| ≤ 1) →
        ∫ x, (u (x + h) - u x) * φ x ≤ ‖h‖ * Mb by
      exact dual _ _ hw (fun K _ => hwI.integrableOn) H
    intro φ hφ hφc hφ1
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    obtain ⟨B, hB⟩ := hφ'c.bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
    have hφb : ∀ x, ‖φ x‖ ≤ 1 := fun x => by rw [Real.norm_eq_abs]; exact hφ1 x
    have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun y => u y * φ (y - t • h)) volume :=
      fun t => (hu_meas.mul (hφ.continuous.measurable.comp (measurable_id.sub_const _))).aestronglyMeasurable
    have hFd : ∀ t : ℝ, HasDerivAt (fun t => ∫ y, u y * φ (y - t • h))
        (∫ y, u y * fderiv ℝ φ (y - t • h) (-h)) t := by
      intro t
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
        (F := fun t y => u y * φ (y - t • h)) (x₀ := t)
        (F' := fun t y => u y * fderiv ℝ φ (y - t • h) (-h))
        (bound := fun y => ‖u y‖ * (B * ‖h‖)) (s := univ) univ_mem
        (Eventually.of_forall hmeasF) (hu_int.mul_bdd
          (hφ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
          (Eventually.of_forall fun y => hφb _))
        ((hu_meas.mul ((hφ'c.comp (continuous_id.sub continuous_const)).clm_apply
          continuous_const).measurable).aestronglyMeasurable)
        (Eventually.of_forall fun y t' _ => ?_) (hu_int.norm.mul_const _)
        (Eventually.of_forall fun y t' _ => ?_)).2
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left (((fderiv ℝ φ _).le_opNorm _).trans ?_) (norm_nonneg _)
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
      · have h1 : HasDerivAt (fun t : ℝ => y - t • h) (-h) t' := by
          simpa using ((hasDerivAt_id t').smul_const h).const_sub y
        exact ((hφd (y - t' • h)).hasFDerivAt.comp_hasDerivAt t' h1).const_mul (u y)
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun t => ∫ y, u y * φ (y - t • h))
      (fun t => ∫ y, u y * fderiv ℝ φ (y - t • h) (-h)) zero_lt_one
      (fun t _ => (hFd t).continuousAt.continuousWithinAt) (fun t _ => hFd t)
    have hF1 : ∫ y, u y * φ (y - (1 : ℝ) • h) = ∫ x, u (x + h) * φ x := by
      rw [← integral_add_right_eq_self (fun y => u y * φ (y - (1 : ℝ) • h)) h]
      simp
    have hF0 : ∫ y, u y * φ (y - (0 : ℝ) • h) = ∫ x, u x * φ x := by simp
    have hsplit : ∫ x, (u (x + h) - u x) * φ x = (∫ x, u (x + h) * φ x) - ∫ x, u x * φ x := by
      simp only [sub_mul]
      exact integral_sub ((hu_int.comp_add_right h).mul_bdd hφ.continuous.aestronglyMeasurable
        (Eventually.of_forall hφb)) (hu_int.mul_bdd hφ.continuous.aestronglyMeasurable
        (Eventually.of_forall hφb))
    rw [hsplit, ← hF1, ← hF0]
    simp only [sub_zero, div_one] at hc
    rw [← hc]
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
    have hψ := hV (fun y => φ (y + -(c • h))) (hφ.comp (contDiff_id.add contDiff_const))
      (hφc.comp_homeomorph (Homeomorph.addRight (-(c • h)))) (fun y => hφ1 _)
      (‖h‖⁻¹ • (-h)) (by rw [norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ hnh.ne'])
    simp only [fderiv_comp_add_right] at hψ
    simp only [map_smul, smul_eq_mul, ← sub_eq_add_neg] at hψ
    have he : ∀ y, u y * fderiv ℝ φ (y - c • h) (-h) =
        ‖h‖ * (u y * (‖h‖⁻¹ * fderiv ℝ φ (y - c • h) (-h))) := fun y => by
      rw [mul_left_comm, mul_inv_cancel_left₀ hnh.ne']
    simp only [he, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hψ hnh.le
  have main : ∀ ρ : ℝ, 0 < ρ → ∃ (β : LatticeFaceIndex (m + 1) (m + 1) → ℤ)
      (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)),
      IsLatticeChain ρ (fun F => (β F : ℝ)) Pc ∧
      (∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) (c : ℝ),
        (∀ x, |(ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))| ≤ c) →
        |X ω - Pc ω| ≤ c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb)) ∧
      Pc.boundary.mass ≤
        ENNReal.ofReal ((m + 1) * (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb) := by
    intro ρ hρ
    obtain ⟨H, hHdef⟩ : ∃ H : (Fin (m + 1) → ℤ) → Set (Eucl (m + 1)),
        H = fun z => WithLp.ofLp ⁻¹' (Set.univ.pi fun i => Ico (ρ * z i) (ρ * z i + ρ)) := ⟨_, rfl⟩
    have hofLp := PiLp.volume_preserving_ofLp (Fin (m + 1))
    have hHm : ∀ z, MeasurableSet (H z) := fun z => by
      rw [hHdef]; exact hofLp.measurable (MeasurableSet.univ_pi fun i => measurableSet_Ico)
    have hHv : ∀ z, volume (H z) = ENNReal.ofReal (ρ ^ (m + 1)) := fun z => by
      rw [hHdef]; dsimp only
      rw [hofLp.measure_preimage (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet,
        Real.volume_pi_Ico]
      simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow hρ.le]
    have hint : ∀ (a b : ℤ) (t : ℝ), ρ * a ≤ t → t < ρ * b + ρ → a ≤ b := by
      intro a b t h1 h2
      have h3 : (a : ℝ) < b + 1 := lt_of_mul_lt_mul_left (by linarith) hρ.le
      exact Int.lt_add_one_iff.1 (by exact_mod_cast h3)
    have hHd : Pairwise (Function.onFun Disjoint H) := by
      intro z z' hzz'
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rw [hHdef] at hx hx'
      simp only [mem_preimage, mem_univ_pi, mem_Ico] at hx hx'
      exact hzz' (funext fun i => le_antisymm (hint _ _ _ (hx i).1 (hx' i).2)
        (hint _ _ _ (hx' i).1 (hx i).2))
    have hHc : ⋃ z, H z = univ := by
      refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨fun i => ⌊x i / ρ⌋, ?_⟩
      rw [hHdef]
      simp only [mem_preimage, mem_univ_pi, mem_Ico]
      intro i
      have e : ρ * (x i / ρ) = x i := mul_div_cancel₀ _ hρ.ne'
      constructor
      · nlinarith [Int.floor_le (x i / ρ)]
      · nlinarith [Int.lt_floor_add_one (x i / ρ)]
    have hpart : ∀ f : Eucl (m + 1) → ℝ≥0∞, ∑' z, ∫⁻ x in H z, f x = ∫⁻ x, f x := by
      intro f
      rw [← lintegral_iUnion hHm hHd, hHc, Measure.restrict_univ]
    have hHF : ∀ F : LatticeFaceIndex (m + 1) (m + 1), H F.1 =ᵐ[volume] latticeFace ρ F := by
      intro F
      have hr : ∀ i, i ∈ Set.range F.2 := fun i => ⟨i, congrFun F.2.strictMono.eq_id i⟩
      have hL : latticeFace ρ F =
          WithLp.ofLp ⁻¹' Icc (fun i => ρ * F.1 i) (fun i => ρ * F.1 i + ρ) := by
        ext x
        simp only [latticeFace, mem_ofPred_eq, hr, true_implies, not_true_eq_false, false_implies,
          and_true, mem_preimage, mem_Icc, Pi.le_def, mul_add, mul_one]
        exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
      rw [hL, hHdef]
      exact hofLp.quasiMeasurePreserving.preimage_ae_eq Measure.univ_pi_Ico_ae_eq_Icc
    obtain ⟨Q, hQdef⟩ : ∃ Q : Set (Eucl (m + 1)),
        Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ => Ioo (-ρ) ρ) := ⟨_, rfl⟩
    have hQm : MeasurableSet Q := by
      rw [hQdef]; exact hofLp.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    have hQv : volume Q = ENNReal.ofReal ((2 * ρ) ^ (m + 1)) := by
      rw [hQdef, hofLp.measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
      simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.ofReal_pow (by linarith), two_mul]
    have hQn : ∀ h ∈ Q, ‖h‖ ≤ Real.sqrt ((m : ℝ) + 1) * ρ := by
      intro h hh
      rw [hQdef] at hh
      simp only [mem_preimage, mem_univ_pi, mem_Ioo] at hh
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hρ.le, ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖h i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), ρ ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]; exact (sq_lt_sq' (hh i).1 (hh i).2).le
        _ = ((m : ℝ) + 1) * ρ ^ 2 := by simp
    have hHQ : ∀ z, ∀ x ∈ H z, ∀ y ∈ H z, y - x ∈ Q := by
      intro z x hx y hy
      rw [hHdef] at hx hy; rw [hQdef]
      simp only [mem_preimage, mem_univ_pi, mem_Ico, mem_Ioo, WithLp.ofLp_sub, Pi.sub_apply] at hx hy ⊢
      intro i
      constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    have h2ρ : ENNReal.ofReal (ρ ^ (m + 1)) = 2 * ENNReal.ofReal (ρ ^ (m + 1) / 2) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    have hmed : ∀ z, ∃ bz : ℤ, ∀ a : ℝ, ENNReal.ofReal |(bz : ℝ) - a| * ENNReal.ofReal (ρ ^ (m + 1)) ≤
        2 * ∫⁻ x in H z, ‖u x - a‖ₑ := by
      intro z
      have hfm : ∀ j : ℤ, MeasurableSet ({x | (j : ℝ) ≤ u x} ∩ H z) := fun j =>
        (measurableSet_le measurable_const hu_meas).inter (hHm z)
      have hfa : ∀ j k : ℤ, j ≤ k →
          volume ({x | (k : ℝ) ≤ u x} ∩ H z) ≤ volume ({x | (j : ℝ) ≤ u x} ∩ H z) :=
        fun j k hjk => measure_mono (inter_subset_inter_left _ fun x (hx : (k : ℝ) ≤ u x) =>
          (le_trans (by exact_mod_cast hjk) hx : (j : ℝ) ≤ u x))
      have hhpos : 0 < ENNReal.ofReal (ρ ^ (m + 1) / 2) := ENNReal.ofReal_pos.2 (by positivity)
      have hhlt : ENNReal.ofReal (ρ ^ (m + 1) / 2) < volume (H z) := by
        rw [hHv]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
          (by linarith [show 0 < ρ ^ (m + 1) from by positivity])
      obtain ⟨j₁, hj₁⟩ : ∃ j : ℤ,
          volume ({x | (j : ℝ) ≤ u x} ∩ H z) < ENNReal.ofReal (ρ ^ (m + 1) / 2) := by
        by_contra hcon
        push Not at hcon
        have ht := tendsto_measure_iInter_atTop (μ := volume)
          (s := fun k : ℕ => {x | ((k : ℤ) : ℝ) ≤ u x} ∩ H z)
          (fun k => (hfm k).nullMeasurableSet) (fun k l hkl => inter_subset_inter_left _
            fun x (hx : ((l : ℤ) : ℝ) ≤ u x) => (le_trans (by exact_mod_cast hkl) hx : ((k : ℤ) : ℝ) ≤ u x))
          ⟨0, ((measure_mono inter_subset_right).trans_lt
            ((hHv z).symm ▸ ENNReal.ofReal_lt_top)).ne⟩
        have hempty : (⋂ k : ℕ, {x | ((k : ℤ) : ℝ) ≤ u x} ∩ H z) = ∅ := by
          refine eq_empty_of_forall_notMem fun x hx => ?_
          obtain ⟨k, hk⟩ := exists_nat_gt (u x)
          have := (mem_iInter.1 hx k).1
          simp only [mem_ofPred_eq, Int.cast_natCast] at this
          linarith
        rw [hempty, measure_empty] at ht
        exact absurd (ge_of_tendsto' ht fun k => hcon k) (not_le.2 hhpos)
      obtain ⟨j₀, hj₀⟩ : ∃ j : ℤ,
          ENNReal.ofReal (ρ ^ (m + 1) / 2) ≤ volume ({x | (j : ℝ) ≤ u x} ∩ H z) := by
        have ht := tendsto_measure_iUnion_atTop (μ := volume)
          (s := fun k : ℕ => {x | ((-(k : ℤ) : ℤ) : ℝ) ≤ u x} ∩ H z)
          (fun k l hkl => inter_subset_inter_left _ fun x (hx : (((-(k : ℤ)) : ℤ) : ℝ) ≤ u x) =>
            (le_trans (by push_cast; exact neg_le_neg (by exact_mod_cast hkl)) hx :
              (((-(l : ℤ)) : ℤ) : ℝ) ≤ u x))
        have hU : (⋃ k : ℕ, {x | ((-(k : ℤ) : ℤ) : ℝ) ≤ u x} ∩ H z) = H z := by
          refine Subset.antisymm (iUnion_subset fun k => inter_subset_right) fun x hx =>
            mem_iUnion.2 ?_
          obtain ⟨k, hk⟩ := exists_nat_gt (-u x)
          exact ⟨k, ⟨show (((-(k : ℤ) : ℤ)) : ℝ) ≤ u x by push_cast; linarith, hx⟩⟩
        rw [hU] at ht
        obtain ⟨k, hk⟩ := ((tendsto_order.1 ht).1 _ hhlt).exists
        exact ⟨-(k : ℤ), hk.le⟩
      obtain ⟨bz, hbz, hbmax⟩ := Int.exists_greatest_of_bdd (P := fun j : ℤ =>
          ENNReal.ofReal (ρ ^ (m + 1) / 2) ≤ volume ({x | (j : ℝ) ≤ u x} ∩ H z))
        ⟨j₁, fun j hj => by
          by_contra hjj
          exact absurd (hj.trans (hfa _ _ (le_of_lt (not_le.1 hjj)))) (not_le.2 hj₁)⟩ ⟨j₀, hj₀⟩
      have hb1 : volume ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z) < ENNReal.ofReal (ρ ^ (m + 1) / 2) :=
        lt_of_not_ge fun h => absurd (hbmax _ h) (by omega)
      refine ⟨bz, fun a => ?_⟩
      rw [h2ρ, mul_left_comm]
      gcongr
      rcases le_or_gt a bz with hab | hab
      · calc ENNReal.ofReal |(bz : ℝ) - a| * ENNReal.ofReal (ρ ^ (m + 1) / 2)
            ≤ ENNReal.ofReal |(bz : ℝ) - a| * volume ({x | (bz : ℝ) ≤ u x} ∩ H z) := by gcongr
          _ = ∫⁻ x in {x | (bz : ℝ) ≤ u x} ∩ H z, ENNReal.ofReal |(bz : ℝ) - a| :=
            (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in {x | (bz : ℝ) ≤ u x} ∩ H z, ‖u x - a‖ₑ :=
            setLIntegral_mono' (hfm bz) fun x hx => by
              have hx1 : (bz : ℝ) ≤ u x := hx.1
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (abs_le_abs (by linarith) (by linarith))
          _ ≤ ∫⁻ x in H z, ‖u x - a‖ₑ := lintegral_mono_set inter_subset_right
      · have hD : ENNReal.ofReal (ρ ^ (m + 1) / 2) ≤
            volume (H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z)) := by
          rw [measure_sdiff inter_subset_right (hfm _).nullMeasurableSet
            ((measure_mono inter_subset_right).trans_lt ((hHv z).symm ▸ ENNReal.ofReal_lt_top)).ne,
            hHv, h2ρ, two_mul]
          exact ENNReal.le_sub_of_add_le_right ((measure_mono inter_subset_right).trans_lt
            ((hHv z).symm ▸ ENNReal.ofReal_lt_top)).ne (add_le_add le_rfl hb1.le)
        calc ENNReal.ofReal |(bz : ℝ) - a| * ENNReal.ofReal (ρ ^ (m + 1) / 2)
            ≤ ENNReal.ofReal |(bz : ℝ) - a| *
              volume (H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z)) := by gcongr
          _ = ∫⁻ x in H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z), ENNReal.ofReal |(bz : ℝ) - a| :=
            (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z), ‖u x - a‖ₑ :=
            setLIntegral_mono' ((hHm z).diff (hfm _)) fun x hx => by
              obtain ⟨k, hk⟩ := hu_Z x
              have hlt : u x < (bz : ℝ) + 1 := by
                by_contra h
                exact hx.2 ⟨show (((bz + 1 : ℤ)) : ℝ) ≤ u x by push_cast; linarith, hx.1⟩
              have hle : u x ≤ bz := by
                rw [hk] at hlt ⊢
                exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast hlt)
              rw [Real.enorm_eq_ofReal_abs, abs_sub_comm, abs_sub_comm (u x)]
              exact ENNReal.ofReal_le_ofReal (abs_le_abs (by linarith) (by linarith))
          _ ≤ ∫⁻ x in H z, ‖u x - a‖ₑ := lintegral_mono_set sdiff_subset
    choose b hb using hmed
    have hbfin : {z | b z ≠ 0}.Finite := by
      have htsum : ∑' z, ∫⁻ x in H z, ‖u x‖ₑ ≠ ⊤ := by rw [hpart]; exact hu_int.2.ne
      refine (ENNReal.finite_const_le_of_tsum_ne_top htsum
        (ε := ENNReal.ofReal (ρ ^ (m + 1) / 2)) (ENNReal.ofReal_pos.2 (by positivity)).ne').subset
        fun z hz => ?_
      have h1 := hb z 0
      simp only [sub_zero] at h1
      have h3 : (1 : ℝ) ≤ |(b z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
      have h4 : ENNReal.ofReal (ρ ^ (m + 1)) ≤ 2 * ∫⁻ x in H z, ‖u x‖ₑ := by
        refine le_trans ?_ h1
        calc ENNReal.ofReal (ρ ^ (m + 1)) = 1 * ENNReal.ofReal (ρ ^ (m + 1)) := (one_mul _).symm
          _ ≤ ENNReal.ofReal |(b z : ℝ)| * ENNReal.ofReal (ρ ^ (m + 1)) := by
            gcongr; exact ENNReal.one_le_ofReal.2 h3
      rw [h2ρ] at h4
      exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h4
    have hKEY : ∑' z, ∫⁻ x in H z, ‖u x - b z‖ₑ ≤
        ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
      have hPM : ∀ z, ENNReal.ofReal (ρ ^ (m + 1)) * ∫⁻ x in H z, ‖u x - b z‖ₑ ≤
          3 * ∫⁻ y in H z, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by
        intro z
        have hI : ∀ y ∈ H z, ∫⁻ x in H z, ‖u x - b z‖ₑ ≤ 3 * ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by
          intro y hy
          have hDB : ∫⁻ x in H z, ‖u x - u y‖ₑ ≤ ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by
            rw [← lintegral_indicator (hHm z), ← lintegral_add_left_eq_self _ y,
              ← lintegral_indicator hQm]
            refine lintegral_mono fun h => ?_
            by_cases hh : y + h ∈ H z
            · rw [indicator_of_mem hh, indicator_of_mem (by simpa using hHQ z y hy _ hh)]
            · rw [indicator_of_notMem hh]; exact zero_le
          have h1 : ∫⁻ x in H z, ‖u x - b z‖ₑ ≤
              (∫⁻ x in H z, ‖u x - u y‖ₑ) + ENNReal.ofReal (ρ ^ (m + 1)) * ‖u y - b z‖ₑ := by
            calc ∫⁻ x in H z, ‖u x - b z‖ₑ ≤ ∫⁻ x in H z, (‖u x - u y‖ₑ + ‖u y - b z‖ₑ) :=
                  lintegral_mono fun x => by
                    simpa only [sub_add_sub_cancel] using enorm_add_le (u x - u y) (u y - b z)
              _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const, hHv, mul_comm]
          have h2 : ENNReal.ofReal (ρ ^ (m + 1)) * ‖u y - b z‖ₑ ≤ 2 * ∫⁻ x in H z, ‖u x - u y‖ₑ := by
            rw [mul_comm, Real.enorm_eq_ofReal_abs, abs_sub_comm]; exact hb z (u y)
          calc ∫⁻ x in H z, ‖u x - b z‖ₑ
              ≤ (∫⁻ x in H z, ‖u x - u y‖ₑ) + 2 * ∫⁻ x in H z, ‖u x - u y‖ₑ :=
                h1.trans (add_le_add le_rfl h2)
            _ = 3 * ∫⁻ x in H z, ‖u x - u y‖ₑ := by ring
            _ ≤ 3 * ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by gcongr
        calc ENNReal.ofReal (ρ ^ (m + 1)) * ∫⁻ x in H z, ‖u x - b z‖ₑ
            = ∫⁻ y in H z, ∫⁻ x in H z, ‖u x - b z‖ₑ := by rw [setLIntegral_const, hHv, mul_comm]
          _ ≤ ∫⁻ y in H z, 3 * ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := setLIntegral_mono' (hHm z) hI
          _ = 3 * ∫⁻ y in H z, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := lintegral_const_mul' _ _ (by norm_num)
      have hswap : ∫⁻ y, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ = ∫⁻ h in Q, ∫⁻ y, ‖u (y + h) - u y‖ₑ :=
        lintegral_lintegral_swap (((hu_meas.comp measurable_add).sub
          (hu_meas.comp measurable_fst)).enorm.aemeasurable)
      have hQb : ∫⁻ h in Q, ∫⁻ y, ‖u (y + h) - u y‖ₑ ≤
          ENNReal.ofReal (Real.sqrt ((m : ℝ) + 1) * ρ * Mb) * ENNReal.ofReal ((2 * ρ) ^ (m + 1)) := by
        rw [← hQv, ← setLIntegral_const]
        exact setLIntegral_mono' hQm fun h hh => (hTr h).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hQn h hh) hMb0))
      have hne : ENNReal.ofReal (ρ ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [← ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top, ← ENNReal.tsum_mul_left]
      calc ∑' z, ENNReal.ofReal (ρ ^ (m + 1)) * ∫⁻ x in H z, ‖u x - b z‖ₑ
          ≤ ∑' z, 3 * ∫⁻ y in H z, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := ENNReal.tsum_le_tsum hPM
        _ = 3 * ∫⁻ y, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by rw [ENNReal.tsum_mul_left, hpart]
        _ ≤ 3 * (ENNReal.ofReal (Real.sqrt ((m : ℝ) + 1) * ρ * Mb) *
            ENNReal.ofReal ((2 * ρ) ^ (m + 1))) := by rw [hswap]; gcongr
        _ = ENNReal.ofReal (ρ ^ (m + 1)) *
            ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
    have hZbm : ∀ z, z ∉ hbfin.toFinset → b z = 0 := fun z hz => by
      by_contra h; exact hz (hbfin.mem_toFinset.2 h)
    obtain ⟨v, hvdef⟩ : ∃ v : Eucl (m + 1) → ℝ,
        v = fun x => ∑ z ∈ hbfin.toFinset, (H z).indicator (fun _ => (b z : ℝ)) x := ⟨_, rfl⟩
    have hv_meas : Measurable v := by
      rw [hvdef]; exact Finset.measurable_sum _ fun z _ => measurable_const.indicator (hHm z)
    have hv_eq : ∀ z, ∀ x ∈ H z, v x = b z := by
      intro z x hx
      rw [hvdef]; dsimp only
      rw [Finset.sum_eq_single z (fun z' _ hz' => indicator_of_notMem
        (fun hx' => Set.disjoint_left.1 (hHd hz') hx' hx) _)
        (fun hz => by rw [indicator_of_mem hx, hZbm z hz, Int.cast_zero]), indicator_of_mem hx]
    have hv_bdd : ∀ x, ‖v x‖ ≤ ∑ z ∈ hbfin.toFinset, |(b z : ℝ)| := by
      intro x; rw [hvdef]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
      by_cases hx : x ∈ H z
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
      · rw [indicator_of_notMem hx, norm_zero]; exact abs_nonneg _
    have hv_intg : Integrable v volume := by
      rw [hvdef]
      exact integrable_finsetSum _ fun z _ => (integrableOn_const (by rw [hHv]; exact
        ENNReal.ofReal_ne_top)).integrable_indicator (hHm z)
    have hv_int : ∀ g : Eucl (m + 1) → ℝ, Integrable g volume →
        ∫ x, v x * g x = ∑ z ∈ hbfin.toFinset, (b z : ℝ) * ∫ x in H z, g x := by
      intro g hg
      rw [hvdef]
      simp only [Finset.sum_mul]
      rw [integral_finsetSum _ fun z _ => ?_]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [← integral_indicator (hHm z), ← integral_const_mul]
        congr 1; funext x
        by_cases hx : x ∈ H z
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, mul_zero]
      · refine ((hg.indicator (hHm z)).const_mul (b z : ℝ)).congr (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ H z
        · simp only [indicator_of_mem hx]
        · simp only [indicator_of_notMem hx, zero_mul, mul_zero]
    have hI : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Integrable (fun x =>
        v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)))
        volume := fun ω =>
      ((hωh ω _).1.integrable_of_hasCompactSupport (hωh ω _).2).bdd_mul hv_meas.aestronglyMeasurable
        (Eventually.of_forall hv_bdd)
    obtain ⟨F, hF⟩ : ∃ F : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1) → ℝ, ∀ ω, F ω =
        ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := ⟨_, fun _ => rfl⟩
    have hadd : ∀ ω η, F (ω + η) = F ω + F η := fun ω η => by
      rw [hF, hF, hF, ← integral_add (hI ω) (hI η)]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_add _ _ _)
    have hsmul : ∀ (c : ℝ) ω, F (c • ω) = (RingHom.id ℝ) c • F ω := fun c ω => by
      rw [hF, hF, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_left_comm (v x) c _)
    have hcont : ∀ ωs : ℕ → TestFormOn (univ : Set (Eucl (m + 1))) (m + 1),
        TestFormOnConverges ωs 0 → Tendsto (fun j => F (ωs j)) atTop (𝓝 0) := by
      rintro ωs ⟨K, -, -, hsupp, -, hder⟩
      refine Metric.tendsto_nhds.2 fun ε hε => (hder 0 _ (Metric.dist_mem_uniformity
        (show 0 < ε / ((∫ x, ‖v x‖) + 1) by positivity))).mono fun j hj => ?_
      have hbd : ∀ x, ‖(ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ ε / ((∫ x, ‖v x‖) + 1) := by
        intro x
        refine (((ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x).le_opNorm _).trans ?_
        rw [he, mul_one]
        by_cases hx : x ∈ K
        · have h : dist (iteratedFDeriv ℝ 0 ((0 : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) :
              DifferentialForm (Eucl (m + 1)) (m + 1)) x)
              (iteratedFDeriv ℝ 0 (ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x) <
              ε / ((∫ x, ‖v x‖) + 1) := hj x hx
          rw [show ((0 : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) :
            DifferentialForm (Eucl (m + 1)) (m + 1)) = 0 from rfl, iteratedFDeriv_zero, Pi.zero_apply,
            dist_zero_left, norm_iteratedFDeriv_zero] at h
          exact h.le
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]; positivity
      rw [dist_zero_right, hF]
      calc ‖∫ x, v x * (ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x
            (fun i => EuclideanSpace.single i (1 : ℝ))‖
          ≤ ∫ x, ε / ((∫ x, ‖v x‖) + 1) * ‖v x‖ :=
            norm_integral_le_of_norm_le (hv_intg.norm.const_mul _) (Eventually.of_forall fun x => by
              rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _))
        _ = ε / ((∫ x, ‖v x‖) + 1) * ∫ x, ‖v x‖ := integral_const_mul _ _
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          exact mul_lt_mul_of_pos_left (lt_add_one _) hε
    obtain ⟨Pc, hPc⟩ : ∃ Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1),
        ∀ ω, Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := ⟨⟨⟨⟨F, hadd⟩, hsmul⟩, hcont⟩, hF⟩
    have hLFA : ∀ (z : Fin (m + 1) → ℤ) (σ : SimonMultiIndex (m + 1) (m + 1))
        (ω : DifferentialForm (Eucl (m + 1)) (m + 1)),
        latticeFaceAction ρ (z, σ) ω = ∫ x in H z, ω x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
      intro z σ ω
      unfold latticeFaceAction
      rw [hvol, ← setIntegral_congr_set (hHF (z, σ))]
      have hσ : ⇑σ = id := σ.strictMono.eq_id
      simp only [hσ, id]
    have hPcZ : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω =
        ∑ z ∈ hbfin.toFinset, (b z : ℝ) * latticeFaceAction ρ (z, RelEmbedding.refl _) ω := by
      intro ω
      rw [hPc, hv_int _ ((hωh ω _).1.integrable_of_hasCompactSupport (hωh ω _).2)]
      simp only [hLFA]
    have hLC : IsLatticeChain ρ (fun F : LatticeFaceIndex (m + 1) (m + 1) => ((b F.1 : ℤ) : ℝ)) Pc := by
      intro ω
      rw [hPcZ, ← (Equiv.mk (fun z => (z, RelEmbedding.refl _)) Prod.fst (fun _ => rfl)
        (fun F => Prod.ext rfl (DFunLike.coe_injective (F.2.strictMono.eq_id).symm)) :
          (Fin (m + 1) → ℤ) ≃ LatticeFaceIndex (m + 1) (m + 1)).tsum_eq]
      exact (tsum_eq_sum fun z hz => by simp only [hZbm z hz, Int.cast_zero, zero_mul]).symm
    have hres : ∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) (c : ℝ),
        (∀ x, |(ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))| ≤ c) →
        |X ω - Pc ω| ≤ c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
      intro ω c hc
      have hωhi := (hωh ω (fun i => EuclideanSpace.single i (1 : ℝ))).1.integrable_of_hasCompactSupport
        (μ := volume) (hωh ω _).2
      have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
      have huv : Integrable (fun x => u x - v x) volume := hu_int.sub hv_intg
      rw [hE1, hPc, ← integral_sub (hu_int.mul_bdd hωhi.aestronglyMeasurable
        (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hc x))) (hI ω)]
      refine (le_trans (b := ∫ x, c * |u x - v x|) ?_ ?_)
      · rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (huv.abs.const_mul c) (Eventually.of_forall fun x => ?_)
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      have h2 : ∫ x, |u x - v x| = (∫⁻ x, ‖u x - v x‖ₑ).toReal := by
        rw [← integral_norm_eq_lintegral_enorm huv.aestronglyMeasurable]
        simp only [Real.norm_eq_abs]
      rw [h2]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      rw [← hpart]
      exact le_trans (le_of_eq (tsum_congr fun z => setLIntegral_congr_fun (hHm z)
        fun x hx => by simp only [hv_eq z x hx])) hKEY
    have hadj : ∀ i : Fin (m + 1), ∑' z, ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| *
        ρ ^ (m + 1)) ≤ ENNReal.ofReal (2 * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) +
          ρ * Mb) := by
      intro i
      have hcn : ‖ρ • (EuclideanSpace.single i (1 : ℝ) : Eucl (m + 1))‖ = ρ := by
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg hρ.le]
      have hshift : ∀ z, ∫⁻ x in H z, ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) -
          b (z + Pi.single i 1)‖ₑ = ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ := by
        intro z
        rw [← lintegral_indicator (hHm z), ← lintegral_indicator (hHm _)]
        conv_rhs => rw [← lintegral_add_right_eq_self _ (ρ • EuclideanSpace.single i (1 : ℝ))]
        refine lintegral_congr fun x => ?_
        have hiff : x + ρ • EuclideanSpace.single i (1 : ℝ) ∈ H (z + Pi.single i 1) ↔ x ∈ H z := by
          rw [hHdef]
          simp only [mem_preimage, mem_univ_pi, mem_Ico, WithLp.ofLp_add, WithLp.ofLp_smul,
            PiLp.ofLp_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          refine forall_congr' fun j => ?_
          rcases eq_or_ne j i with rfl | hj
          · simp only [Pi.single_eq_same, Int.cast_add, Int.cast_one, mul_add, mul_one,
              add_le_add_iff_right, add_lt_add_iff_right]
          · simp only [Pi.single_eq_of_ne hj, add_zero, mul_zero]
        by_cases hx : x ∈ H z
        · rw [indicator_of_mem hx, indicator_of_mem (hiff.2 hx)]
        · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hiff.1 h))]
      have hz : ∀ z, ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| * ρ ^ (m + 1)) ≤
          (∫⁻ x in H z, ‖u x - b z‖ₑ) + (∫⁻ x in H z,
            ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ) +
          ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ := by
        intro z
        rw [← hshift z]
        calc ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| * ρ ^ (m + 1))
            = ∫⁻ x in H z, ENNReal.ofReal |(b z : ℝ) - b (z + Pi.single i 1)| := by
              rw [setLIntegral_const, hHv, ENNReal.ofReal_mul (abs_nonneg _)]
          _ ≤ ∫⁻ x in H z, (‖u x - b z‖ₑ + ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ +
              ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - b (z + Pi.single i 1)‖ₑ) :=
              lintegral_mono fun x => by
                rw [← Real.enorm_eq_ofReal_abs, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub,
                  ← edist_eq_enorm_sub, ← edist_eq_enorm_sub, edist_comm (u x),
                  edist_comm (u (x + ρ • EuclideanSpace.single i (1 : ℝ)))]
                exact edist_triangle4 _ _ _ _
          _ = _ := by
              have hm1 : Measurable fun x : Eucl (m + 1) =>
                  ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - (b (z + Pi.single i 1) : ℝ)‖ₑ :=
                ((hu_meas.comp (measurable_add_const _)).sub_const _).enorm
              have hm2 : Measurable fun x : Eucl (m + 1) =>
                  ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ :=
                ((hu_meas.comp (measurable_add_const _)).sub hu_meas).enorm
              rw [lintegral_add_right _ hm1, lintegral_add_right _ hm2]
      calc ∑' z, ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| * ρ ^ (m + 1))
          ≤ ∑' z, ((∫⁻ x in H z, ‖u x - b z‖ₑ) + (∫⁻ x in H z,
            ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ) +
            ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ) :=
            ENNReal.tsum_le_tsum hz
        _ = (∑' z, ∫⁻ x in H z, ‖u x - b z‖ₑ) + (∑' z, ∫⁻ x in H z,
            ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ) +
            ∑' z, ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add]
        _ ≤ ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) +
            ENNReal.ofReal (ρ * Mb) +
            ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
            refine add_le_add (add_le_add hKEY ?_) ?_
            · rw [hpart]; exact (hTr _).trans (by rw [hcn])
            · exact (Equiv.tsum_eq (Equiv.addRight (Pi.single i 1))
                (fun z => ∫⁻ y in H z, ‖u y - b z‖ₑ)).le.trans hKEY
        _ = _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    have hface : ∀ (i : Fin (m + 1)) (w : Fin (m + 1) → ℤ),
        (μHE[m] : Measure (Eucl (m + 1))) (latticeFace ρ
          (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))) ≤ ENNReal.ofReal (ρ ^ m) := by
      intro i w
      have hι : Isometry (fun s : EuclideanSpace ℝ (Fin m) => (WithLp.toLp 2 fun l =>
          ρ * (w l : ℝ) + Fin.insertNth (α := fun _ => ℝ) i 0 (WithLp.ofLp s) l : Eucl (m + 1))) :=
        Isometry.of_dist_eq fun s t => by
          rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succAbove _ i]
          simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
            dist_add_left, dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            zero_add]
      have hsub : latticeFace ρ (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _)) ⊆
          (fun s : EuclideanSpace ℝ (Fin m) => (WithLp.toLp 2 fun l =>
            ρ * (w l : ℝ) + Fin.insertNth (α := fun _ => ℝ) i 0 (WithLp.ofLp s) l : Eucl (m + 1))) ''
          (WithLp.ofLp ⁻¹' Icc 0 (fun _ => ρ)) := by
        intro x hx
        have hr : ∀ j, (Fin.succAbove i j) ∈ Set.range
            ((Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _) : Fin m → Fin (m + 1)) :=
          fun j => ⟨j, rfl⟩
        have hi : i ∉ Set.range
            ((Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _) : Fin m → Fin (m + 1)) := by
          rintro ⟨j, hj⟩; exact Fin.succAbove_ne i j hj
        refine ⟨WithLp.toLp 2 fun j => x (Fin.succAbove i j) - ρ * (w (Fin.succAbove i j) : ℝ),
          ⟨fun j => ?_, fun j => ?_⟩, ?_⟩
        · have := ((hx (Fin.succAbove i j)).1 (hr j)).1
          simp only [Pi.zero_apply]; linarith
        · have := ((hx (Fin.succAbove i j)).1 (hr j)).2
          dsimp only; linarith
        · ext l
          dsimp only
          rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
          · rw [Fin.insertNth_apply_same, add_zero, (hx l).2 hi]
          · rw [Fin.insertNth_apply_succAbove]; ring
      calc (μHE[m] : Measure (Eucl (m + 1))) (latticeFace ρ
            (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _)))
          ≤ (μHE[m] : Measure (Eucl (m + 1))) _ := measure_mono hsub
        _ = (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) (WithLp.ofLp ⁻¹' Icc 0 (fun _ => ρ)) :=
          hι.euclideanHausdorffMeasure_image _
        _ = ENNReal.ofReal (ρ ^ m) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
            (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage measurableSet_Icc.nullMeasurableSet,
            Real.volume_Icc_pi]
          simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [ENNReal.ofReal_pow hρ.le]
    have hAbd : ∀ (i : Fin (m + 1)) (w : Fin (m + 1) → ℤ)
        (ω : TestFormOn (univ : Set (Eucl (m + 1))) m),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ 1) →
        |latticeFaceAction ρ (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
          (ω : DifferentialForm (Eucl (m + 1)) m)| ≤ ρ ^ m := by
      intro i w ω hω
      refine (norm_setIntegral_le_of_norm_le_const (C := 1)
        ((hface i w).trans_lt ENNReal.ofReal_lt_top)
        fun x _ => by rw [Real.norm_eq_abs]; exact (hCN1 _ i).trans (hω x)).trans ?_
      rw [one_mul]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hface i w)
    have hbdry : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) m,
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ 1) →
        Pc.boundary ω ≤ (m + 1) * (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb := by
      intro ω hω
      have hst : ∀ z, latticeFaceAction ρ (z, RelEmbedding.refl _)
          (exteriorDerivative (ω : DifferentialForm (Eucl (m + 1)) m)) = ∑ i : Fin (m + 1),
          (-1 : ℝ) ^ (i : ℕ) * (latticeFaceAction ρ (z + Pi.single i 1,
            (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _)) (ω : DifferentialForm (Eucl (m + 1)) m) -
            latticeFaceAction ρ (z, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
              (ω : DifferentialForm (Eucl (m + 1)) m)) := fun z =>
        Submission.br_lattice_face_stokes (m + 1) m ρ hρ (z, RelEmbedding.refl _) ω ω.property.1.1
      rw [GeometricCurrentOn.boundary_apply, hPcZ]
      change ∑ z ∈ hbfin.toFinset, (b z : ℝ) * latticeFaceAction ρ (z, RelEmbedding.refl _)
        (exteriorDerivative (ω : DifferentialForm (Eucl (m + 1)) m)) ≤ _
      simp only [hst, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine (le_abs_self _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      have hfin : ∀ i : Fin (m + 1), |∑ z ∈ hbfin.toFinset, (b z : ℝ) * ((-1 : ℝ) ^ (i : ℕ) *
          (latticeFaceAction ρ (z + Pi.single i 1, (Fin.succAboveOrderEmb i).trans
            (RelEmbedding.refl _)) (ω : DifferentialForm (Eucl (m + 1)) m) -
          latticeFaceAction ρ (z, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
            (ω : DifferentialForm (Eucl (m + 1)) m)))| ≤
          (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb := by
        intro i
        obtain ⟨A, hA⟩ : ∃ A : (Fin (m + 1) → ℤ) → ℝ, ∀ w, latticeFaceAction ρ
            (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
            (ω : DifferentialForm (Eucl (m + 1)) m) = A w := ⟨_, fun _ => rfl⟩
        have hAb : ∀ w, |A w| ≤ ρ ^ m := fun w => (hA w) ▸ hAbd i w ω hω
        simp only [hA]
        have hadj' := hadj i
        generalize (Pi.single i 1 : Fin (m + 1) → ℤ) = e at hadj' ⊢
        have e1 : ∑ z ∈ hbfin.toFinset, (b z : ℝ) * A (z + e) =
            ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e), (b (w - e) : ℝ) * A w := by
          rw [← Finset.sum_subset (s₁ := hbfin.toFinset.image (· + e))
            (f := fun w => (b (w - e) : ℝ) * A w) Finset.subset_union_right ?_,
            Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
          · simp only [add_sub_cancel_right]
          · intro w _ hw
            rw [hZbm _ (fun h => hw (Finset.mem_image.2 ⟨_, h, sub_add_cancel w e⟩)),
              Int.cast_zero, zero_mul]
        have e2 : ∑ z ∈ hbfin.toFinset, (b z : ℝ) * A z =
            ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e), (b w : ℝ) * A w :=
          Finset.sum_subset Finset.subset_union_left fun w _ hw => by
            rw [hZbm w hw, Int.cast_zero, zero_mul]
        have e3 : ∑ z ∈ hbfin.toFinset, (b z : ℝ) * ((-1 : ℝ) ^ (i : ℕ) * (A (z + e) - A z)) =
            (-1 : ℝ) ^ (i : ℕ) * ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e),
              ((b (w - e) : ℝ) - b w) * A w := by
          calc ∑ z ∈ hbfin.toFinset, (b z : ℝ) * ((-1 : ℝ) ^ (i : ℕ) * (A (z + e) - A z))
              = (-1 : ℝ) ^ (i : ℕ) * (∑ z ∈ hbfin.toFinset, (b z : ℝ) * A (z + e) -
                ∑ z ∈ hbfin.toFinset, (b z : ℝ) * A z) := by
                rw [← Finset.sum_sub_distrib, Finset.mul_sum]
                exact Finset.sum_congr rfl fun z _ => by ring
            _ = _ := by rw [e1, e2, ← Finset.sum_sub_distrib]; simp only [sub_mul]
        have hsumW : ρ * ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e),
            |(b (w - e) : ℝ) - b w| * ρ ^ m ≤
            ρ * ((6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb) := by
          rw [Finset.mul_sum, ← ENNReal.ofReal_le_ofReal_iff (by positivity),
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          calc ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e),
                ENNReal.ofReal (ρ * (|(b (w - e) : ℝ) - b w| * ρ ^ m))
              ≤ ∑' w, ENNReal.ofReal (|(b (w - e) : ℝ) - b w| * ρ ^ (m + 1)) := by
                refine le_trans (le_of_eq (Finset.sum_congr rfl fun w _ => by ring_nf))
                  (ENNReal.sum_le_tsum _)
            _ = ∑' z, ENNReal.ofReal (|(b z : ℝ) - b (z + e)| * ρ ^ (m + 1)) := by
                rw [← (Equiv.addRight e).tsum_eq]
                simp only [Equiv.coe_addRight, add_sub_cancel_right]
            _ ≤ _ := hadj'
            _ = _ := by congr 1; ring
        rw [e3, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine le_trans (Finset.sum_le_sum fun w _ => ?_) (le_of_mul_le_mul_left hsumW hρ)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hAb w) (abs_nonneg _)
      refine (Finset.sum_le_sum fun i _ => hfin i).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hmass : Pc.boundary.mass ≤
        ENNReal.ofReal ((m + 1) * (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb) := by
      rw [GeometricCurrentOn.mass, GeometricCurrentOn.massOn]
      refine sSup_le ?_
      rintro _ ⟨ω, hω, rfl⟩
      exact ENNReal.ofReal_le_ofReal (hbdry ω hω.2)
    exact ⟨fun F => b F.1, Pc, hLC, hres, hmass⟩
  choose β Pc hLC hres hbd using fun k : ℕ => main (1 / ((k : ℝ) + 1)) (by positivity)
  refine ⟨fun k => 1 / ((k : ℝ) + 1), β, Pc, fun k => by positivity, hLC, fun ω => ?_,
    (iSup_le hbd).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨c, hc⟩ := (hωh ω (fun i => EuclideanSpace.single i (1 : ℝ))).1.bounded_above_of_compact_support
    (hωh ω _).2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun k : ℕ => c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) *
    (1 / ((k : ℝ) + 1)) * Mb)) (fun k => norm_nonneg _) (fun k => ?_) ?_
  · rw [Real.norm_eq_abs, abs_sub_comm]
    exact hres k ω c fun x => (Real.norm_eq_abs _).symm.trans_le (hc x)
  · have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1)))).mul_const Mb
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring

/-- **Lattice approximation with bounded boundary masses** (the first paragraph of the proof of
Simon Ch. 6, 6.2, p. 169, for `M(X), M(∂X) < ∞`).  If `P < m + 1` every `(m+1)`-current on `ℝ^P`
vanishes and `P_k = 0` works; `P = m + 1` is `br_top_dim_lattice_approximation`.  If
`P = m + 1 + ℓ` with `ℓ ≥ 1`, the Deformation Theorem 5.3 at scale `ρ_k = 1/(k+1)` gives
`X − P_k = ∂R_k + S_k` with integer `β_F`, `M(∂P_k) ≤ C M(∂X)`, `M(R_k) ≤ C ρ_k M(X) → 0` and
`M(S_k) ≤ C ρ_k M(∂X) → 0`, so `P_k ⇀ X`. -/
theorem Submission.br_lattice_approximation : DeformationTheorem → ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) P → ℤ) (Pk : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ k, 0 < ρ k) ∧ (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧ WeaklyConvergesOn Pk X ∧ (⨆ k, (Pk k).boundary.mass) < ∞ := by
  intro hdef P m X hX hXm hXb
  rcases lt_trichotomy P (m + 1) with hP | rfl | hP
  · -- `P < m + 1`: `X = 0`, so `ρ_k = 1`, `β_k = 0`, `P_k = 0` work; `M(∂0) = 0`.
    have h0 : (0 : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)).boundary.mass = 0 := by
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, -, rfl⟩
      simp
    refine ⟨fun _ => 1, fun _ _ => 0, fun _ => 0, fun _ => one_pos, fun _ ω => by simp,
      fun ω => ?_, by simp [h0]⟩
    rw [Submission.br_la_apply_eq_zero_of_lt_degree P (m + 1) univ X hP ω]
    exact tendsto_const_nhds
  · -- `P = m + 1`: the top-dimensional case.
    exact Submission.br_top_dim_lattice_approximation m X hX hXm hXb
  · -- `P = m + 1 + ℓ`, `ℓ ≥ 1`: the Deformation Theorem at scale `ρ_k = 1/(k+1)`.
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, P = m + 1 + ℓ := ⟨P - (m + 1), by omega⟩
    obtain ⟨C, hC⟩ := hdef m ℓ (by omega)
    have hρ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    choose Pc β' R S hlat hdec _ hPb hR hS _ _ hint _ using
      fun k => hC X (ENNReal.add_lt_top.2 ⟨hXm, hXb⟩) _ (hρ k)
    -- `X` is integer multiplicity, so every `β'_k(F)` is an integer `β_k(F)`.
    choose β hβ using fun k => (hint k hX).1
    -- `C ρ_k A → 0` in `[0, ∞]` for finite `A`.
    have hlim : ∀ A : ℝ≥0∞, A ≠ ∞ → Tendsto
        (fun k : ℕ => (C : ℝ≥0∞) * ENNReal.ofReal (1 / ((k : ℝ) + 1)) * A) atTop (𝓝 0) := by
      intro A hA
      have h := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [ENNReal.ofReal_zero] at h
      have h' := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.coe_ne_top (r := C)))) (Or.inr hA)
      rwa [mul_zero, zero_mul] at h'
    refine ⟨fun k => 1 / ((k : ℝ) + 1), β, Pc, hρ, fun k ω => ?_, ?_, ?_⟩
    · simp only [hlat k ω, hβ]
    · -- `M(R_k) ≤ C ρ_k M(X) → 0` and `M(S_k) ≤ C ρ_k M(∂X) → 0`.
      exact Submission.br_la_weaklyConvergesOn_of_flat_decomposition (m + 1 + ℓ) m univ X Pc S R
        hdec
        (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim _ hXm.ne)
          (fun _ => zero_le) hR)
        (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim _ hXb.ne)
          (fun _ => zero_le) hS)
    · -- `sup_k M(∂P_k) ≤ C M(∂X) < ∞`.
      exact (iSup_le hPb).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hXb)

/-- Simon Ch. 6, 6.3 for `U = ℝ^P` and finite masses (proof of 6.3 and Remark 6.4): integer
lattice chains `P_k ⇀ X` with `sup_k M(∂P_k) < ∞` (deformation theorem); the `∂P_k` are integer
multiplicity cycles with `∂P_k ⇀ ∂X` and `M_W(∂P_k) ≤ M(∂P_k)`, so `∂X` is integer multiplicity
by the zero-dimensional case for `m = 0` and by 8.2 for `m ≥ 1`. -/
theorem Submission.br_boundary_isIntegerMultiplicity_of_finite_mass :
    DeformationTheorem → IntegralityOfWeakLimits → ∀ (P m : ℕ)
      (X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), IsIntegerMultiplicity X →
        X.mass < ∞ → X.boundary.mass < ∞ → IsIntegerMultiplicity X.boundary := by
  intro hDef hInt P m X hX hXm hXbm
  obtain ⟨ρ, β, Pk, hρ, hPk, hconv, hbd⟩ :=
    Submission.br_lattice_approximation hDef P m X hX hXm hXbm
  -- `Y_k = ∂P_k` is integer multiplicity and `M_W(Y_k) ≤ M(Y_k) ≤ sup_k M(∂P_k)`.
  have hY : ∀ k, IsIntegerMultiplicity (Pk k).boundary := fun k =>
    Submission.br_lattice_chain_boundary_isIntegerMultiplicity P m (ρ k) (hρ k) (β k) (Pk k)
      (hPk k)
  have hYW : ∀ W, (⨆ k, (Pk k).boundary.massOn W) < ∞ := fun W =>
    (iSup_mono fun k => (Pk k).boundary.massOn_mono (subset_univ W)).trans_lt hbd
  cases m with
  | zero =>
    exact Submission.br_zero_dim_weak_limit_isIntegerMultiplicity P univ isOpen_univ
      (fun k => (Pk k).boundary) X.boundary hY (fun W _ => hYW W) hconv.boundary
  | succ m =>
    -- `∂Y_k = 0 = τ(∅, 0, 0)`: the `Y_k` are integral currents and `M_W(∂Y_k) = 0`.
    have h0 : IsIntegerMultiplicity (0 : GeometricCurrentOn (univ : Set (Eucl P)) m) := by
      refine ⟨∅, fun _ => 0, fun _ => 0,
        { subset := empty_subset _
          nullMeasurableSet := nullMeasurableSet_empty
          countablyRectifiable :=
            Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
          pos := fun x hx => absurd hx (notMem_empty x)
          integrableOn := fun K _ _ => by rw [empty_inter]; exact integrableOn_empty
          aestronglyMeasurable := aestronglyMeasurable_const
          orients := ae_restrict_of_forall_mem MeasurableSet.empty fun x hx =>
            absurd hx (notMem_empty x) },
        fun x hx => absurd hx (notMem_empty x), fun ω => ?_⟩
      rw [GeometricCurrentOn.zero_apply, tauAction, setIntegral_empty]
    have hm0 : ∀ W, (0 : GeometricCurrentOn (univ : Set (Eucl P)) m).massOn W = 0 := fun W =>
      nonpos_iff_eq_zero.1 <| sSup_le <| by
        rintro _ ⟨ω, -, rfl⟩
        simp
    refine hInt P m univ isOpen_univ (fun k => (Pk k).boundary) X.boundary
      (fun k => ⟨hY k, ?_⟩) (fun W _ => ?_) hconv.boundary
    · rw [GeometricCurrentOn.boundary_boundary]
      exact h0
    · simpa only [GeometricCurrentOn.boundary_boundary, hm0, add_zero] using hYW W

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
