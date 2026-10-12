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

/-- **Mass of `τ(M, θ, ξ)` (Simon Ch. 6, Remark 3.2(3), with 2.7–2.8).**  If `T = τ(M, θ, ξ)` for a
rectifiable triple in `U`, then `M_W(T) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  For `Hⁿ`-a.e.
`x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal; with `dx^β` the coordinate wedges, the
Cauchy–Binet identity `∑_β ξ(x)(dx^β)² = 1` (from the expansion `α = ∑_β α(e_β) dx^β` applied to
`⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τₙ, ·⟩`) gives `|ξ(x)(α)| ≤ |α|`, hence `≤`, and makes `b = (ξ(dx^β))_β` a unit
vector with `ξ(∑_β b_β dx^β) = 1`.  For `≥`, exhaust `W ∩ U` by compact sets `K`; approximate
`1_K b` in `L¹(θ Hⁿ ⌞ K')`, `K'` a compact neighbourhood of `K`, by a continuous compactly
supported map, cut it off near `K`, retract it radially onto the unit ball, mollify and rescale.
The resulting test form `ω`, with `|ω| ≤ 1` and `spt ω ⊆ W`, has `T(ω) ≥ ∫_{K ∩ M} θ dHⁿ - ε`. -/
theorem Submission.fiw_im_mass_formula : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U hU T M θ ξ hR hT W hW
  classical
  -- Generic analytic tools, stated for an arbitrary normed space of coefficients.
  -- (D) `L¹` density of continuous compactly supported functions for a finite measure: the proof
  -- of Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` (`p = 1`), whose file is not
  -- imported here.
  have hdense : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (Eucl P))
      [IsFiniteMeasure μ] (f : Eucl P → E), MemLp f 1 μ → ∀ {ε : ℝ≥0∞}, ε ≠ 0 →
      ∃ g : Eucl P → E, HasCompactSupport g ∧ eLpNorm (f - g) 1 μ ≤ ε ∧
        Continuous g ∧ MemLp g 1 μ := by
    intro E _ _ μ _ f hf ε hε
    -- Urysohn approximation of `c • 1_s` for closed `s ⊆ u` open (Mathlib's
    -- `exists_continuous_eLpNorm_sub_le_of_closed`).
    have hury : ∀ {s u : Set (Eucl P)}, IsClosed s → IsOpen u → s ⊆ u → μ s ≠ ∞ →
        ∀ (c : E) {ε : ℝ≥0∞}, ε ≠ 0 → ∃ f : Eucl P → E,
          Continuous f ∧ eLpNorm (fun x => f x - s.indicator (fun _y => c) x) 1 μ ≤ ε ∧
            (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f 1 μ := by
      intro s u s_closed u_open hsu hs c ε hε
      obtain ⟨η, η_pos, hη⟩ :
          ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Eucl P), μ s ≤ η → NullMeasurableSet s μ →
              eLpNorm (s.indicator fun _x => c) 1 μ ≤ ε :=
        exists_eLpNorm_indicator_le ENNReal.one_ne_top c hε
      have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
      obtain ⟨V, sV, V_open, h'V, hV⟩ :
          ∃ (V : Set (Eucl P)), V ⊇ s ∧ IsOpen V ∧ μ V < ∞ ∧ μ (V \ s) < η :=
        s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
      let v := u ∩ V
      have hsv : s ⊆ v := subset_inter hsu sV
      have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
      obtain ⟨g, hgv, hgs, hg_range⟩ :=
        exists_continuous_zero_one_of_isClosed (u_open.inter V_open).isClosed_compl s_closed
          (disjoint_compl_left_iff.2 hsv)
      have g_norm : ∀ x, ‖g x‖ = g x := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
      have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
        intro x
        simp only [norm_smul, g_norm x]
        apply mul_le_of_le_one_left (norm_nonneg _)
        exact (hg_range x).2
      have gc_bd :
          ∀ x, ‖g x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
        intro x
        by_cases hv : x ∈ v
        · rw [← Set.sdiff_union_of_subset hsv] at hv
          rcases hv with hsv | hs
          · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
              Set.indicator_of_mem] using gc_bd0 x
          · simp [hgs hs, hs]
        · simp [hgv hv, show x ∉ s from fun h => hv (hsv h)]
      have gc_support : (Function.support fun x : Eucl P => g x • c) ⊆ v := by
        refine Function.support_subset_iff'.2 fun x hx => ?_
        simp only [hgv hx, Pi.zero_apply, zero_smul]
      have gc_mem : MemLp (fun x => g x • c) 1 μ := by
        refine MemLp.smul ?_ (memLp_top_const (μ := μ) c) (p := 1) (q := ∞) (r := 1)
        have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
        have : eLpNorm (v.indicator fun _x => (1 : ℝ)) 1 μ < ∞ :=
          (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
            simp [lt_top_iff_ne_top, hμv.ne]
        refine (eLpNorm_mono g.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
        by_cases hx : x ∈ v
        · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
            indicator_of_mem, CStarRing.norm_one]
        · simp only [hgv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
      refine ⟨fun x ↦ g x • c, by fun_prop,
        (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator s_closed.measurableSet)) gc_bd).trans ?_, gc_bd0,
          gc_support.trans inter_subset_left, gc_mem⟩
      exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
        ((u_open.measurableSet.inter V_open.measurableSet).diff
          s_closed.measurableSet).nullMeasurableSet
    suffices hex : ∃ g : Eucl P → E,
        eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ MemLp g 1 μ ∧ HasCompactSupport g by
      rcases hex with ⟨g, hg, g_cont, g_mem, g_support⟩
      exact ⟨g, g_support, hg, g_cont, g_mem⟩
    apply hf.induction_dense ENNReal.one_ne_top _ _ _ hε
    rotate_left
    · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
      exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
    intro c t ht htμ ε hε
    rcases exists_Lp_half E μ 1 hε with ⟨δ, δpos, hδ⟩
    obtain ⟨η, ηpos, hη⟩ :
        ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Eucl P), μ s ≤ η → NullMeasurableSet s μ →
            eLpNorm (s.indicator fun _x => c) 1 μ ≤ δ :=
      exists_eLpNorm_indicator_le ENNReal.one_ne_top c δpos.ne'
    have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
    obtain ⟨s, st, s_compact, s_closed, μs⟩ :
        ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
      ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
    have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
    have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) 1 μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
      exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
    obtain ⟨k, k_compact, sk⟩ : ∃ k : Set (Eucl P), IsCompact k ∧ s ⊆ interior k :=
      exists_compact_superset s_compact
    rcases hury s_closed isOpen_interior sk hsμ.ne c δpos.ne'
      with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
    have I3 : eLpNorm (f - t.indicator fun _y => c) 1 μ ≤ ε := by
      convert (hδ _ _ I2 I1).le using 2
      ext x
      simp
    refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
    rw [← Function.notMem_support]
    contrapose hx
    exact interior_subset (f_support hx)
  -- (S) Smoothing: a continuous compactly supported map with `tsupport ⊆ O` (`O` open) is a
  -- uniform limit of smooth maps with compact `tsupport ⊆ O` (convolution with a normalized
  -- bump, then a smooth cutoff equal to `1` on the support).
  have hmoll : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (O : Set (Eucl P)) (u : Eucl P → E), IsOpen O → Continuous u → HasCompactSupport u →
      tsupport u ⊆ O → ∀ ε : ℝ, 0 < ε → ∃ v : Eucl P → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ tsupport v ⊆ O ∧ HasCompactSupport v ∧
          ∀ x, ‖u x - v x‖ ≤ ε := by
    intro E _ _ _ O u hO hu huc huO ε hε
    obtain ⟨O', hO'o, hKO', hO'O, hO'c⟩ :=
      exists_open_between_and_isCompact_closure huc.isCompact hO huO
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hO'o (isClosed_tsupport u) hKO'
    obtain ⟨δ, hδ, huδ⟩ :=
      Metric.uniformContinuous_iff.mp (huc.uniformContinuous_of_continuous hu) ε hε
    obtain ⟨φ, hφs, hφc, hφd, hφr, hφ0⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
    have hφnn : ∀ y, 0 ≤ φ y := fun y => (hφr (mem_range_self y)).1
    have hφint : 0 < ∫ y, φ y :=
      hφd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hφc (fun y => hφnn y)
        (hφ0.symm ▸ one_ne_zero : φ 0 ≠ 0)
    set ψ : Eucl P → ℝ := fun y => (∫ z, φ z)⁻¹ * φ y with hψ_def
    have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hφd
    have hψc : HasCompactSupport ψ := hφc.mul_left
    have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hφint.le) (hφnn y)
    have hψs : Function.support ψ ⊆ ball 0 δ :=
      (Function.support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hφs)
    have hψ1 : ∫ y, ψ y = 1 := by
      rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hφint.ne']
    obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (u x) ≤ ε :=
      ⟨convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume,
        hψc.contDiff_convolution_left _ hψd hu.locallyIntegrable,
        fun x => dist_convolution_le hε.le hψs hψnn hψ1 hu.aestronglyMeasurable
          fun y hy => (huδ (mem_ball.mp hy)).le⟩
    have hv_supp : tsupport (fun x => χ x • g x) ⊆ closure O' := by
      refine (tsupport_smul_subset_left χ g).trans ?_
      rw [tsupport, hχs]
    refine ⟨fun x => χ x • g x, hχ.smul hg, hv_supp.trans hO'O,
      hO'c.of_isClosed_subset (isClosed_tsupport _) hv_supp, fun x => ?_⟩
    beta_reduce
    by_cases hx : x ∈ tsupport u
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  -- (R) The radial retraction `a ↦ a / max 1 ‖a‖` onto the closed unit ball is `2`-Lipschitz
  -- towards points of the ball.
  have hretr : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E), ‖b‖ ≤ 1 →
      ‖(max 1 ‖a‖)⁻¹ • a‖ ≤ 1 ∧ ‖(max 1 ‖a‖)⁻¹ • a - b‖ ≤ 2 * ‖a - b‖ := by
    intro E _ _ a b hb
    have hm : 0 < max 1 ‖a‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, inv_mul_le_iff₀ hm, mul_one]
      exact le_max_right _ _
    · rcases le_total ‖a‖ 1 with ha | ha
      · rw [max_eq_left ha, inv_one, one_smul]
        linarith [norm_nonneg (a - b)]
      · rw [max_eq_right ha]
        have ha0 : 0 < ‖a‖ := lt_of_lt_of_le one_pos ha
        have h1 : ‖‖a‖⁻¹ • a - a‖ = ‖a‖ - 1 := by
          have : ‖a‖⁻¹ • a - a = (‖a‖⁻¹ - 1) • a := by rw [sub_smul, one_smul]
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos, neg_sub, sub_mul,
            inv_mul_cancel₀ ha0.ne', one_mul]
          rw [sub_nonpos]
          exact inv_le_one_of_one_le₀ ha
        have h2 := norm_le_norm_sub_add a b
        calc ‖‖a‖⁻¹ • a - b‖ ≤ ‖‖a‖⁻¹ • a - a‖ + ‖a - b‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * ‖a - b‖ := by rw [h1]; linarith
  -- Linear algebra of `n`-covectors on `ℝ^P` (Simon 1.1–1.5) and Cauchy–Binet.
  set dx : SimonMultiIndex n P → Covector (Eucl P) n :=
    fun I => wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) with hdx
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1 with he
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P, dx β (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    simp only [hdx]
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
        by_contra! h
        apply hβγ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range β ⊆ Set.range γ := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range γ)
        rw [Set.ncard_range_of_injective γ.injective, Set.ncard_range_of_injective β.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [e, PiLp.single_apply, hi j]
  -- Coordinate expansion `α = ∑_β α(e_β) dx^β`.
  have hexp : ∀ α : Covector (Eucl P) n,
      α = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β • dx β := by
    intro α
    set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • dx β with hR
    have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
      intro γ
      rw [hR, ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    have h2 : ∀ v : Fin n → Fin P, Function.Injective v → R (e v) = α (e v) := by
      intro v hv
      have hsm : StrictMono (v ∘ Tuple.sort v) :=
        (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
      have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
      have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
      rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
        ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
        AlternatingMap.map_perm] at hγ
      exact smul_left_cancel _ hγ
    symm
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousAlternatingMap.coe_toAlternatingMap]
    exact h2 v hv
  -- The Euclidean coefficient norm as a sum over increasing multi-indices.
  have hnorm : ∀ α : Covector (Eucl P) n, covectorEuclideanNorm α =
      Real.sqrt (∑ β : SimonMultiIndex n P, (euclideanCovectorCoordinate α β) ^ 2) := by
    intro α
    unfold covectorEuclideanNorm
    congr 1
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij (fun β : SimonMultiIndex n P => (β : Fin n → Fin P))
    · intro β _
      simpa using β.strictMono
    · intro β _ γ _ h
      exact DFunLike.coe_injective h
    · intro I hI
      have hI' : StrictMono I := (Finset.mem_filter.mp hI).2
      exact ⟨OrderEmbedding.ofStrictMono I hI', Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
    · intro β _
      simp [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]
  -- Cauchy–Binet: for an orthonormal frame `τ` and `ζ = ±τ₁ ∧ ⋯ ∧ τₙ`,
  -- `|ζ(α)| ≤ |α|` and `∑_β ζ(dx^β)² = 1`.
  have hALG : ∀ τ : Fin n → Eucl P, Orthonormal ℝ τ → ∀ ζ : NVector (Eucl P) n,
      (ζ = simpleNVector τ ∨ ζ = -simpleNVector τ) →
      (∀ α : Covector (Eucl P) n, |ζ α| ≤ covectorEuclideanNorm α) ∧
        ∑ β : SimonMultiIndex n P, (ζ (dx β)) ^ 2 = 1 := by
    intro τ hτ ζ hζ
    set α₀ : Covector (Eucl P) n := wedgeCovectors n (fun i => innerSL ℝ (τ i)) with hα₀
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀, wedgeCovectors_apply_det]
      have h1 : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp [innerSL_apply_apply, orthonormal_iff_ite.mp hτ, Matrix.one_apply]
      rw [h1, Matrix.det_one]
    have hα₀e : ∀ β : SimonMultiIndex n P, euclideanCovectorCoordinate α₀ β = dx β τ := by
      intro β
      simp only [euclideanCovectorCoordinate, hα₀, hdx, wedgeCovectors_apply_det]
      rw [← Matrix.det_transpose]
      congr 1
      ext i j
      simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    have heval : ∀ α : Covector (Eucl P) n,
        α τ = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β * dx β τ := by
      intro α
      conv_lhs => rw [hexp α]
      rw [ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hsum1 : ∑ β : SimonMultiIndex n P, (dx β τ) ^ 2 = 1 := by
      rw [← hα₀τ, heval α₀]
      simp only [hα₀e, sq]
    obtain ⟨s, hs, hζs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ∀ α : Covector (Eucl P) n, ζ α = s * α τ := by
      rcases hζ with rfl | rfl
      · exact ⟨1, Or.inl rfl, fun α => by simp⟩
      · exact ⟨-1, Or.inr rfl, fun α => by simp⟩
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    refine ⟨fun α => ?_, ?_⟩
    · rw [hζs, abs_mul, habs, one_mul, hnorm, heval]
      apply Real.abs_le_sqrt
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun β => euclideanCovectorCoordinate α β) (fun β => dx β τ)
      rwa [hsum1, mul_one] at this
    · simp only [hζs, mul_pow, hs2, one_mul, hsum1]
  -- Coordinates on `Λⁿ`: `L y = ∑_β y_β dx^β` for `y ∈ ℝ^{multi-indices}` (Euclidean norm), so
  -- `|L y| = ‖y‖`, and `Bv ζ = (ζ(dx^β))_β`.
  set H : Measure (Eucl P) := (μHE[n] : Measure (Eucl P)) with hH
  set L : EuclideanSpace ℝ (SimonMultiIndex n P) →L[ℝ] Covector (Eucl P) n :=
    ∑ β : SimonMultiIndex n P, (EuclideanSpace.proj β).smulRight (dx β) with hL
  have hLapp : ∀ y : EuclideanSpace ℝ (SimonMultiIndex n P),
      L y = ∑ β : SimonMultiIndex n P, y.ofLp β • dx β := by
    intro y
    rw [hL, sum_apply]
    rfl
  have hLnorm : ∀ y : EuclideanSpace ℝ (SimonMultiIndex n P),
      covectorEuclideanNorm (L y) = ‖y‖ := by
    intro y
    rw [hnorm, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hc : euclideanCovectorCoordinate (L y) γ = y.ofLp γ := by
      change (L y) (e γ) = y.ofLp γ
      rw [hLapp, ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc, Real.norm_eq_abs, sq_abs]
  have hLζ : ∀ (ζ : NVector (Eucl P) n) (y : EuclideanSpace ℝ (SimonMultiIndex n P)),
      ζ (L y) = ∑ β : SimonMultiIndex n P, y.ofLp β * ζ (dx β) := by
    intro ζ y
    rw [hLapp, map_sum]
    simp only [map_smul, smul_eq_mul]
  set Bv : NVector (Eucl P) n → EuclideanSpace ℝ (SimonMultiIndex n P) :=
    fun ζ => WithLp.toLp 2 (fun β => ζ (dx β)) with hBv
  have hBvc : Continuous Bv :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun β => continuous_id.clm_apply continuous_const)
  -- Pointwise consequences of the orientation condition, `Hⁿ`-a.e. on `M`.
  have hpt : ∀ᵐ x ∂(H.restrict M),
      (∀ α : Covector (Eucl P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ ‖Bv (ξ x)‖ = 1 ∧
        ξ x (L (Bv (ξ x))) = 1 := by
    filter_upwards [hR.orients] with x hx
    obtain ⟨τ, hτ, -, hξτ⟩ := hx
    obtain ⟨h1, h2⟩ := hALG τ hτ (ξ x) hξτ
    refine ⟨h1, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]
      simp only [hBv, Real.norm_eq_abs, sq_abs, h2, Real.sqrt_one]
    · rw [hLζ, ← h2]
      simp only [hBv, sq]
  -- `M_W(T) ≤ ∫_{M ∩ W} θ dHⁿ`: `|T(ω)| ≤ ∫_M θ |ξ(ω)| dHⁿ` and `|ξ(ω)| ≤ |ω| ≤ 1_W`.
  have hle : T.massOn W ≤ ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H := by
    apply sSup_le
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    change ENNReal.ofReal (T ω) ≤ _
    rw [hT ω]
    calc ENNReal.ofReal (tauAction n M θ ξ ω)
        ≤ ENNReal.ofReal ‖∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x) ∂H‖ :=
          ENNReal.ofReal_le_ofReal (Real.le_norm_self _)
      _ ≤ ENNReal.ofReal (∫⁻ x in M,
            ENNReal.ofReal ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)‖ ∂H).toReal :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)
      _ ≤ ∫⁻ x in M, ENNReal.ofReal ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)‖ ∂H :=
          ENNReal.ofReal_toReal_le
      _ ≤ ∫⁻ x in M, W.indicator (fun x => ENNReal.ofReal (θ x)) x ∂H := by
          apply lintegral_mono_ae
          filter_upwards [hpt, ae_restrict_mem₀ hR.nullMeasurableSet] with x hx hxM
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hR.pos x hxM)]
            exact mul_le_of_le_one_right (hR.pos x hxM).le ((hx.1 _).trans (hω1 x))
          · have h0 : (ω : DifferentialForm (Eucl P) n) x = 0 :=
              image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h)
            rw [h0, map_zero, mul_zero, norm_zero, ENNReal.ofReal_zero]
            exact bot_le
      _ = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H := by
          rw [lintegral_indicator hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
            inter_comm]
  -- `∫_{K ∩ M} θ dHⁿ ≤ M_W(T)` for compact `K ⊆ W ∩ U`.
  have hmain : ∀ K : Set (Eucl P), IsCompact K → K ⊆ W ∩ U →
      ∫⁻ x in K ∩ M, ENNReal.ofReal (θ x) ∂H ≤ T.massOn W := by
    intro K hK hKV
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hθK : IntegrableOn θ (K ∩ M) H := by
      rw [inter_comm]
      exact hR.integrableOn K hK (hKV.trans inter_subset_right)
    have hKMn : NullMeasurableSet (K ∩ M) H := hKm.nullMeasurableSet.inter hR.nullMeasurableSet
    rw [← ofReal_integral_eq_lintegral_ofReal hθK
      ((ae_restrict_mem₀ hKMn).mono fun x hx => (hR.pos x hx.2).le)]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨ω, hωad, hωT⟩ : ∃ ω ∈ massAdmissibleOn U n W,
        (∫ x in K ∩ M, θ x ∂H) - ε ≤ T ω := by
      -- Open sets `K ⊆ O₁ ⊆ closure O₁ ⊆ O₂ ⊆ closure O₂ = K' ⊆ W ∩ U`, `K'` compact.
      obtain ⟨O₂, hO₂o, hKO₂, hO₂V, hO₂c⟩ :=
        exists_open_between_and_isCompact_closure hK (hW.inter hU) hKV
      obtain ⟨O₁, hO₁o, hKO₁, hO₁O₂, hO₁c⟩ :=
        exists_open_between_and_isCompact_closure hK hO₂o hKO₂
      set K' := closure O₂ with hK'
      have hK'm : MeasurableSet K' := isClosed_closure.measurableSet
      have hK'U : K' ⊆ U := hO₂V.trans inter_subset_right
      have hKK' : K ⊆ K' := hKO₂.trans subset_closure
      have hθK' : IntegrableOn θ (K' ∩ M) H := by
        rw [inter_comm]
        exact hR.integrableOn K' hO₂c hK'U
      -- The finite measure `ν = θ Hⁿ ⌞ (K' ∩ M)`.
      set ν : Measure (Eucl P) :=
        (H.restrict (K' ∩ M)).withDensity (fun x => ENNReal.ofReal (θ x)) with hν
      have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hθK'.hasFiniteIntegral
      have hνac : ν ≪ H.restrict M :=
        (withDensity_absolutelyContinuous _ _).trans
          (Measure.absolutelyContinuous_of_le (Measure.restrict_mono inter_subset_right le_rfl))
      -- The target `f = 1_K (ζ(dx^β))_β`, `‖f‖ ≤ 1`.
      set f : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        K.indicator (fun x => Bv (ξ x)) with hf
      have hfM : AEStronglyMeasurable f (H.restrict M) :=
        (hBvc.comp_aestronglyMeasurable hR.aestronglyMeasurable).indicator hKm
      have hf1 : ∀ᵐ x ∂(H.restrict M), ‖f x‖ ≤ 1 := by
        filter_upwards [hpt] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK, hx.2.1]
        · rw [hf, indicator_of_notMem hxK, norm_zero]
          exact zero_le_one
      have hfmem : MemLp f 1 ν := MemLp.of_bound (hfM.mono_ac hνac) 1 (hνac.ae_le hf1)
      -- Tolerances.
      set C : ℝ := (ν univ).toReal with hC
      have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
      set ε₁ : ℝ := (ε : ℝ) / 4 with hε₁
      set ε₂ : ℝ := (ε : ℝ) / (4 * (C + 1)) with hε₂
      have hε₁0 : 0 < ε₁ := by positivity
      have hε₂0 : 0 < ε₂ := by positivity
      -- `L¹(ν)` approximation of `f` by a continuous compactly supported `γ₀`.
      obtain ⟨γ₀, -, hγ₀ε, hγ₀c, -⟩ :=
        hdense (EuclideanSpace ℝ (SimonMultiIndex n P)) ν f hfmem
          (ε := ENNReal.ofReal ε₁) (ENNReal.ofReal_pos.mpr hε₁0).ne'
      -- Cutoff `χ` (`= 1` on `K`, `= 0` off `O₁`), then the radial retraction.
      obtain ⟨χ, hχ0, hχ1, hχr⟩ := exists_continuous_zero_one_of_isClosed hO₁o.isClosed_compl
        hK.isClosed (disjoint_compl_left_iff_subset.mpr hKO₁)
      set γ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        fun x => (max 1 ‖χ x • γ₀ x‖)⁻¹ • (χ x • γ₀ x) with hγ
      have hγc : Continuous γ := by
        have h1 : Continuous fun x => χ x • γ₀ x := χ.continuous.smul hγ₀c
        exact ((continuous_const.max h1.norm).inv₀ fun x =>
          (lt_of_lt_of_le one_pos (le_max_left _ _)).ne').smul h1
      have hγs : Function.support γ ⊆ O₁ := by
        intro x hx
        by_contra hxO
        apply hx
        have h0 : χ x = 0 := hχ0 hxO
        simp only [hγ, h0, zero_smul, smul_zero]
      have hγts : tsupport γ ⊆ O₂ := (closure_mono hγs).trans hO₁O₂
      have hγcs : HasCompactSupport γ :=
        hO₁c.of_isClosed_subset (isClosed_tsupport _) (closure_mono hγs)
      have hγ1 : ∀ x, ‖γ x‖ ≤ 1 := fun x => (hretr _ (χ x • γ₀ x) 0 (by simp)).1
      have hγf : ∀ x, ‖f x‖ ≤ 1 → ‖γ x - f x‖ ≤ 2 * ‖γ₀ x - f x‖ := by
        intro x hx
        refine (hretr _ (χ x • γ₀ x) (f x) hx).2.trans ?_
        gcongr
        by_cases hxK : x ∈ K
        · rw [show χ x = 1 from hχ1 hxK, one_smul]
        · rw [hf, indicator_of_notMem hxK, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hχr x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχr x).2
      -- Smoothing and rescaling: `ψ = (1 + ε₂)⁻¹ φ`, `‖ψ‖ ≤ 1`, `‖ψ - γ‖ ≤ 2 ε₂`.
      obtain ⟨φ, hφd, hφO₂, hφc, hφε⟩ :=
        hmoll (EuclideanSpace ℝ (SimonMultiIndex n P)) O₂ γ hO₂o hγc hγcs hγts ε₂ hε₂0
      have hφ1 : ∀ x, ‖φ x‖ ≤ 1 + ε₂ := fun x => by
        have h1 := norm_le_norm_sub_add (φ x) (γ x)
        rw [norm_sub_rev] at h1
        linarith [hφε x, hγ1 x]
      set ψ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        fun x => (1 + ε₂)⁻¹ • φ x with hψ
      have hε₂1 : (0 : ℝ) < 1 + ε₂ := by linarith
      have hψ1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
        rw [hψ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε₂1, inv_mul_le_iff₀ hε₂1,
          mul_one]
        exact hφ1 x
      have hψγ : ∀ x, ‖ψ x - γ x‖ ≤ 2 * ε₂ := fun x => by
        have h1 : ‖ψ x - φ x‖ ≤ ε₂ := by
          have h2 : ψ x - φ x = ((1 + ε₂)⁻¹ - 1) • φ x := by rw [hψ, sub_smul, one_smul]
          have h3 : |(1 + ε₂)⁻¹ - 1| * (1 + ε₂) = ε₂ := by
            rw [abs_of_nonpos (by rw [sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith)),
              neg_sub, sub_mul, inv_mul_cancel₀ hε₂1.ne', one_mul]
            ring
          rw [h2, norm_smul, Real.norm_eq_abs]
          calc |(1 + ε₂)⁻¹ - 1| * ‖φ x‖ ≤ |(1 + ε₂)⁻¹ - 1| * (1 + ε₂) :=
                mul_le_mul_of_nonneg_left (hφ1 x) (abs_nonneg _)
            _ = ε₂ := h3
        calc ‖ψ x - γ x‖ ≤ ‖ψ x - φ x‖ + ‖φ x - γ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ε₂ + ε₂ := add_le_add h1 (by rw [norm_sub_rev]; exact hφε x)
          _ = 2 * ε₂ := by ring
      have hψc : Continuous ψ := by
        have hφcont : Continuous φ := hφd.continuous
        rw [hψ]
        fun_prop
      have hψts : tsupport ψ ⊆ O₂ :=
        (tsupport_comp_subset (g := fun y => (1 + ε₂)⁻¹ • y) (smul_zero _) φ).trans hφO₂
      have hψcs : HasCompactSupport ψ :=
        hφc.comp_left (g := fun y => (1 + ε₂)⁻¹ • y) (smul_zero _)
      -- The test form `ω' = L ∘ ψ`.
      set ω' : Eucl P → Covector (Eucl P) n := fun x => L (ψ x) with hω'
      have hω'd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω' :=
        L.contDiff.comp (hφd.const_smul ((1 + ε₂)⁻¹))
      have hω'ts : tsupport ω' ⊆ O₂ :=
        (tsupport_comp_subset (g := fun y => L y) (map_zero L) ψ).trans hψts
      have hω'c : HasCompactSupport ω' := hψcs.comp_left (g := fun y => L y) (map_zero L)
      have hω'cont : Continuous ω' := L.continuous.comp hψc
      have hO₂W : O₂ ⊆ W ∩ U := subset_closure.trans hO₂V
      refine ⟨⟨ω', ⟨hω'd, hω'c⟩, hω'ts.trans (hO₂W.trans inter_subset_right)⟩,
        ⟨hω'ts.trans (hO₂W.trans inter_subset_left), fun x => ?_⟩, ?_⟩
      · change covectorEuclideanNorm (L (ψ x)) ≤ 1
        rw [hLnorm]
        exact hψ1 x
      · -- `∫_{K ∩ M} θ - ε ≤ T ω`.
        rw [hT]
        change (∫ x in K ∩ M, θ x ∂H) - ε ≤ ∫ x in M, θ x * ξ x (ω' x) ∂H
        have hg₁ : Integrable (K.indicator θ) (H.restrict M) := by
          rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
          exact hθK
        have hξω : AEStronglyMeasurable (fun x => ξ x (ω' x)) (H.restrict M) :=
          (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
            (hR.aestronglyMeasurable.prodMk hω'cont.aestronglyMeasurable)
        have hξω1 : ∀ᵐ x ∂(H.restrict M), ‖ξ x (ω' x)‖ ≤ 1 := by
          filter_upwards [hpt] with x hx
          rw [Real.norm_eq_abs]
          exact (hx.1 _).trans ((hLnorm _).trans_le (hψ1 x))
        have hω'0 : ∀ x, x ∉ K' → ω' x = 0 := fun x hx =>
          image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hω'ts h))
        have hg₂ : Integrable (fun x => θ x * ξ x (ω' x)) (H.restrict M) := by
          have h1 : Integrable (K'.indicator θ) (H.restrict M) := by
            rw [integrable_indicator_iff hK'm, IntegrableOn, Measure.restrict_restrict hK'm]
            exact hθK'
          refine (h1.mul_bdd hξω hξω1).congr (Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ K'
          · simp only [indicator_of_mem hx]
          · simp only [indicator_of_notMem hx, hω'0 x hx, map_zero, mul_zero]
        have hint : (∫ x in K ∩ M, θ x ∂H) = ∫ x in M, K.indicator θ x ∂H := by
          rw [integral_indicator hKm, Measure.restrict_restrict hKm]
        have hkey : ∫⁻ x in M, ENNReal.ofReal ‖K.indicator θ x - θ x * ξ x (ω' x)‖ ∂H ≤
            ENNReal.ofReal ε := by
          have hθm : AEMeasurable (fun x => ENNReal.ofReal (θ x)) (H.restrict (K' ∩ M)) :=
            hθK'.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          have hfK' : AEStronglyMeasurable f (H.restrict (K' ∩ M)) :=
            hfM.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
          have hgm : AEMeasurable (fun x => ENNReal.ofReal ‖f x - ψ x‖) (H.restrict (K' ∩ M)) :=
            (hfK'.sub hψc.aestronglyMeasurable).norm.aemeasurable.ennreal_ofReal
          have hfγ₀ : AEStronglyMeasurable (f - γ₀) ν :=
            (hfM.mono_ac hνac).sub hγ₀c.aestronglyMeasurable
          have hγ₀ε' : ∫⁻ x, ‖f x - γ₀ x‖ₑ ∂ν ≤ ENNReal.ofReal ε₁ := by
            rw [eLpNorm_one_eq_lintegral_enorm hfγ₀] at hγ₀ε
            exact hγ₀ε
          calc ∫⁻ x in M, ENNReal.ofReal ‖K.indicator θ x - θ x * ξ x (ω' x)‖ ∂H
              ≤ ∫⁻ x in M, K'.indicator
                  (fun x => ENNReal.ofReal (θ x) * ENNReal.ofReal ‖f x - ψ x‖) x ∂H := by
                apply lintegral_mono_ae
                filter_upwards [hpt, ae_restrict_mem₀ hR.nullMeasurableSet] with x hx hxM
                have hθx := hR.pos x hxM
                have hid : K.indicator θ x - θ x * ξ x (ω' x) = θ x * ξ x (L (f x - ψ x)) := by
                  rw [map_sub L, map_sub (ξ x)]
                  by_cases hxK : x ∈ K
                  · rw [indicator_of_mem hxK, hf, indicator_of_mem hxK, hx.2.2]
                    ring
                  · rw [indicator_of_notMem hxK, hf, indicator_of_notMem hxK, map_zero, map_zero]
                    ring
                rw [hid]
                by_cases hxK' : x ∈ K'
                · rw [indicator_of_mem hxK', ← ENNReal.ofReal_mul hθx.le]
                  apply ENNReal.ofReal_le_ofReal
                  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθx]
                  exact mul_le_mul_of_nonneg_left ((hx.1 _).trans (hLnorm _).le) hθx.le
                · have hf0 : f x = 0 := indicator_of_notMem (fun h => hxK' (hKK' h)) _
                  have hψ0 : ψ x = 0 :=
                    image_eq_zero_of_notMem_tsupport fun h => hxK' (subset_closure (hψts h))
                  rw [indicator_of_notMem hxK', hf0, hψ0, sub_zero, map_zero, map_zero, mul_zero,
                    norm_zero, ENNReal.ofReal_zero]
            _ = ∫⁻ x, ENNReal.ofReal ‖f x - ψ x‖ ∂ν := by
                rw [lintegral_indicator hK'm, Measure.restrict_restrict hK'm]
                exact (lintegral_withDensity_eq_lintegral_mul₀ hθm hgm).symm
            _ ≤ ∫⁻ x, (2 * ‖f x - γ₀ x‖ₑ + ENNReal.ofReal (2 * ε₂)) ∂ν := by
                apply lintegral_mono_ae
                filter_upwards [hνac.ae_le hf1] with x hx
                have h1 : ‖f x - ψ x‖ ≤ 2 * ‖f x - γ₀ x‖ + 2 * ε₂ :=
                  calc ‖f x - ψ x‖ ≤ ‖f x - γ x‖ + ‖γ x - ψ x‖ :=
                        norm_sub_le_norm_sub_add_norm_sub _ _ _
                    _ ≤ 2 * ‖f x - γ₀ x‖ + 2 * ε₂ := by
                        rw [norm_sub_rev (f x) (γ x), norm_sub_rev (f x) (γ₀ x),
                          norm_sub_rev (γ x) (ψ x)]
                        exact add_le_add (hγf x hx) (hψγ x)
                calc ENNReal.ofReal ‖f x - ψ x‖ ≤ ENNReal.ofReal (2 * ‖f x - γ₀ x‖ + 2 * ε₂) :=
                      ENNReal.ofReal_le_ofReal h1
                  _ = 2 * ‖f x - γ₀ x‖ₑ + ENNReal.ofReal (2 * ε₂) := by
                      rw [ENNReal.ofReal_add (by positivity) (by positivity),
                        ENNReal.ofReal_mul (by norm_num), ofReal_norm, ENNReal.ofReal_ofNat]
            _ = 2 * ∫⁻ x, ‖f x - γ₀ x‖ₑ ∂ν + ENNReal.ofReal (2 * ε₂) * ν univ := by
                rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
                  lintegral_const]
            _ ≤ 2 * ENNReal.ofReal ε₁ + ENNReal.ofReal (2 * ε₂) * ENNReal.ofReal C := by
                rw [hC, ENNReal.ofReal_toReal (measure_ne_top ν univ)]
                gcongr
            _ = ENNReal.ofReal (2 * ε₁ + 2 * ε₂ * C) := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity),
                  ENNReal.ofReal_mul (p := 2 * ε₂) (q := C) (by positivity),
                  ENNReal.ofReal_mul (p := 2) (q := ε₁) (by norm_num), ENNReal.ofReal_ofNat]
            _ ≤ ENNReal.ofReal ε := by
                apply ENNReal.ofReal_le_ofReal
                have h1 : ε₂ * C + ε₂ = (ε : ℝ) / 4 := by
                  rw [hε₂]
                  field_simp
                rw [hε₁]
                linarith
        have h1 := norm_integral_le_lintegral_norm (μ := H.restrict M)
          (fun x => K.indicator θ x - θ x * ξ x (ω' x))
        rw [integral_sub hg₁ hg₂] at h1
        have h2 := (Real.le_norm_self _).trans
          (h1.trans (ENNReal.toReal_le_of_le_ofReal hε0.le hkey))
        rw [hint]
        linarith
    calc ENNReal.ofReal (∫ x in K ∩ M, θ x ∂H) ≤ ENNReal.ofReal (T ω + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (T ω) + ε := by rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ T.massOn W + ε := add_le_add_left (T.le_massOn hωad) _
  -- `∫_{M ∩ W} θ dHⁿ ≤ M_W(T)`: exhaust `W ∩ U` by compact sets.
  have hge : ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H ≤ T.massOn W := by
    have hVo : IsOpen (W ∩ U) := hW.inter hU
    obtain ⟨F, hFc, hFV, hFU, hFm⟩ := hVo.exists_iUnion_isClosed
    set Kk : ℕ → Set (Eucl P) := fun k => F k ∩ closedBall 0 k with hKk
    have hKkc : ∀ k, IsCompact (Kk k) := fun k =>
      (isCompact_closedBall (0 : Eucl P) (k : ℝ)).inter_left (hFc k)
    have hKkV : ∀ k, Kk k ⊆ W ∩ U := fun k => inter_subset_left.trans (hFV k)
    have hKkm : Monotone Kk := fun k l hkl =>
      inter_subset_inter (hFm hkl) (Metric.closedBall_subset_closedBall (by exact_mod_cast hkl))
    have hKkU : ⋃ k, Kk k = W ∩ U := by
      refine Subset.antisymm (iUnion_subset hKkV) fun x hx => ?_
      rw [← hFU] at hx
      obtain ⟨k₀, hk₀⟩ := mem_iUnion.mp hx
      obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.mpr ⟨max k₀ k₁, hFm (le_max_left _ _) hk₀, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact hk₁.trans (by exact_mod_cast le_max_right _ _)
    set ν₀ : Measure (Eucl P) := (H.restrict M).withDensity (fun x => ENNReal.ofReal (θ x))
      with hν₀
    have hν₀A : ∀ A : Set (Eucl P), MeasurableSet A →
        ν₀ A = ∫⁻ x in A ∩ M, ENNReal.ofReal (θ x) ∂H := by
      intro A hA
      rw [hν₀, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hMW : M ∩ W = (W ∩ U) ∩ M := by
      ext x
      constructor
      · rintro ⟨hxM, hxW⟩
        exact ⟨⟨hxW, hR.subset hxM⟩, hxM⟩
      · rintro ⟨⟨hxW, -⟩, hxM⟩
        exact ⟨hxM, hxW⟩
    rw [hMW, ← hν₀A _ hVo.measurableSet, ← hKkU, hKkm.measure_iUnion]
    refine iSup_le fun k => ?_
    rw [hν₀A _ (hKkc k).isClosed.measurableSet]
    exact hmain (Kk k) (hKkc k) (hKkV k)
  exact le_antisymm hle hge

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
