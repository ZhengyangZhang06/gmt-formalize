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

/-- **Lipschitz bound, in the field, for the pairing `∫_Ω Df(b)`.**  If `f` is `C`-Lipschitz on
the open set `Ω ⊆ ℝⁿ` and `b, b'` are integrable on `Ω`, then
`|∫_Ω Df(b) − ∫_Ω Df(b')| ≤ C ∫_Ω |b − b'|`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not
differentiable).  On `Ω` we have `‖Df(w)‖ ≤ C`, so `w ↦ Df(w)(v(w))` is dominated by `C |v|`; it
is a.e. strongly measurable because `Df` is Borel, hence integrable for `v = b, b'`, and the
estimate follows by linearity of the integral and of `Df(w)`. -/
theorem Submission.slicing_im_ll_gws_pairing_bound :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (f : Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C f Ω →
      ∀ b b' : Eucl n → Eucl n, IntegrableOn b Ω (volume : Measure (Eucl n)) →
        IntegrableOn b' Ω (volume : Measure (Eucl n)) →
        |(∫ w in Ω, fderiv ℝ f w (b w)) - ∫ w in Ω, fderiv ℝ f w (b' w)| ≤
          C * ∫ w in Ω, ‖b w - b' w‖ := by
  intro n Ω C f hΩ hf b b' hb hb'
  -- `Ω` is a neighbourhood of each of its points, so `‖Df(w)‖ ≤ C` on `Ω`.
  have hD : ∀ w ∈ Ω, ‖fderiv ℝ f w‖ ≤ C := fun w hw =>
    norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hf
  -- Hence `|Df(w)(v(w))| ≤ C |v(w)|` for a.e. `w ∈ Ω`, for every field `v`.
  have hle : ∀ v : Eucl n → Eucl n,
      ∀ᵐ w ∂(volume : Measure (Eucl n)).restrict Ω, ‖fderiv ℝ f w (v w)‖ ≤ C * ‖v w‖ := by
    intro v
    refine (ae_restrict_iff' hΩ.measurableSet).2 (Eventually.of_forall fun w hw => ?_)
    exact (fderiv ℝ f w).le_of_opNorm_le (hD w hw) (v w)
  -- `w ↦ Df(w)(v(w))` is integrable on `Ω` when `v` is: it is a.e. strongly measurable
  -- (`Df` is Borel) and dominated by `C |v|`.
  have hint : ∀ v : Eucl n → Eucl n, IntegrableOn v Ω volume →
      IntegrableOn (fun w => fderiv ℝ f w (v w)) Ω volume := fun v hv =>
    (hv.norm.const_mul C).mono' ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
      hv.aestronglyMeasurable (measurable_fderiv ℝ f).aestronglyMeasurable) (hle v)
  -- Combine the integrals by linearity, then estimate.
  rw [← integral_sub (hint b hb) (hint b' hb')]
  simp_rw [← map_sub]
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((hb.sub hb').norm.const_mul C) (hle (b - b'))
/-- **Integration by parts against a `C¹` field, for functions Lipschitz on `Ω`.**  Let `Ω ⊆ ℝⁿ`
be open and `b : ℝⁿ → ℝⁿ` be `C¹` with compact support and `tsupport b ⊆ Ω`.  The divergence
`g = ∑ᵢ Dbᵢ(·)(eᵢ)` of `b` is integrable, and for every `f` that is `L`-Lipschitz on `Ω`, `f g` is
integrable on `Ω` and `∫_Ω Df(b) = −∫_Ω f g`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not
differentiable).  Extend `f` to an `L`-Lipschitz `F` on `ℝⁿ` (McShane); `DF = Df` on the open set
`Ω` and `b, g` vanish off `Ω`, so both sides are integrals over `ℝⁿ` with `F` in place of `f`.
Expand `b = ∑ᵢ bᵢ eᵢ`: by Rademacher's theorem `DF(w)(eᵢ)` is the line derivative of `F` along
`eᵢ` for a.e. `w`, and integration by parts for Lipschitz functions moves it onto the compactly
supported Lipschitz coordinate `bᵢ`. -/
theorem Submission.slicing_im_ll_gws_lipschitz_ibp :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (b : Eucl n → Eucl n), IsOpen Ω → ContDiff ℝ 1 b →
      HasCompactSupport b → tsupport b ⊆ Ω → ∃ g : Eucl n → ℝ,
        Integrable g (volume : Measure (Eucl n)) ∧
        ∀ (L : ℝ≥0) (f : Eucl n → ℝ), LipschitzOnWith L f Ω →
          IntegrableOn (fun w => f w * g w) Ω (volume : Measure (Eucl n)) ∧
          ∫ w in Ω, fderiv ℝ f w (b w) = -∫ w in Ω, f w * g w := by
  intro n Ω b hΩ hb hbc hbΩ
  classical
  -- Coordinates `bᵢ` of `b`: `C¹` with compact support, hence Lipschitz; `Dbᵢ = 0` off
  -- `tsupport b`.
  let e : Fin n → Eucl n := fun i => EuclideanSpace.single i 1
  let bi : Fin n → Eucl n → ℝ := fun i x => EuclideanSpace.proj i (b x)
  have hbi_cd : ∀ i, ContDiff ℝ 1 (bi i) := fun i =>
    (EuclideanSpace.proj i : StrongDual ℝ (Eucl n)).contDiff.comp hb
  have hbi_cs : ∀ i, HasCompactSupport (bi i) := fun i =>
    hbc.comp_left (g := fun y => EuclideanSpace.proj i y) (map_zero _)
  have hbi_ts : ∀ i, tsupport (bi i) ⊆ tsupport b := fun i =>
    tsupport_comp_subset (g := fun y => EuclideanSpace.proj i y) (map_zero _) b
  have hbi_lip : ∀ i, ∃ D, LipschitzWith D (bi i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hbi_cs i) (hbi_cd i) one_ne_zero
  have hbi_diff : ∀ i, Differentiable ℝ (bi i) := fun i => (hbi_cd i).differentiable one_ne_zero
  have hbi_cfd : ∀ i, Continuous (fderiv ℝ (bi i)) := fun i =>
    (hbi_cd i).continuous_fderiv one_ne_zero
  have hDbi_zero : ∀ i w, w ∉ tsupport b → fderiv ℝ (bi i) w = 0 := fun i w hw =>
    image_eq_zero_of_notMem_tsupport fun h => hw (hbi_ts i (tsupport_fderiv_subset ℝ h))
  -- The divergence `g = ∑ᵢ Dbᵢ(·)(eᵢ)` is continuous and vanishes off `tsupport b`, so it has
  -- compact support and is integrable.  It does not depend on `L` or `f`.
  let g : Eucl n → ℝ := fun w => ∑ i, fderiv ℝ (bi i) w (e i)
  have hg_cont : Continuous g :=
    continuous_finsetSum _ fun i _ => (hbi_cfd i).clm_apply continuous_const
  have hg_zero : ∀ w, w ∉ tsupport b → g w = 0 := fun w hw =>
    Finset.sum_eq_zero fun i _ => by simp [hDbi_zero i w hw]
  have hg_cs : HasCompactSupport g := HasCompactSupport.intro hbc hg_zero
  refine ⟨g, hg_cont.integrable_of_hasCompactSupport hg_cs, fun L f hf => ?_⟩
  -- McShane: `F` is `L`-Lipschitz on `ℝⁿ` and `F = f` on `Ω`, so `DF = Df` on the open set `Ω`.
  obtain ⟨F, hF, hfF⟩ := hf.extend_real
  have hDf : ∀ w ∈ Ω, fderiv ℝ f w = fderiv ℝ F w := fun w hw =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hw) hfF)
  -- (a): `F g` is continuous with compact support, and `f g = F g` on `Ω`.
  have hFg_int : Integrable (fun w => F w * g w) volume :=
    (hF.continuous.mul hg_cont).integrable_of_hasCompactSupport (hg_cs.mul_left (f := F))
  refine ⟨hFg_int.integrableOn.congr_fun (fun w hw => by simp [hfF hw]) hΩ.measurableSet, ?_⟩
  -- (b) reduces to `∫ DF(b) = −∫ F g` over `ℝⁿ`, as `b` and `g` vanish off `Ω`.
  have h1 : ∫ w in Ω, fderiv ℝ f w (b w) = ∫ w, fderiv ℝ F w (b w) := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun w => fderiv ℝ F w (b w))
      (fun w hw => by simp only [hDf w hw])]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
    simp [image_eq_zero_of_notMem_tsupport fun h => hw (hbΩ h)]
  have h2 : ∫ w in Ω, f w * g w = ∫ w, F w * g w := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun w => F w * g w)
      (fun w hw => by simp only [hfF hw])]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
    simp [hg_zero w fun h => hw (hbΩ h)]
  rw [h1, h2]
  -- Expand `b = ∑ᵢ bᵢ eᵢ`; each term `DF(·)(eᵢ) bᵢ` is integrable, as `‖DF‖ ≤ L` and `bᵢ` is
  -- continuous with compact support.
  have hexp : ∀ w, fderiv ℝ F w (b w) = ∑ i, fderiv ℝ F w (e i) * bi i w := by
    intro w
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (b w)]
    simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, mul_comm, e, bi]
  have hterm_int : ∀ i, Integrable (fun w => fderiv ℝ F w (e i) * bi i w) volume := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hbi_cd i).continuous.integrable_of_hasCompactSupport (hbi_cs i))
      (measurable_fderiv_apply_const ℝ F (e i)).aestronglyMeasurable ?_
    filter_upwards with w
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  -- Rademacher (`DF(w)(eᵢ) = ∂_{eᵢ}F(w)` a.e.) and integration by parts for Lipschitz functions.
  have hibp : ∀ i, ∫ w, fderiv ℝ F w (e i) * bi i w
      = -∫ w, fderiv ℝ (bi i) w (e i) * F w := by
    intro i
    obtain ⟨D, hD⟩ := hbi_lip i
    have hae : (fun w => fderiv ℝ F w (e i) * bi i w)
        =ᵐ[volume] (fun w => lineDeriv ℝ F w (e i) * bi i w) := by
      filter_upwards [hF.ae_differentiableAt (μ := volume)] with w hw
      rw [hw.lineDeriv_eq_fderiv]
    rw [integral_congr_ae hae, hF.integral_lineDeriv_mul_eq hD (hbi_cs i) (e i), ← integral_neg]
    congr 1
    ext w
    rw [((hbi_diff i) w).lineDeriv_eq_fderiv]
    simp
  -- Sum over `i`; each `Dbᵢ(·)(eᵢ) F` is continuous and vanishes off the compact `tsupport b`.
  have hterm2_int : ∀ i, Integrable (fun w => fderiv ℝ (bi i) w (e i) * F w) volume := by
    intro i
    refine (((hbi_cfd i).clm_apply continuous_const).mul
      hF.continuous).integrable_of_hasCompactSupport (HasCompactSupport.intro hbc fun w hw => ?_)
    simp [hDbi_zero i w hw]
  calc ∫ w, fderiv ℝ F w (b w) = ∫ w, ∑ i, fderiv ℝ F w (e i) * bi i w := by
        simp_rw [hexp]
    _ = ∑ i, ∫ w, fderiv ℝ F w (e i) * bi i w :=
        integral_finsetSum _ fun i _ => hterm_int i
    _ = ∑ i, -∫ w, fderiv ℝ (bi i) w (e i) * F w :=
        Finset.sum_congr rfl fun i _ => hibp i
    _ = -∫ w, ∑ i, fderiv ℝ (bi i) w (e i) * F w := by
        rw [integral_finsetSum _ fun i _ => hterm2_int i, Finset.sum_neg_distrib]
    _ = -∫ w, F w * g w := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp [g, Finset.mul_sum, mul_comm]

/-- Convergence of the gradient pairings against a `C¹` test field: if `u_k → u` uniformly on
the open set `Ω`, all `C`-Lipschitz on `Ω`, and `b` is `C¹` with compact support in `Ω`, then
`∫_Ω Du_k(b) → ∫_Ω Du(b)`.  With the weak divergence `g ∈ L¹` of `b` given by
`slicing_im_ll_gws_lipschitz_ibp`, `∫_Ω Du_k(b) - ∫_Ω Du(b) = ∫_Ω (u - u_k) g`, which is at most
`sup_Ω |u - u_k| · ∫_Ω |g|`. -/
theorem Submission.slicing_im_ll_gws_smooth_tendsto : ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (u : Eucl n → ℝ) (ug : ℕ → Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C u Ω → (∀ k, LipschitzOnWith C (ug k) Ω) → TendstoUniformlyOn ug u atTop Ω → ∀ b : Eucl n → Eucl n, ContDiff ℝ 1 b → HasCompactSupport b → tsupport b ⊆ Ω → Tendsto (fun k => ∫ w in Ω, fderiv ℝ (ug k) w (b w)) atTop (𝓝 (∫ w in Ω, fderiv ℝ u w (b w))) := by
  intro n Ω C u ug hΩ hu hug hconv b hb hbc hbΩ
  -- Step 1: the weak divergence `g` of `b`, applied to `u` and to every `u_k` (all
  -- `C`-Lipschitz on `Ω`).
  obtain ⟨g, hg, hgf⟩ := Submission.slicing_im_ll_gws_lipschitz_ibp n Ω b hΩ hb hbc hbΩ
  obtain ⟨hu_int, hu_eq⟩ := hgf C u hu
  -- Step 2: `∫_Ω Du_k(b) - ∫_Ω Du(b) = -∫_Ω u_k g + ∫_Ω u g = ∫_Ω (u - u_k) g`.
  have hdiff : ∀ k, (∫ w in Ω, fderiv ℝ (ug k) w (b w)) - ∫ w in Ω, fderiv ℝ u w (b w) =
      ∫ w in Ω, (u w - ug k w) * g w := fun k => by
    obtain ⟨hk_int, hk_eq⟩ := hgf C (ug k) (hug k)
    simp only [sub_mul]
    rw [hk_eq, hu_eq, integral_sub hu_int hk_int]
    ring
  -- Step 3: `A = ∫_Ω |g| ≥ 0`, `η = ε / (2 (A + 1))`, and `N` with `|u - u_k| < η` on `Ω` for
  -- all `k ≥ N` (uniform convergence).
  obtain ⟨A, hA⟩ : ∃ A, ∫ w in Ω, |g w| = A := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [← hA]
    exact integral_nonneg fun w => abs_nonneg (g w)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hA1 : 0 < 2 * (A + 1) := by linarith
  have hη : 0 < ε / (2 * (A + 1)) := div_pos hε hA1
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv _ hη)
  refine ⟨N, fun k hk => ?_⟩
  -- Step 4: `|∫_Ω (u - u_k) g| ≤ ∫_Ω η |g| = η A`.
  have hbound : ∀ w ∈ Ω, ‖(u w - ug k w) * g w‖ ≤ ε / (2 * (A + 1)) * |g w| := fun w hw => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← Real.dist_eq]
    exact mul_le_mul_of_nonneg_right (hN k hk w hw).le (abs_nonneg (g w))
  have hest : ‖∫ w in Ω, (u w - ug k w) * g w‖ ≤ ∫ w in Ω, ε / (2 * (A + 1)) * |g w| :=
    norm_integral_le_of_norm_le (hg.integrableOn.abs.const_mul _)
      (ae_restrict_of_forall_mem hΩ.measurableSet hbound)
  rw [integral_const_mul, hA] at hest
  -- Step 5: `η A < η · 2 (A + 1) = ε`.
  rw [Real.dist_eq, hdiff k, ← Real.norm_eq_abs]
  calc ‖∫ w in Ω, (u w - ug k w) * g w‖ ≤ ε / (2 * (A + 1)) * A := hest
    _ < ε / (2 * (A + 1)) * (2 * (A + 1)) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ ε hA1.ne'

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
