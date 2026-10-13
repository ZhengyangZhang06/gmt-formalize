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

/-- A coordinate of an `n`-covector is bounded by its Euclidean coefficient norm:
`|α(e_{β(0)}, …, e_{β(n-1)})| ≤ |α|` for every increasing multi-index `β`. -/
theorem Submission.cmb_rb_abs_euclideanCovectorCoordinate_le :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n) (β : SimonMultiIndex n P),
      |euclideanCovectorCoordinate α β| ≤ covectorEuclideanNorm α := by
  intro P n α β
  -- `|c| = √(c²)` and `√` is monotone, so it suffices to bound `c²` by the defining sum.
  rw [covectorEuclideanNorm, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  -- `c²` is the summand of the strictly increasing tuple `β`; every summand is nonnegative.
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun I _ => ?_) (Finset.mem_univ ⇑β))
  · simp only [euclideanCovectorCoordinate, β.strictMono, ↓reduceIte,
      EuclideanSpace.basisFun_apply]
  · exact ite_nonneg (sq_nonneg _) le_rfl
/-- The triangle inequality for the Euclidean coefficient norm of covectors (Simon Ch. 6, 1.15):
`|α + γ| ≤ |α| + |γ|`.  `|a|` is the Euclidean norm of the coefficient vector
`c(a)_I = [I strictly increasing] · a(b_{I(0)}, …, b_{I(n-1)})` in `ℝ^(Fin n → Fin P)`, and `c` is
additive, so this is `norm_add_le` in that Euclidean space. -/
theorem Submission.cmb_rb_covectorEuclideanNorm_add_le :
    ∀ (P n : ℕ) (α γ : Covector (Eucl P) n),
      covectorEuclideanNorm (α + γ) ≤ covectorEuclideanNorm α + covectorEuclideanNorm γ := by
  intro P n α γ
  -- The coefficient vector `c(a)_I = [I strictly increasing] · a(b_{I(0)}, …, b_{I(n-1)})`.
  let c : Covector (Eucl P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun a =>
    WithLp.toLp 2 fun I =>
      if StrictMono I then a (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) else 0
  have hc : ∀ a, covectorEuclideanNorm a = ‖c a‖ := by
    intro a
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [c, Real.norm_eq_abs, sq_abs]
    split_ifs <;> simp
  have hadd : c (α + γ) = c α + c γ := by
    ext I
    simp only [c, PiLp.add_apply, ContinuousAlternatingMap.add_apply]
    split_ifs <;> simp
  rw [hc, hc, hc, hadd]
  exact norm_add_le _ _
/-- Coefficients of a measure representation (2.7) are integrable on compact sets (Simon Ch. 6,
p. 136): for compact `K ⊆ W ⊆ U`, `W` open, test with `ψ = χ dx^β`, where the smooth cutoff `χ`
equals `1` exactly on `K` and has compact support in `W`.  Then `⟨ψ, v⟩` is `μ`-integrable and
agrees on `K` with the coefficient `⟨dx^β, v⟩`. -/
theorem Submission.cmb_rb_measureRepresentation_integrableOn_coeff :
    ∀ (P n : ℕ) (U W : Set (Eucl P)), IsOpen W → W ⊆ U → ∀ (T : GeometricCurrentOn U n)
      (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v →
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ W → ∀ β : SimonMultiIndex n P,
        IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) K μ := by
  intro P n U W hW hWU T μ v hrep K hK hKW β
  -- An open `V` with `K ⊆ V` and `closure V` compact inside `W`.
  obtain ⟨V, hVo, hKV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  -- A smooth cutoff `χ` with `support χ = V` and `χ x = 1 ↔ x ∈ K`.
  obtain ⟨χ, hχs, -, hχV, hχK⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hVo hK.isClosed hKV
  -- The test form `ψ = χ dx^β`.
  let c : Covector (Eucl P) n := wedgeCovectors n (fun j => EuclideanSpace.proj (β j))
  let ψ : DifferentialForm (Eucl P) n := fun x => χ x • c
  have hψV : tsupport ψ ⊆ closure V := by
    simpa [tsupport, hχV] using tsupport_smul_subset_left χ (fun _ => c)
  have hψ : ψ ∈ TestFormOn U n :=
    ⟨⟨hχs.smul contDiff_const, hVc.of_isClosed_subset (isClosed_tsupport _) hψV⟩,
      hψV.trans (hVW.trans hWU)⟩
  -- `⟨ψ, v⟩` is `μ`-integrable and equals the coefficient on the closed set `K`.
  refine (hrep ⟨ψ, hψ⟩).1.integrableOn.congr_fun (fun x hx => ?_) hK.isClosed.measurableSet
  simp [ψ, c, (hχK x).1 hx, euclideanNVectorCoordinate]

/-- **Coordinate pairing estimate, the step "by (2.7)" in the proof of Simon Ch. 6, Lemma 2.15
(p. 137).**  Let the coefficients `v^β = ⟨dx^β, v⟩` of `v` be `μ`-integrable on a measurable set
`K`, and let `θ` be a continuous `n`-form vanishing off `K` with `|θ| ≤ D` (Euclidean coefficient
norm).  Then `f = ∑_β θ(e_β) v^β` is `μ`-integrable and `|∫ f dμ| ≤ D ∑_β ∫_K |v^β| dμ`.  Each
coefficient `θ(e_β)` is continuous with `|θ(e_β)| ≤ |θ| ≤ D`, so `f` is integrable on `K`; it
vanishes off `K`; and `|f| ≤ ∑_β D |v^β|` pointwise. -/
theorem Submission.cmb_rb_integral_coeff_pairing_bound : ∀ (P n : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) (K : Set (Eucl P)), MeasurableSet K → (∀ β : SimonMultiIndex n P, IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) K μ) → ∀ (θ : Eucl P → Covector (Eucl P) n) (D : ℝ), Continuous θ → (∀ x, x ∉ K → θ x = 0) → (∀ x, covectorEuclideanNorm (θ x) ≤ D) → Integrable (fun x => ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β) μ ∧ |∫ x, ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β ∂μ| ≤ D * ∑ β : SimonMultiIndex n P, ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ := by
  intro P n μ v K _hK hv θ D hθ hθK hθD
  -- Step 1: every coefficient is bounded, `|θ(x)(e_β)| ≤ |θ(x)| ≤ D`.
  have hcD : ∀ (β : SimonMultiIndex n P) (x : Eucl P),
      |euclideanCovectorCoordinate (θ x) β| ≤ D := fun β x =>
    (Submission.cmb_rb_abs_euclideanCovectorCoordinate_le P n (θ x) β).trans (hθD x)
  -- Step 2: `x ↦ θ(x)(e_β)` is continuous, as evaluation at `e_β` is continuous.
  have hcc : ∀ β : SimonMultiIndex n P,
      Continuous fun x => euclideanCovectorCoordinate (θ x) β := fun β =>
    hθ.eval_const _
  -- Step 3: each `θ(e_β) v^β`, hence `f`, is `μ`-integrable on `K`.
  have hfK : IntegrableOn (fun x => ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β) K μ :=
    integrable_finsetSum _ fun β _ => Integrable.bdd_mul (hv β) (hcc β).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hcD β x))
  -- Step 4: `f = 0` off `K`, so `f` is `μ`-integrable and `∫ f dμ = ∫_K f dμ`.
  have hf0 : ∀ x, x ∉ K → ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β = 0 := by
    intro x hx
    simp [euclideanCovectorCoordinate, hθK x hx]
  refine ⟨(integrableOn_iff_integrable_of_support_subset
    (Function.support_subset_iff'.2 hf0)).1 hfK, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf0]
  -- Steps 5–6: `|f| ≤ ∑_β D |v^β|` pointwise; integrate over `K`.
  have hg : ∀ β ∈ (Finset.univ : Finset (SimonMultiIndex n P)),
      IntegrableOn (fun x => D * |euclideanNVectorCoordinate (v x) β|) K μ := fun β _ =>
    (hv β).abs.const_mul D
  calc |∫ x in K, ∑ β : SimonMultiIndex n P,
          euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β ∂μ|
      ≤ ∫ x in K, |∑ β : SimonMultiIndex n P,
          euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in K, ∑ β : SimonMultiIndex n P, D * |euclideanNVectorCoordinate (v x) β| ∂μ :=
        integral_mono hfK.abs (integrable_finsetSum _ hg) fun x =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hcD β x) (abs_nonneg _))
    _ = ∑ β : SimonMultiIndex n P, D * ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ := by
        rw [integral_finsetSum _ hg]
        simp only [integral_const_mul]
    _ = D * ∑ β : SimonMultiIndex n P, ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ :=
        (Finset.mul_sum _ _ _).symm
/-- Mass estimate: if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ C` everywhere
(Euclidean covector norm), then `|T(ω)| ≤ B · C`. -/
theorem Submission.cmb_abs_apply_le_of_massOn_le :
    ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B C : ℝ),
      0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      |T ω| ≤ B * C := by
  intro P n U W T ω B C hB hM hW hC
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
  -- `C ≥ 0`, by evaluating the pointwise bound at `0`.
  have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
  -- For every `c > C`, both `±c⁻¹ ω` are mass-admissible for `W`, hence `|T ω| ≤ B c`.
  have key : ∀ c, C < c → |T ω| ≤ B * c := by
    intro c hc
    have hc0 : 0 < c := hC0.trans_lt hc
    have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * T ω ≤ B := by
      intro s hs
      have hadm : s • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hW, fun x => ?_⟩
        change covectorEuclideanNorm (s • (ω : DifferentialForm (Eucl P) n) x) ≤ 1
        rw [hsmul, hs, inv_mul_le_iff₀ hc0, mul_one]
        exact (hC x).trans hc.le
      have hle := (T.le_massOn hadm).trans hM
      rw [ENNReal.ofReal_le_ofReal_iff hB] at hle
      have hlin : T (s • ω) = s * T ω := by
        rw [map_smul, smul_eq_mul]
      rwa [hlin] at hle
    have h1 := hbound c⁻¹ (abs_of_pos (inv_pos.mpr hc0))
    have h2 := hbound (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc0)])
    have e1 : c * (c⁻¹ * T ω) = T ω := by field_simp
    have e2 : c * (-c⁻¹ * T ω) = -T ω := by field_simp
    rw [abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left h2 hc0.le
      rw [e2] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h1 hc0.le
      rw [e1] at this
      linarith
  -- Let `c ↓ C`: take `c = C + ε / (B + 1)`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < ε / (B + 1) := div_pos hε hB1
  have hBδ : B * (ε / (B + 1)) ≤ ε := by
    calc B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := by field_simp
  have := key (C + ε / (B + 1)) (by linarith)
  calc |T ω| ≤ B * (C + ε / (B + 1)) := this
    _ = B * C + B * (ε / (B + 1)) := by ring
    _ ≤ B * C + ε := by linarith
/-- **Mollification step of Simon Ch. 6, Lemma 2.15 (p. 137).**  A continuous compactly supported
`n`-form `ω` with `tsupport ω ⊆ V`, `V` open, is a uniform limit, in the Euclidean coefficient
norm, of test forms supported in `V`.  As `|α| ≤ √N ‖α‖` (`N = #(Fin n → Fin P)`, `‖α‖` the
operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ ω)`: `ψ ⋆ ω`
is the convolution of `ω` with a normalized smooth bump `ψ` supported in a ball whose radius is
a uniform-continuity modulus of `ω`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to
`1` exactly on `tsupport ω`, whose support `V'` has compact closure in `V`. -/
theorem Submission.cmb_exists_testForm_uniform_approx : ∀ (P n : ℕ) (U V : Set (Eucl P)) (ω : Eucl P → Covector (Eucl P) n), IsOpen V → V ⊆ U → Continuous ω → HasCompactSupport ω → tsupport ω ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U n, tsupport (η : DifferentialForm (Eucl P) n) ⊆ V ∧ ∀ x, covectorEuclideanNorm (ω x - (η : DifferentialForm (Eucl P) n) x) ≤ ε := by
  intro P n U V ω hV hVU hω hωc hωV ε hε
  -- Step 1: `|α| ≤ √N ‖α‖`, since every coefficient satisfies `|α(e_I)| ≤ ‖α‖ ∏ ‖e_{I j}‖ = ‖α‖`.
  set N : ℝ := Real.sqrt (Fintype.card (Fin n → Fin P)) with hN_def
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hcmp : ∀ α : Covector (Eucl P) n, covectorEuclideanNorm α ≤ N * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hN_def, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin n → Fin P,
          (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
        ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg α)] using h)
          · positivity
      _ = (Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  have hN1 : 0 < N + 1 := by linarith
  set ε' : ℝ := ε / (N + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε hN1
  -- Step 2: an open `V'` with `tsupport ω ⊆ V'` and `closure V' ⊆ V` compact.
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ :=
    exists_open_between_and_isCompact_closure hωc.isCompact hV hωV
  -- Step 3: a smooth cutoff `χ : ℝ^P → [0, 1]` with `support χ = V'` and `χ = 1` exactly on
  -- `tsupport ω`.
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV'o (isClosed_tsupport ω) hKV'
  -- Step 4: mollification.  `ω` is uniformly continuous with modulus `δ` at accuracy `ε'`; `ψ` is
  -- a smooth bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `g = ψ ⋆ ω` is smooth and
  -- `dist (g x) (ω x) ≤ ε'`.
  obtain ⟨δ, hδ, hωδ⟩ :=
    Metric.uniformContinuous_iff.mp (hωc.uniformContinuous_of_continuous hω) ε' hε'
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
  obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → Covector (Eucl P) n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (ω x) ≤ ε' :=
    ⟨convolution ψ ω (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      hψc.contDiff_convolution_left _ hψd hω.locallyIntegrable,
      fun x => dist_convolution_le hε'.le hψs hψnn hψ1 hω.aestronglyMeasurable
        fun y hy => (hωδ (mem_ball.mp hy)).le⟩
  -- Step 5: `η = χ • g` is a test form with `tsupport η ⊆ closure V' ⊆ V ⊆ U`.
  have hη_supp : tsupport (fun x => χ x • g x) ⊆ closure V' := by
    refine (tsupport_smul_subset_left χ g).trans ?_
    rw [tsupport, hχs]
  have hη_cpt : HasCompactSupport (fun x => χ x • g x) :=
    hV'c.of_isClosed_subset (isClosed_tsupport _) hη_supp
  refine ⟨⟨fun x => χ x • g x, ⟨⟨hχ.smul hg, hη_cpt⟩, hη_supp.trans (hV'V.trans hVU)⟩⟩,
    hη_supp.trans hV'V, fun x => ?_⟩
  -- Step 6: `‖ω x - η x‖ ≤ ε'` (on `tsupport ω`, `η = g`; off it, `ω = 0` and `0 ≤ χ ≤ 1`),
  -- hence `|ω x - η x| ≤ √N ε' ≤ ε`.
  have hle : ‖ω x - χ x • g x‖ ≤ ε' := by
    by_cases hx : x ∈ tsupport ω
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : ω x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε' := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  calc covectorEuclideanNorm (ω x - χ x • g x) ≤ N * ‖ω x - χ x • g x‖ := hcmp _
    _ ≤ N * ε' := mul_le_mul_of_nonneg_left hle hN
    _ ≤ ε := by
      rw [hε'_def, mul_div_assoc', div_le_iff₀ hN1]
      nlinarith
/-- Coordinate expansion of an `n`-covector on `ℝ^P` in the wedge basis:
`α = ∑_β α(e_{β(0)}, …, e_{β(n-1)}) dx^β` over the increasing multi-indices `β`. -/
theorem Submission.cmb_covector_eq_sum_coord_smul_wedge :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n), α = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) := by
  intro P n α
  classical
  -- `e v = (e_{v 0}, …, e_{v (n - 1)})` for a tuple `v` of coordinate indices.
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1
  set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
    euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) with hR
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P,
      wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · -- the matrix `[δ_{β i, β j}]` is the identity
      subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · -- some `β i` is not among the `γ j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
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
  -- `R` agrees with `α` on increasing tuples of basis vectors.
  have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
    intro γ
    rw [hR, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  -- `R` agrees with `α` on injective tuples: sort them and use `map_perm`.
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
  -- Conclude by extensionality on the standard basis.
  symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  exact h2 v hv

/-- **Continuous forms against a measure representation: the step "by (2.7)" in the proof of
Simon Ch. 6, Lemma 2.15 (p. 137).**  Let `(μ, v)` represent `T` as in (2.7), `W ⊂⊂ U` and
`M_W(T) ≤ B`.  If `ω` is a continuous `n`-form with `tsupport ω ⊆ W` and `|ω(x)| ≤ C` everywhere
(Euclidean coefficient norm), then `⟨ω, v⟩` is `μ`-integrable and `|∫ ⟨ω, v⟩ dμ| ≤ B · C`.
Choose `V` open with `tsupport ω ⊆ V` and `closure V ⊆ W` compact.  The coefficients `v_β` of `v`
are `μ`-integrable on `closure V`, so for every continuous `θ` vanishing off `closure V` with
`|θ| ≤ D`, `⟨θ, v⟩ = ∑_β θ(e_β) v_β` is integrable and `|∫ ⟨θ, v⟩ dμ| ≤ D · G`, where
`G = ∑_β ∫_{closure V} |v_β| dμ`.  For a test form `η` supported in `V` with `|ω - η| ≤ ε`, the
mass bound gives `|∫ ⟨ω, v⟩ dμ| ≤ |T(η)| + ε G ≤ B (C + ε) + ε G`; let `ε → 0`. -/
theorem Submission.cmb_measureRepresentation_continuous_bound : ∀ (P n : ℕ) (U W : Set (Eucl P)), CompactlyContainedOpen W U → ∀ (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → ∀ (B C : ℝ), 0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → tsupport ω ⊆ W → (∀ x, covectorEuclideanNorm (ω x) ≤ C) → Integrable (fun x => v x (ω x)) μ ∧ |∫ x, v x (ω x) ∂μ| ≤ B * C := by
  intro P n U W hWU T μ v hT B C hB hM ω hω hωW hωC
  obtain ⟨hWo, hWc, hWU'⟩ := hWU
  have hWU₀ : W ⊆ U := subset_closure.trans hWU'
  -- Step 1: `tsupport ω` is compact; choose `V` open with `tsupport ω ⊆ V`, `closure V ⊆ W`
  -- compact.
  have hωc : HasCompactSupport ω :=
    hWc.of_isClosed_subset (isClosed_tsupport ω) (hωW.trans subset_closure)
  obtain ⟨V, hVo, hωV, hVW, hVc⟩ :=
    exists_open_between_and_isCompact_closure hωc.isCompact hWo hωW
  have hVU : V ⊆ U := subset_closure.trans (hVW.trans hWU₀)
  -- Step 2: the coefficients `v_β` of `v` are `μ`-integrable on `closure V`.
  have hcoef : ∀ β : SimonMultiIndex n P,
      IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) (closure V) μ :=
    Submission.cmb_rb_measureRepresentation_integrableOn_coeff P n U W hWo hWU₀ T μ v hT
      (closure V) hVc hVW
  set G : ℝ := ∑ β : SimonMultiIndex n P,
    ∫ x in closure V, |euclideanNVectorCoordinate (v x) β| ∂μ
  have hG : 0 ≤ G := Finset.sum_nonneg fun β _ => integral_nonneg fun x => abs_nonneg _
  -- Step 3: coordinate expansion `v(x)(α) = ∑_β α(e_β) v_β(x)`.
  have hexp : ∀ (x : Eucl P) (α : Covector (Eucl P) n), v x α = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β * euclideanNVectorCoordinate (v x) β := by
    intro x α
    conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P n α]
    simp only [map_sum, map_smul, smul_eq_mul, euclideanNVectorCoordinate]
  -- Step 4: pairings with continuous forms vanishing off `closure V` are integrable, and
  -- `|∫ ⟨θ, v⟩ dμ| ≤ D G` when `|θ| ≤ D`.
  have hpair : ∀ (θ : Eucl P → Covector (Eucl P) n) (D : ℝ), Continuous θ →
      (∀ x, x ∉ closure V → θ x = 0) → (∀ x, covectorEuclideanNorm (θ x) ≤ D) →
      Integrable (fun x => v x (θ x)) μ ∧ |∫ x, v x (θ x) ∂μ| ≤ D * G := by
    intro θ D hθ hθV hθD
    have hfun : (fun x => v x (θ x)) = fun x => ∑ β : SimonMultiIndex n P,
        euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β :=
      funext fun x => hexp x (θ x)
    rw [hfun]
    exact Submission.cmb_rb_integral_coeff_pairing_bound P n μ v (closure V)
      isClosed_closure.measurableSet hcoef θ D hθ hθV hθD
  have hωV' : ∀ x, x ∉ closure V → ω x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hωV h))
  refine ⟨(hpair ω C hω hωV' hωC).1, ?_⟩
  -- Step 5: compare with a test form `η` supported in `V`, `|ω - η| ≤ ε`.
  have key : ∀ ε : ℝ, 0 < ε → |∫ x, v x (ω x) ∂μ| ≤ B * (C + ε) + ε * G := by
    intro ε hε
    obtain ⟨η, hηV, hηω⟩ :=
      Submission.cmb_exists_testForm_uniform_approx P n U V ω hVo hVU hω hωc hωV ε hε
    -- `|η| ≤ C + ε`, hence `|T(η)| ≤ B (C + ε)` by the mass bound.
    have hηC : ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ C + ε := by
      intro x
      have h := Submission.cmb_rb_covectorEuclideanNorm_add_le P n (ω x)
        (-(ω x - (η : DifferentialForm (Eucl P) n) x))
      have heq : ω x + -(ω x - (η : DifferentialForm (Eucl P) n) x) =
          (η : DifferentialForm (Eucl P) n) x := by abel
      rw [heq, covectorEuclideanNorm_neg] at h
      linarith [hωC x, hηω x]
    have hTη : |T η| ≤ B * (C + ε) :=
      Submission.cmb_abs_apply_le_of_massOn_le P n U W T η B (C + ε) hB hM
        (hηV.trans (subset_closure.trans hVW)) hηC
    -- `θ = ω - η` is continuous, vanishes off `closure V` and `|θ| ≤ ε`.
    have hηc : Continuous (η : DifferentialForm (Eucl P) n) := ContDiff.continuous η.property.1.1
    have hθV : ∀ x, x ∉ closure V → ω x - (η : DifferentialForm (Eucl P) n) x = 0 := by
      intro x hx
      rw [hωV' x hx, image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hηV h)),
        sub_zero]
    obtain ⟨hθi, hθb⟩ :
        Integrable (fun x => v x (ω x - (η : DifferentialForm (Eucl P) n) x)) μ ∧
          |∫ x, v x (ω x - (η : DifferentialForm (Eucl P) n) x) ∂μ| ≤ ε * G :=
      hpair (fun x => ω x - (η : DifferentialForm (Eucl P) n) x) ε (hω.sub hηc) hθV hηω
    -- `∫ ⟨ω, v⟩ dμ = T(η) + ∫ ⟨ω - η, v⟩ dμ`.
    obtain ⟨hηi, hηT⟩ := hT η
    have hsplit : ∫ x, v x (ω x) ∂μ =
        T η + ∫ x, v x (ω x - (η : DifferentialForm (Eucl P) n) x) ∂μ := by
      rw [hηT, ← integral_add hηi hθi]
      congr 1
      funext x
      rw [← map_add, add_sub_cancel]
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hTη hθb)
  -- Step 6: let `ε → 0`, with `ε = ε₀ / (B + G + 1)`.
  refine le_of_forall_pos_le_add fun ε₀ hε₀ => ?_
  have hBG : 0 < B + G + 1 := by linarith
  have hε : 0 < ε₀ / (B + G + 1) := div_pos hε₀ hBG
  have hεε₀ : ε₀ / (B + G + 1) * (B + G + 1) = ε₀ := div_mul_cancel₀ ε₀ hBG.ne'
  have h := key _ hε
  nlinarith
/-- The coordinate wedge covectors are dual to the increasing basis tuples: the `J`-th coordinate
of `∑_I c_I dx^I` is `c_J`, i.e. `dx^I(e_{J(0)}, …, e_{J(k-1)}) = δ_{IJ}`. -/
theorem Submission.smr_ci_coord_sum_smul_wedge :
    ∀ (P k : ℕ) (c : SimonMultiIndex k P → ℝ) (J : SimonMultiIndex k P),
      euclideanCovectorCoordinate (∑ I : SimonMultiIndex k P,
        c I • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)) : Covector (Eucl P) k) J = c J := by
  intro P k c J
  classical
  -- Kronecker property: `dx^I (e_J) = δ_{IJ}`.
  have hK : ∀ I : SimonMultiIndex k P, wedgeCovectors k (fun j => EuclideanSpace.proj (I j))
      (fun j => EuclideanSpace.single (J j) (1 : ℝ)) = if I = J then 1 else 0 := by
    intro I
    rw [wedgeCovectors_apply_det]
    split_ifs with hIJ
    · -- the matrix `[δ_{I i, I j}]` is the identity
      subst hIJ
      convert Matrix.det_one (n := Fin k) (R := ℝ)
      ext i j
      simp [Matrix.one_apply, PiLp.single_apply, I.injective.eq_iff]
    · -- some `I i` is not among the `J j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra! h
        apply hIJ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range I ⊆ Set.range J := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range J)
        rw [Set.ncard_range_of_injective J.injective, Set.ncard_range_of_injective I.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  -- Evaluation at `e_J` is linear, so only the term `I = J` survives.
  rw [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
/-- The Euclidean coefficient norm of a `k`-covector on `ℝ^P` is the `ℓ²`-norm of its coordinates
`α(e_{I(0)}, …, e_{I(k-1)})` over the increasing multi-indices `I : Fin k ↪o Fin P`. -/
theorem Submission.smr_ci_norm_eq_sqrt_sum_coord_sq :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k), covectorEuclideanNorm α =
      Real.sqrt (∑ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I ^ 2) := by
  intro P k α
  unfold covectorEuclideanNorm
  congr 1
  -- Drop the tuples that are not strictly increasing; their terms vanish.
  rw [← Finset.sum_filter]
  -- Reindex the strictly increasing tuples by the order embeddings, `I ↦ ⇑I`.
  symm
  refine Finset.sum_bij' (fun I _ => ⇑I)
    (fun f hf => OrderEmbedding.ofStrictMono f (Finset.mem_filter.1 hf).2)
    (fun I _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, I.strictMono⟩)
    (fun _ _ => Finset.mem_univ _) (fun I _ => ?_) (fun f _ => ?_) (fun I _ => ?_)
  · exact RelEmbedding.ext fun _ => rfl
  · exact OrderEmbedding.coe_ofStrictMono _
  · -- Matching summands: `basisFun i = EuclideanSpace.single i 1`.
    simp only [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]
/-- **`L¹` density of continuous compactly supported maps for a finite measure on `ℝ^N`.**  For a
finite Borel measure `ν` on `ℝ^N` and `f ∈ L¹(ν)` with values in a real normed space `E`, every
`ε ≠ 0` admits a continuous compactly supported `g ∈ L¹(ν)` with `‖f - g‖_{L¹(ν)} ≤ ε` (the case
`p = 1` of Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, whose file is not imported
here; its proof is reproduced).  Urysohn's lemma and outer regularity approximate `c • 1_s` (`s`
closed, `s ⊆ u` open, `ν s < ∞`) by a continuous `L¹` map supported in `u`; inner regularity by
compact closed sets treats `c • 1_t` for measurable `t` with `ν t < ∞`; and `MemLp.induction_dense`
(density of simple functions) extends this to all of `L¹(ν)`, the class being closed under `+`. -/
theorem Submission.imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le : ∀ (N : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure (Eucl N)) [IsFiniteMeasure ν] (f : Eucl N → E), MemLp f 1 ν → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ g : Eucl N → E, HasCompactSupport g ∧ eLpNorm (f - g) 1 ν ≤ ε ∧ Continuous g ∧ MemLp g 1 ν := by
  intro N E _ _ ν _ f hf ε hε
  -- Urysohn approximation of `c • 1_s` for `s` closed, `s ⊆ u` open, `ν s < ∞` (Mathlib's
  -- `exists_continuous_eLpNorm_sub_le_of_closed` with `p = 1`).
  have hury : ∀ {s u : Set (Eucl N)}, IsClosed s → IsOpen u → s ⊆ u → ν s ≠ ∞ →
      ∀ (c : E) {δ : ℝ≥0∞}, δ ≠ 0 → ∃ h : Eucl N → E,
        Continuous h ∧ eLpNorm (fun x => h x - s.indicator (fun _y => c) x) 1 ν ≤ δ ∧
          (∀ x, ‖h x‖ ≤ ‖c‖) ∧ Function.support h ⊆ u ∧ MemLp h 1 ν := by
    intro s u s_closed u_open hsu hs c δ hδ
    -- `‖c • 1_r‖₁ ≤ δ` whenever `ν r ≤ η`.
    obtain ⟨η, η_pos, hη⟩ :
        ∃ η : ℝ≥0, 0 < η ∧ ∀ r : Set (Eucl N), ν r ≤ η → NullMeasurableSet r ν →
            eLpNorm (r.indicator fun _x => c) 1 ν ≤ δ :=
      exists_eLpNorm_indicator_le ENNReal.one_ne_top c hδ
    have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
    -- Outer regularity: an open `V ⊇ s` with `ν (V \ s) < η`.
    obtain ⟨V, sV, V_open, h'V, hV⟩ :
        ∃ (V : Set (Eucl N)), V ⊇ s ∧ IsOpen V ∧ ν V < ∞ ∧ ν (V \ s) < η :=
      s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
    let v := u ∩ V
    have hsv : s ⊆ v := subset_inter hsu sV
    have hνv : ν v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
    -- Urysohn's lemma: `φ = 0` off `v`, `φ = 1` on `s`, `0 ≤ φ ≤ 1`.
    obtain ⟨φ, hφv, hφs, hφ_range⟩ :=
      exists_continuous_zero_one_of_isClosed (u_open.inter V_open).isClosed_compl s_closed
        (disjoint_compl_left_iff.2 hsv)
    have φ_norm : ∀ x, ‖φ x‖ = φ x := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ_range x).1]
    have φc_bd0 : ∀ x, ‖φ x • c‖ ≤ ‖c‖ := by
      intro x
      simp only [norm_smul, φ_norm x]
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact (hφ_range x).2
    -- Pointwise `‖φ c - c 1_s‖ ≤ ‖c 1_{v \ s}‖`.
    have φc_bd :
        ∀ x, ‖φ x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
      intro x
      by_cases hv : x ∈ v
      · rw [← Set.sdiff_union_of_subset hsv] at hv
        rcases hv with hxvs | hxs
        · simpa only [hxvs.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hxvs,
            Set.indicator_of_mem] using φc_bd0 x
        · simp [hφs hxs, hxs]
      · simp [hφv hv, show x ∉ s from fun h => hv (hsv h)]
    have φc_support : (Function.support fun x : Eucl N => φ x • c) ⊆ v := by
      refine Function.support_subset_iff'.2 fun x hx => ?_
      simp only [hφv hx, Pi.zero_apply, zero_smul]
    -- `φ c ∈ L¹(ν)`: `φ ≤ 1_v` and `ν v < ∞`.
    have φc_mem : MemLp (fun x => φ x • c) 1 ν := by
      refine MemLp.smul ?_ (memLp_top_const (μ := ν) c) (p := 1) (q := ∞) (r := 1)
      have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
      have : eLpNorm (v.indicator fun _x => (1 : ℝ)) 1 ν < ∞ :=
        (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
          simp [lt_top_iff_ne_top, hνv.ne]
      refine (eLpNorm_mono φ.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
      by_cases hx : x ∈ v
      · simp only [hx, abs_of_nonneg (hφ_range x).1, (hφ_range x).2, Real.norm_eq_abs,
          indicator_of_mem, CStarRing.norm_one]
      · simp only [hφv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
    refine ⟨fun x ↦ φ x • c, by fun_prop,
      (eLpNorm_mono (φc_mem.aestronglyMeasurable.sub
        (aestronglyMeasurable_const.indicator s_closed.measurableSet)) φc_bd).trans ?_, φc_bd0,
        φc_support.trans inter_subset_left, φc_mem⟩
    exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
      ((u_open.measurableSet.inter V_open.measurableSet).diff
        s_closed.measurableSet).nullMeasurableSet
  suffices hex : ∃ g : Eucl N → E,
      eLpNorm (f - g) 1 ν ≤ ε ∧ Continuous g ∧ MemLp g 1 ν ∧ HasCompactSupport g by
    rcases hex with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  -- Density of simple functions: approximate indicator-constants, and close under addition.
  apply hf.induction_dense ENNReal.one_ne_top _ _ _ hε
  rotate_left
  · rintro g₁ g₂ ⟨g₁_cont, g₁_mem, hg₁⟩ ⟨g₂_cont, g₂_mem, hg₂⟩
    exact ⟨g₁_cont.add g₂_cont, g₁_mem.add g₂_mem, hg₁.add hg₂⟩
  intro c t ht htν δ hδ
  rcases exists_Lp_half E ν 1 hδ with ⟨δ', δ'pos, hδ'⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ r : Set (Eucl N), ν r ≤ η → NullMeasurableSet r ν →
          eLpNorm (r.indicator fun _x => c) 1 ν ≤ δ' :=
    exists_eLpNorm_indicator_le ENNReal.one_ne_top c δ'pos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  -- Inner regularity: a compact closed `s ⊆ t` with `ν (t \ s) < η`.
  obtain ⟨s, st, s_compact, s_closed, νs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ ν (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htν.ne hη_pos'.ne'
  have hsν : ν s < ∞ := (measure_mono st).trans_lt htν
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) 1 ν ≤ δ' := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ νs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  -- A compact `k` with `s ⊆ interior k`, and the Urysohn approximation for `(s, interior k)`.
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set (Eucl N), IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases hury s_closed isOpen_interior sk hsν.ne c δ'pos.ne'
    with ⟨h, h_cont, I2, _h_bound, h_support, h_mem⟩
  have I3 : eLpNorm (h - t.indicator fun _y => c) 1 ν ≤ δ := by
    convert (hδ' _ _ I2 I1).le using 2
    ext x
    simp
  refine ⟨h, I3, h_cont, h_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (h_support hx)

/-- **Polar field (Simon Ch. 6, 2.7–2.8; Steps 3, 5 and 6 of the mass lower bound).**  If `g` is
`μ`-integrable on `B = B_R(0)` with values in a real inner product space, then for every `ε > 0`
there is a continuous `F` with `tsupport F ⊆ B` and `‖F‖ ≤ 1` such that `⟨F, g⟩` is
`μ`-integrable and `∫_B ‖g‖ dμ ≤ ∫ ⟨F, g⟩ dμ + ε`.  With `ρ = ‖g‖`, the polar field `u = g / ρ`
and the finite measure `ν = ρ μ⌞B`, approximate `u` in `L¹(ν)` by a continuous compactly
supported `g₀` (sibling `l1_density`) and take `F = χ · π(g₀)`, where `χ` cuts off near `∂B` and
`π(a) = a / max(1, ‖a‖)` is the radial retraction onto the closed unit ball. -/
theorem Submission.imc_mlb_exists_unit_field_integral_ge : ∀ (N : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure (Eucl N)) (R : ℝ) (g : Eucl N → E), IntegrableOn g (ball (0 : Eucl N) R) μ → ∀ ε : ℝ, 0 < ε → ∃ F : Eucl N → E, Continuous F ∧ tsupport F ⊆ ball (0 : Eucl N) R ∧ (∀ x, ‖F x‖ ≤ 1) ∧ Integrable (fun x => inner ℝ (F x) (g x)) μ ∧ ∫ x in ball (0 : Eucl N) R, ‖g x‖ ∂μ ≤ ∫ x, inner ℝ (F x) (g x) ∂μ + ε := by
  intro N E _ _ μ R g hg ε hε
  -- Step 0: a continuous `F` with `‖F‖ ≤ 1` vanishing off `B` pairs integrably with `g`, and
  -- `∫ ⟨F, g⟩ dμ = ∫_B ⟨F, g⟩ dμ`.
  have hpair : ∀ F : Eucl N → E, Continuous F → tsupport F ⊆ ball (0 : Eucl N) R →
      (∀ x, ‖F x‖ ≤ 1) → Integrable (fun x => inner ℝ (F x) (g x)) μ ∧
        ∫ x, inner ℝ (F x) (g x) ∂μ = ∫ x in ball (0 : Eucl N) R, inner ℝ (F x) (g x) ∂μ := by
    intro F hFc hFs hF1
    have hzero : ∀ x, x ∉ ball (0 : Eucl N) R → inner ℝ (F x) (g x) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (hFs h), inner_zero_left]
    have hint : IntegrableOn (fun x => inner ℝ (F x) (g x)) (ball (0 : Eucl N) R) μ :=
      (Integrable.norm hg).mono' (continuous_inner.comp_aestronglyMeasurable
        (hFc.aestronglyMeasurable.prodMk hg.aestronglyMeasurable))
        (Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hF1 x)))
    exact ⟨(integrableOn_iff_integrable_of_support_subset fun x hx =>
      not_not.mp fun h => hx (hzero x h)).mp hint,
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm⟩
  -- Step 1: if `R ≤ 0` then `B = ∅` and `F = 0` works.
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨0, continuous_const, by rw [tsupport_zero]; exact empty_subset _, fun x => by simp,
      by simp, ?_⟩
    rw [ball_eq_empty.mpr hR]
    simp [hε.le]
  -- Step 2: a strongly measurable `g' = g` `μ⌞B`-a.e.; `ρ = ‖g'‖` and `u = ρ⁻¹ g'`, so that
  -- `‖u‖ ≤ 1`, `‖u‖ = 1` where `g' ≠ 0`, and `g' = ρ u`.
  obtain ⟨g', hg'm, hgg'⟩ := hg.aestronglyMeasurable
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Eucl N → ℝ, ρ = fun x => ‖g' x‖ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Eucl N → E, u = fun x => (ρ x)⁻¹ • g' x := ⟨_, rfl⟩
  have hρx : ∀ x, ρ x = ‖g' x‖ := fun x => by rw [hρ]
  have hux : ∀ x, u x = (ρ x)⁻¹ • g' x := fun x => by rw [hu]
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => by rw [hρx]; exact norm_nonneg _
  have hρm : StronglyMeasurable ρ := by rw [hρ]; exact hg'm.norm
  have hum : StronglyMeasurable u := by
    rw [hu]; exact hρm.measurable.inv.stronglyMeasurable.smul hg'm
  have hgρu : ∀ x, g' x = ρ x • u x := by
    intro x
    rw [hux, smul_smul]
    rcases eq_or_ne (g' x) 0 with h | h
    · rw [h, smul_zero]
    · rw [mul_inv_cancel₀ (by rw [hρx]; exact norm_ne_zero_iff.mpr h), one_smul]
  have hu1 : ∀ x, ‖u x‖ ≤ 1 := by
    intro x
    rw [hux, norm_smul, norm_inv, Real.norm_of_nonneg (hρ0 x), hρx]
    rcases eq_or_ne ‖g' x‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hu1' : ∀ x, g' x ≠ 0 → ‖u x‖ = 1 := by
    intro x hx
    rw [hux, norm_smul, norm_inv, Real.norm_of_nonneg (hρ0 x), hρx,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hgρ : (fun x => ‖g x‖) =ᵐ[μ.restrict (ball (0 : Eucl N) R)] ρ :=
    hgg'.mono fun x hx => by simp only [hρx, hx]
  have hρi : Integrable ρ (μ.restrict (ball (0 : Eucl N) R)) := (Integrable.norm hg).congr hgρ
  have hρ_eq : ∫ x in ball (0 : Eucl N) R, ‖g x‖ ∂μ = ∫ x in ball (0 : Eucl N) R, ρ x ∂μ :=
    integral_congr_ae hgρ
  -- Step 3: the finite measure `ν = ρ μ⌞B`, with `ν(S) = ∫_S ρ dμ` for measurable `S ⊆ B`;
  -- `u ∈ L¹(ν)`.
  have hρmeas : Measurable fun x => ENNReal.ofReal (ρ x) := hρm.measurable.ennreal_ofReal
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Eucl N),
      ν = (μ.restrict (ball (0 : Eucl N) R)).withDensity fun x => ENNReal.ofReal (ρ x) :=
    ⟨_, rfl⟩
  have : IsFiniteMeasure ν := by
    rw [hν]
    refine isFiniteMeasure_withDensity ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0)]
    exact ENNReal.ofReal_ne_top
  have hνS : ∀ S, MeasurableSet S → S ⊆ ball (0 : Eucl N) R →
      ν S = ENNReal.ofReal (∫ x in S, ρ x ∂μ) := by
    intro S hS hSB
    rw [hν, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSB,
      ofReal_integral_eq_lintegral_ofReal (IntegrableOn.mono_set hρi hSB)
        (Eventually.of_forall hρ0)]
  have huL1 : MemLp u 1 ν := MemLp.of_bound hum.aestronglyMeasurable 1 (Eventually.of_forall hu1)
  -- Step 4: continuity from above of `ν` gives `0 < R' < R` with `ν(B ∖ B̄_{R'}) < ε/4`.
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  obtain ⟨R', hR'0, hR'R, hνR'⟩ : ∃ R', 0 < R' ∧ R' < R ∧
      ν (ball (0 : Eucl N) R \ closedBall 0 R') < ENNReal.ofReal (ε / 4) := by
    have hanti : Antitone fun n : ℕ => ball (0 : Eucl N) R \ closedBall 0 (R - R / (n + 2)) := by
      intro m n hmn
      refine sdiff_subset_sdiff_right (closedBall_subset_closedBall ?_)
      have : R / (n + 2) ≤ R / (m + 2) := div_le_div_of_nonneg_left hR.le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hmn 2)
      linarith
    have hempty : (⋂ n : ℕ, ball (0 : Eucl N) R \ closedBall 0 (R - R / (n + 2))) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      rw [mem_iInter] at hx
      have hxR : ‖x‖ < R := mem_ball_zero_iff.mp (hx 0).1
      obtain ⟨n, hn⟩ := exists_nat_gt (R / (R - ‖x‖))
      have hpos : 0 < R - ‖x‖ := sub_pos.mpr hxR
      have hlt : R / (n + 2) < R - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      exact (hx n).2 (mem_closedBall_zero_iff.mpr (by linarith))
    have htend := tendsto_measure_iInter_atTop (μ := ν)
      (fun n => (measurableSet_ball.diff measurableSet_closedBall).nullMeasurableSet) hanti
      ⟨0, measure_ne_top ν _⟩
    rw [hempty, measure_empty] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε4))).exists
    refine ⟨R - R / (n + 2), ?_, ?_, hn⟩
    · have : R / (n + 2) < R := div_lt_self hR (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      linarith
    · have : 0 < R / (n + 2) := by positivity
      linarith
  -- Step 5 (sibling `l1_density`): a continuous compactly supported `g₀` with
  -- `∫⁻_B ρ ‖g₀ - u‖ dμ = ‖u - g₀‖_{L¹(ν)} ≤ ε/4`; `g₀` is bounded.
  obtain ⟨g₀, hg₀s, hg₀L1, hg₀c, -⟩ :=
    Submission.imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le N E ν u huL1
      (ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.mpr hε4).ne'
  obtain ⟨C₀, hC₀⟩ := hg₀c.bounded_above_of_compact_support hg₀s
  have h51 : ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (ρ x * ‖g₀ x - u x‖) ∂μ ≤
      ENNReal.ofReal (ε / 4) :=
    calc ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (ρ x * ‖g₀ x - u x‖) ∂μ
        = ∫⁻ x in ball (0 : Eucl N) R,
            ((fun x => ENNReal.ofReal (ρ x)) * fun x => ‖(u - g₀) x‖ₑ) x ∂μ := by
          refine lintegral_congr fun x => ?_
          show ENNReal.ofReal (ρ x * ‖g₀ x - u x‖) = ENNReal.ofReal (ρ x) * ‖u x - g₀ x‖ₑ
          rw [ENNReal.ofReal_mul (hρ0 x), ofReal_norm, enorm_sub_rev]
      _ = ∫⁻ x, ‖(u - g₀) x‖ₑ ∂ν := by
          rw [hν, lintegral_withDensity_eq_lintegral_mul _ hρmeas
            (hum.sub hg₀c.stronglyMeasurable).enorm]
      _ ≤ eLpNorm (u - g₀) 1 ν := lintegral_enorm_le_eLpNorm_one
      _ ≤ ENNReal.ofReal (ε / 4) := hg₀L1
  -- Step 6: the cut-off `χ`, equal to `1` on `B̄_{R'}` and to `0` off `B_{R''}`,
  -- `R'' = (R + R')/2`; `tsupport χ ⊆ B̄_{R''} ⊆ B`.
  obtain ⟨R'', hR''⟩ : ∃ R'' : ℝ, R'' = (R + R') / 2 := ⟨_, rfl⟩
  have hR'R'' : R' < R'' := by rw [hR'']; linarith
  have hR''R : R'' < R := by rw [hR'']; linarith
  obtain ⟨χ, hχ⟩ : ∃ χ : Eucl N → ℝ, χ = fun x => min 1 (max 0 ((R'' - ‖x‖) / (R'' - R'))) :=
    ⟨_, rfl⟩
  have hχx : ∀ x, χ x = min 1 (max 0 ((R'' - ‖x‖) / (R'' - R'))) := fun x => by rw [hχ]
  have hχc : Continuous χ := by
    rw [hχ]
    exact continuous_const.min (continuous_const.max
      ((continuous_const.sub continuous_norm).div_const _))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => by rw [hχx]; exact le_min zero_le_one (le_max_left _ _)
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => by rw [hχx]; exact min_le_left _ _
  have hχin : ∀ x, ‖x‖ ≤ R' → χ x = 1 := by
    intro x hx
    rw [hχx, min_eq_left]
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hχout : ∀ x, R'' ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    rw [hχx, max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)),
      min_eq_right zero_le_one]
  have hχs : tsupport χ ⊆ ball (0 : Eucl N) R := by
    have hsupp : Function.support χ ⊆ ball (0 : Eucl N) R'' := fun x hx =>
      mem_ball_zero_iff.mpr (not_le.mp fun h => hx (hχout x h))
    exact (closure_mono hsupp).trans
      (closure_ball_subset_closedBall.trans (closedBall_subset_ball hR''R))
  -- Step 7: the radial retraction `pr a = a / max(1, ‖a‖)`: continuous, `‖pr a‖ ≤ 1`, and
  -- `‖pr a - b‖ ≤ 2 ‖a - b‖` whenever `‖b‖ ≤ 1`.
  have hmax : ∀ a : E, 0 < max 1 ‖a‖ := fun a => zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨pr, hpr⟩ : ∃ pr : E → E, pr = fun a => (max 1 ‖a‖)⁻¹ • a := ⟨_, rfl⟩
  have hprx : ∀ a, pr a = (max 1 ‖a‖)⁻¹ • a := fun a => by rw [hpr]
  have hprc : Continuous pr := by
    rw [hpr]
    exact ((continuous_const.max continuous_norm).inv₀ fun a => (hmax a).ne').smul continuous_id
  have hpr1 : ∀ a, ‖pr a‖ ≤ 1 := by
    intro a
    rw [hprx, norm_smul, norm_inv, Real.norm_of_nonneg (hmax a).le, inv_mul_le_iff₀ (hmax a),
      mul_one]
    exact le_max_right _ _
  have hpr2 : ∀ a b : E, ‖b‖ ≤ 1 → ‖pr a - b‖ ≤ 2 * ‖a - b‖ := by
    intro a b hb
    rcases le_or_gt ‖a‖ 1 with ha | ha
    · rw [hprx, max_eq_left ha, inv_one, one_smul]
      linarith [norm_nonneg (a - b)]
    · have ha0 : 0 < ‖a‖ := zero_lt_one.trans ha
      have h1 : ‖pr a - a‖ = ‖a‖ - 1 := by
        rw [hprx, max_eq_right ha.le,
          show ‖a‖⁻¹ • a - a = (‖a‖⁻¹ - 1) • a by rw [sub_smul, one_smul], norm_smul,
          Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (inv_le_one_of_one_le₀ ha.le)),
          neg_sub, sub_mul, one_mul, inv_mul_cancel₀ ha0.ne']
      have h2 : ‖a‖ - 1 ≤ ‖a - b‖ := by linarith [norm_sub_norm_le a b]
      calc ‖pr a - b‖ = ‖(pr a - a) + (a - b)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖pr a - a‖ + ‖a - b‖ := norm_add_le _ _
        _ ≤ 2 * ‖a - b‖ := by linarith
  -- Step 8: the competitor `F = χ · pr ∘ g₀`.
  obtain ⟨F, hF⟩ : ∃ F : Eucl N → E, F = fun x => χ x • pr (g₀ x) := ⟨_, rfl⟩
  have hFx : ∀ x, F x = χ x • pr (g₀ x) := fun x => by rw [hF]
  have hFc : Continuous F := by rw [hF]; exact hχc.smul (hprc.comp hg₀c)
  have hFs : tsupport F ⊆ ball (0 : Eucl N) R := by
    rw [hF]; exact (tsupport_smul_subset_left _ _).trans hχs
  have hF1 : ∀ x, ‖F x‖ ≤ 1 := by
    intro x
    rw [hFx, norm_smul, Real.norm_of_nonneg (hχ0 x)]
    nlinarith [hχ0 x, hχ1 x, hpr1 (g₀ x), norm_nonneg (pr (g₀ x))]
  obtain ⟨hFi, hFeq⟩ := hpair F hFc hFs hF1
  refine ⟨F, hFc, hFs, hF1, hFi, ?_⟩
  -- Step 9: pointwise, `⟨F, g'⟩ = χρ⟨pr g₀, u⟩ ≥ ρ - ρ(1 - χ) - 2ρ‖g₀ - u‖`.
  have h9 : ∀ x, ρ x - ρ x * (1 - χ x) - 2 * (ρ x * ‖g₀ x - u x‖) ≤ inner ℝ (F x) (g' x) := by
    intro x
    have hinner : inner ℝ (F x) (g' x) = χ x * ρ x * inner ℝ (pr (g₀ x)) (u x) := by
      rw [hFx, hgρu x, real_inner_smul_left, real_inner_smul_right]; ring
    rw [hinner]
    rcases eq_or_ne (g' x) 0 with h0 | h0
    · have : ρ x = 0 := by rw [hρx, h0, norm_zero]
      rw [this]; simp
    · have hux1 : ‖u x‖ = 1 := hu1' x h0
      have hlow : 1 - 2 * ‖g₀ x - u x‖ ≤ inner ℝ (pr (g₀ x)) (u x) := by
        have e1 : inner ℝ (pr (g₀ x)) (u x) = 1 + inner ℝ (pr (g₀ x) - u x) (u x) := by
          rw [inner_sub_left, real_inner_self_eq_norm_sq, hux1]; ring
        have e2 := abs_real_inner_le_norm (pr (g₀ x) - u x) (u x)
        have e3 := hpr2 (g₀ x) (u x) (hu1 x)
        rw [hux1, mul_one] at e2
        rw [e1]
        linarith [neg_abs_le (inner ℝ (pr (g₀ x) - u x) (u x))]
      have hd0 : 0 ≤ ‖g₀ x - u x‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hlow (mul_nonneg (hχ0 x) (hρ0 x)),
        mul_nonneg (sub_nonneg.mpr (hχ1 x)) (mul_nonneg (hρ0 x) hd0)]
  -- Step 10: integrability on `B` of `ρ(1 - χ)`, `ρ‖g₀ - u‖` and `⟨F, g'⟩`.
  have hi2 : Integrable (fun x => ρ x * (1 - χ x)) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.mul_bdd (c := 1) (continuous_const.sub hχc).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sub_nonneg.mpr (hχ1 x))]; linarith [hχ0 x])
  have hi3 : Integrable (fun x => ρ x * ‖g₀ x - u x‖) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.mul_bdd (c := C₀ + 1) (hg₀c.stronglyMeasurable.sub hum).norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hC₀ x) (hu1 x)))
  have hi4 : Integrable (fun x => inner ℝ (F x) (g' x)) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.mono' (continuous_inner.comp_aestronglyMeasurable
      (hFc.aestronglyMeasurable.prodMk hg'm.aestronglyMeasurable))
      (Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans (by
        rw [hρx]; exact mul_le_of_le_one_left (norm_nonneg _) (hF1 x)))
  -- Step 11(a): `∫_B ρ(1 - χ) dμ ≤ ∫_{B ∖ B̄_{R'}} ρ dμ < ε/4`.
  have hAm : MeasurableSet (ball (0 : Eucl N) R \ closedBall 0 R') :=
    measurableSet_ball.diff measurableSet_closedBall
  have h11a : ∫ x in ball (0 : Eucl N) R, ρ x * (1 - χ x) ∂μ ≤ ε / 4 := by
    have hle : ∫ x in ball (0 : Eucl N) R, ρ x * (1 - χ x) ∂μ ≤
        ∫ x in ball (0 : Eucl N) R,
          (ball (0 : Eucl N) R \ closedBall 0 R').indicator ρ x ∂μ := by
      refine setIntegral_mono_on hi2 (hρi.indicator hAm) measurableSet_ball fun x hx => ?_
      by_cases hxA : x ∈ ball (0 : Eucl N) R \ closedBall 0 R'
      · rw [indicator_of_mem hxA]
        nlinarith [hρ0 x, hχ0 x]
      · have hxR' : ‖x‖ ≤ R' := by
          by_contra h
          exact hxA ⟨hx, fun h' => h (mem_closedBall_zero_iff.mp h')⟩
        rw [indicator_of_notMem hxA, hχin x hxR', sub_self, mul_zero]
    have heq : ∫ x in ball (0 : Eucl N) R,
          (ball (0 : Eucl N) R \ closedBall 0 R').indicator ρ x ∂μ =
        ∫ x in ball (0 : Eucl N) R \ closedBall 0 R', ρ x ∂μ := by
      rw [setIntegral_indicator hAm, inter_eq_right.mpr sdiff_subset]
    have hlt : ∫ x in ball (0 : Eucl N) R \ closedBall 0 R', ρ x ∂μ < ε / 4 := by
      rw [← ENNReal.ofReal_lt_ofReal_iff hε4, ← hνS _ hAm sdiff_subset]
      exact hνR'
    linarith
  -- Step 11(b): `∫_B ρ‖g₀ - u‖ dμ ≤ ε/4` by (5.1).
  have h11b : ∫ x in ball (0 : Eucl N) R, ρ x * ‖g₀ x - u x‖ ∂μ ≤ ε / 4 := by
    rw [← ENNReal.ofReal_le_ofReal_iff hε4.le, ofReal_integral_eq_lintegral_ofReal hi3
      (Eventually.of_forall fun x => mul_nonneg (hρ0 x) (norm_nonneg _))]
    exact h51
  -- Step 12: integrate the pointwise estimate over `B`.
  have hiA : Integrable (fun x => ρ x - ρ x * (1 - χ x)) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.sub hi2
  have hiB : Integrable (fun x => ρ x - ρ x * (1 - χ x) - 2 * (ρ x * ‖g₀ x - u x‖))
      (μ.restrict (ball (0 : Eucl N) R)) := hiA.sub (hi3.const_mul 2)
  have h12 := integral_mono hiB hi4 h9
  rw [integral_sub hiA (hi3.const_mul 2), integral_sub hρi hi2, integral_const_mul] at h12
  have hFg : ∫ x in ball (0 : Eucl N) R, inner ℝ (F x) (g x) ∂μ =
      ∫ x in ball (0 : Eucl N) R, inner ℝ (F x) (g' x) ∂μ :=
    integral_congr_ae (hgg'.mono fun x hx => by simp only [hx])
  rw [hρ_eq, hFeq, hFg]
  linarith
/-- **Polar test form for a `k`-vector field** (Simon Ch. 6, 2.6–2.8).  If the coordinates
`κ^γ = κ(dx^γ)` of `κ : ℝ^N → Λ_k(ℝ^N)` are `μ`-integrable on `B = B_R(0)`, then for every `ε > 0`
there is a continuous `k`-form `ω` with `tsupport ω ⊆ B` and `|ω| ≤ 1` such that
`∫_B |κ| dμ ≤ ∫ κ(ω) dμ + ε`, where `|κ| = (∑_γ (κ^γ)²)^{1/2}`.  Apply
`imc_mlb_exists_unit_field_integral_ge` to the coefficient field `c = (κ^γ)_γ ∈ ℝ^I` and put
`ω = ∑_γ F^γ dx^γ`, so that `|ω| = |F| ≤ 1` and `κ(ω) = ⟨F, c⟩`. -/
theorem Submission.imc_mlb_exists_form_lintegral_coordNorm_le : ∀ (N k : ℕ) (μ : Measure (Eucl N)) (κ : Eucl N → NVector (Eucl N) k) (R : ℝ), (∀ γ : SimonMultiIndex k N, IntegrableOn (fun x => euclideanNVectorCoordinate (κ x) γ) (ball (0 : Eucl N) R) μ) → ∀ ε : ℝ, 0 < ε → ∃ ω : Eucl N → Covector (Eucl N) k, Continuous ω ∧ tsupport ω ⊆ ball (0 : Eucl N) R ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ Integrable (fun x => κ x (ω x)) μ ∧ ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ ENNReal.ofReal (∫ x, κ x (ω x) ∂μ + ε) := by
  intro N k μ κ R hκ ε hε
  classical
  -- Step 1: the coefficient field `c(x) = (κ^γ(x))_γ = ∑_γ κ^γ(x) e_γ` in `ℝ^I`.
  obtain ⟨c, hc_apply⟩ : ∃ c : Eucl N → EuclideanSpace ℝ (SimonMultiIndex k N),
      ∀ x γ, c x γ = euclideanNVectorCoordinate (κ x) γ :=
    ⟨fun x => WithLp.toLp 2 fun γ => euclideanNVectorCoordinate (κ x) γ, fun _ _ => rfl⟩
  have hc_sum : c = fun x => ∑ γ : SimonMultiIndex k N,
      euclideanNVectorCoordinate (κ x) γ • EuclideanSpace.single γ (1 : ℝ) := by
    funext x
    ext β
    simp [hc_apply, Pi.single_apply, mul_ite]
  -- Step 2: `c` is `μ`-integrable on `B`.
  have hc : IntegrableOn c (ball (0 : Eucl N) R) μ := by
    rw [hc_sum]
    exact integrable_finsetSum _ fun γ _ => (hκ γ).smul_const _
  -- Step 3: `|c(x)| = (∑_γ κ^γ(x)²)^{1/2}`.
  have hc_norm : ∀ x, ‖c x‖ =
      Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2) := by
    intro x
    simp [EuclideanSpace.norm_eq, hc_apply]
  -- Step 4: a continuous unit field `F` nearly attaining `∫_B |c| dμ`.
  obtain ⟨F, hF, hFB, hF1, hFi, hFle⟩ := Submission.imc_mlb_exists_unit_field_integral_ge N
    (EuclideanSpace ℝ (SimonMultiIndex k N)) μ R c hc ε hε
  -- Step 5: the test form `ω = ∑_γ F^γ dx^γ`.
  obtain ⟨ω, hω⟩ : ∃ ω : Eucl N → Covector (Eucl N) k, ∀ x, ω x = ∑ γ : SimonMultiIndex k N,
      F x γ • wedgeCovectors k (fun j => EuclideanSpace.proj (γ j)) :=
    ⟨_, fun _ => rfl⟩
  -- Step 5(d): `κ(x)(ω(x)) = ∑_γ F^γ(x) κ^γ(x) = ⟨F(x), c(x)⟩`.
  have hpair : (fun x => κ x (ω x)) = fun x => inner ℝ (F x) (c x) := by
    funext x
    simp only [hω, map_sum, map_smul, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, hc_apply, euclideanNVectorCoordinate, mul_comm]
  refine ⟨ω, ?_, ?_, fun x => ?_, ?_, ?_⟩
  · -- Step 5(a): `ω` is continuous.
    rw [show ω = _ from funext hω]
    fun_prop
  · -- Step 5(b): `support ω ⊆ support F`, so `tsupport ω ⊆ tsupport F ⊆ B`.
    refine (closure_mono (Function.support_subset_iff'.2 fun x hx => ?_)).trans hFB
    rw [Function.notMem_support] at hx
    simp [hω, hx]
  · -- Step 5(c): the coordinates of `ω(x)` are `F^β(x)`, so `|ω(x)| = |F(x)| ≤ 1`.
    have hcoord : ∀ β, euclideanCovectorCoordinate (ω x) β = F x β := by
      intro β
      rw [hω]
      exact Submission.smr_ci_coord_sum_smul_wedge N k (fun γ => F x γ) β
    calc covectorEuclideanNorm (ω x)
        = Real.sqrt (∑ β : SimonMultiIndex k N, (F x β) ^ 2) := by
          rw [Submission.smr_ci_norm_eq_sqrt_sum_coord_sq]
          simp only [hcoord]
      _ = ‖F x‖ := by simp [EuclideanSpace.norm_eq]
      _ ≤ 1 := hF1 x
  · -- Step 6: `κ(ω) = ⟨F, c⟩` is `μ`-integrable.
    rw [hpair]
    exact hFi
  · -- Step 7: `∫⁻_B |κ| dμ = ofReal (∫_B |c| dμ) ≤ ofReal (∫ ⟨F, c⟩ dμ + ε)`.
    rw [hpair]
    calc ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
          (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ
        = ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal ‖c x‖ ∂μ := by simp only [hc_norm]
      _ = ENNReal.ofReal (∫ x in ball (0 : Eucl N) R, ‖c x‖ ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (Integrable.norm hc)
          (Eventually.of_forall fun x => norm_nonneg (c x))).symm
      _ ≤ ENNReal.ofReal (∫ x, inner ℝ (F x) (c x) ∂μ + ε) := ENNReal.ofReal_le_ofReal hFle
/-- **Kronecker duality of coordinate wedges (Simon Ch. 6, 1.1–1.2).**  For an increasing
multi-index `I`, `dx^I = dx^{I₁} ∧ ⋯ ∧ dx^{Iₙ}` has coordinate `1` at `I` and `0` at every
increasing `J ≠ I`: by (1.1), `dx^I(e_{J₁}, …, e_{Jₙ}) = det [I i = J j]`.  For `J = I` this matrix
is the identity, as `I` is injective.  For `J ≠ I` some `I i ∉ range J` (otherwise the finite
ranges, of equal cardinality, coincide, and increasing enumerations with equal ranges are equal),
so row `i` vanishes. -/
theorem Submission.polyhedral_approx_pairing_wedge_kronecker : ∀ (P n : ℕ) (I : SimonMultiIndex n P), euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) I = 1 ∧ ∀ J : SimonMultiIndex n P, J ≠ I → euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J = 0 := by
  intro P n I
  -- (1)–(2) The coordinate at `J` is the determinant of the matrix `[I i = J j]`.
  have hdet : ∀ J : SimonMultiIndex n P,
      euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        Matrix.det (Matrix.of fun i j => if I i = J j then (1 : ℝ) else 0) := by
    intro J
    rw [euclideanCovectorCoordinate, wedgeCovectors_apply_det]
    congr 1
    ext i j
    simp [PiLp.single_apply]
  refine ⟨?_, fun J hJ => ?_⟩
  · -- (3) For `J = I` the matrix is the identity, as `I` is injective.
    have hone : (Matrix.of fun i j => if I i = I j then (1 : ℝ) else 0) = 1 := by
      ext i j
      simp [Matrix.one_apply, I.injective.eq_iff]
    rw [hdet, hone, Matrix.det_one]
  · -- (4) Some `I i` lies outside `range J`: otherwise `range I = range J` and `I = J`.
    obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
      by_contra h
      have hsub : range I ⊆ range J := by
        rintro _ ⟨i, rfl⟩
        by_contra hi
        exact h ⟨i, fun j hj => hi ⟨j, hj.symm⟩⟩
      have hrange : range I = range J :=
        Set.eq_of_subset_of_ncard_le hsub (by
          rw [Set.ncard_range_of_injective I.injective, Set.ncard_range_of_injective J.injective])
      exact hJ (OrderEmbedding.range_inj_of_wellFoundedLT.mp hrange).symm
    -- (5) Row `i` of the matrix vanishes, so the determinant is `0`.
    rw [hdet]
    exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [hi j]
/-- An `n`-covector on `ℝ^P` is determined by its coordinates on increasing multi-indices
(Simon Ch. 6, 1.2): if `α(e_{I(0)}, …, e_{I(n-1)}) = β(e_{I(0)}, …, e_{I(n-1)})` for every
increasing `I`, then `α = β`.  Alternating maps agreeing on injective tuples of basis vectors are
equal; sorting an injective tuple `v` by `σ = Tuple.sort v` gives the increasing `I = v ∘ σ`, and
`e_v = e_I ∘ σ⁻¹` gives `γ(e_v) = sign(σ⁻¹) γ(e_I)` for `γ = α, β`. -/
theorem Submission.polyhedral_approx_pairing_covector_ext : ∀ (P n : ℕ) (α β : Covector (Eucl P) n), (∀ I : SimonMultiIndex n P, euclideanCovectorCoordinate α I = euclideanCovectorCoordinate β I) → α = β := by
  intro P n α β h
  -- Reduce to the underlying alternating maps on injective tuples of standard basis vectors.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  -- Sorting `v` by `σ = Tuple.sort v` gives the increasing multi-index `I = v ∘ σ`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  let I : SimonMultiIndex n P := OrderEmbedding.ofStrictMono _ hsm
  -- `e_v = e_I ∘ σ⁻¹`.
  have he : (fun i => EuclideanSpace.single (v i) (1 : ℝ)) =
      (fun j => EuclideanSpace.single (I j) (1 : ℝ)) ∘ ⇑(Tuple.sort v)⁻¹ := by
    funext i
    simp [I]
  -- `γ(e_v) = sign(σ⁻¹) • γ(e_I)` for `γ = α, β`, and `α(e_I) = β(e_I)`.
  rw [he, AlternatingMap.map_perm, AlternatingMap.map_perm]
  congr 1
  exact h I
/-- **Coordinate bound** (for the pairing expansion in the proof of Simon Ch. 6, 6.2, p. 169).
Each increasing coordinate `c_I = c(e_{I(1)}, …, e_{I(n)})` of an `n`-covector `c` is bounded in
absolute value by the Euclidean coefficient norm `|c|` of Remark 2.6.  Here `|c|² = ∑_J t_J`, with
`t_J = c(e_{J(1)}, …, e_{J(n)})²` for strictly increasing `J : Fin n → Fin P` and `t_J = 0`
otherwise.  Every `t_J ≥ 0` and `t_I = c_I²`, so `c_I² ≤ |c|²`. -/
theorem Submission.polyhedral_approx_pairing_coordinate_bound : ∀ (P n : ℕ) (c : Covector (Eucl P) n) (I : SimonMultiIndex n P), |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c := by
  intro P n c I
  -- `|c| = √(∑_J t_J)`, the sum over all `J : Fin n → Fin P`.
  set t : (Fin n → Fin P) → ℝ := fun J =>
    if StrictMono J then (c fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) ^ 2 else 0 with ht
  -- Each `t_J` is a square or `0`.
  have ht0 : ∀ J ∈ Finset.univ, 0 ≤ t J := fun J _ => by
    simp only [ht]
    split_ifs <;> positivity
  -- `⇑I` is strictly increasing and `basisFun (I i) = e_{I(i)}`, so `t_I = c_I²`.
  have htI : t I = euclideanCovectorCoordinate c I ^ 2 := by
    simp only [ht, I.strictMono, ite_true, EuclideanSpace.basisFun_apply, euclideanCovectorCoordinate]
  -- `|c_I| = √(c_I²) = √(t_I) ≤ √(∑_J t_J) = |c|`.
  calc |euclideanCovectorCoordinate c I| = √(euclideanCovectorCoordinate c I ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(∑ J, t J) := by
        rw [← htI]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum ht0 (Finset.mem_univ _))
    _ = covectorEuclideanNorm c := rfl

/-- **Pairing expansion** (Simon Ch. 6, 1.2 and 1.7, pp. 132–133; used for 6.2, p. 169).  For an
`n`-vector `w` and an `n`-covector `c` on `ℝ^P`, `w(c) = ∑_I c_I · w(dx^I)`, the sum over the
increasing multi-indices `I`, where `c_I = c(e_{I(1)}, …, e_{I(n)})` and
`dx^I = dx^{I(1)} ∧ ⋯ ∧ dx^{I(n)}`; moreover `|c_I| ≤ |c|`.  Since `dx^I(e_J) = δ_{IJ}` on
increasing multi-indices, `c` and `∑_I c_I dx^I` have the same increasing coordinates, hence are
equal (1.2), and `w` is linear. -/
theorem Submission.polyhedral_approx_pairing_expansion : ∀ (P n : ℕ) (w : NVector (Eucl P) n) (c : Covector (Eucl P) n), w c = ∑ I : SimonMultiIndex n P, euclideanCovectorCoordinate c I * w (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) ∧ ∀ I : SimonMultiIndex n P, |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c := by
  intro P n w c
  refine ⟨?_, Submission.polyhedral_approx_pairing_coordinate_bound P n c⟩
  -- `c = ∑_I c_I • dx^I`: both sides have the same increasing coordinates.
  have hc : c = ∑ I : SimonMultiIndex n P,
      euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) := by
    refine Submission.polyhedral_approx_pairing_covector_ext P n _ _ fun J => ?_
    -- The `J`-th coordinate of the sum is `∑_I c_I · dx^I(e_J)`.
    have hsum : euclideanCovectorCoordinate (∑ I : SimonMultiIndex n P,
          euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        ∑ I : SimonMultiIndex n P, euclideanCovectorCoordinate c I *
          euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J := by
      simp only [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    -- Only `I = J` contributes, since `dx^I(e_J) = δ_{IJ}`.
    rw [hsum, Finset.sum_eq_single J]
    · rw [(Submission.polyhedral_approx_pairing_wedge_kronecker P n J).1, mul_one]
    · intro I _ hIJ
      rw [(Submission.polyhedral_approx_pairing_wedge_kronecker P n I).2 J (Ne.symm hIJ), mul_zero]
    · intro hJ
      exact absurd (Finset.mem_univ J) hJ
  -- `w(∑_I c_I • dx^I) = ∑_I c_I · w(dx^I)` by linearity.
  calc w c = w (∑ I : SimonMultiIndex n P,
        euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) :=
        congrArg w hc
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- **Lower half of the mass formula `M(T) = ∫ |T⃗| dμ_T` (Simon Ch. 6, 2.7–2.8; display (1) in the
proof of Lemma 3.13).**  If `(μ, κ)` represents `Y ∈ 𝒟_k(ℝ^N)` as in (2.7), then
`∫ |κ| dμ ≤ M(Y)` in `[0, ∞]`, where `|w| = (∑_γ w(dx^γ)²)^{1/2}` is the Euclidean norm of a
`k`-vector.  Let `M(Y) < ∞` and `R ∈ ℕ`.  The coordinates `κ^γ` are `μ`-integrable on `B_R`, so
for `ε > 0` there is a continuous form `ω` with `tsupport ω ⊆ B_R`, `|ω| ≤ 1` and
`∫_{B_R} |κ| dμ ≤ ∫ κ(ω) dμ + ε`; by (2.7) and the mass bound, `∫ κ(ω) dμ ≤ M(Y)`.  Hence
`∫_{B_R} |κ| dμ ≤ M(Y)`; let `R ↑ ∞`. -/
theorem Submission.imc_lintegral_coordNorm_le_mass : ∀ (N k : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ : Measure (Eucl N)) (κ : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation Y μ κ → ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ Y.mass := by
  intro N k Y μ κ hY
  -- If `M(Y) = ∞` there is nothing to prove.
  rcases eq_or_ne Y.mass ∞ with hM | hM
  · rw [hM]
    exact le_top
  -- Step 7: the integral over every ball `B_R`, `R ∈ ℕ`, is at most `M(Y)`.
  have hball : ∀ R : ℕ, ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
      (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ Y.mass := by
    intro R
    -- Step 1: the coordinates `κ^γ` are `μ`-integrable on `closedBall 0 R ⊇ B_R`.
    have hint : ∀ γ : SimonMultiIndex k N,
        IntegrableOn (fun x => euclideanNVectorCoordinate (κ x) γ) (ball (0 : Eucl N) R) μ :=
      fun γ => (Submission.cmb_rb_measureRepresentation_integrableOn_coeff N k univ univ
        isOpen_univ subset_rfl Y μ κ hY (closedBall 0 R) (isCompact_closedBall 0 R)
        (subset_univ _) γ).mono_set ball_subset_closedBall
    -- `B_R ⊂⊂ ℝ^N`, and `M_{B_R}(Y) ≤ M(Y) = ofReal (M(Y).toReal)`.
    have hW : CompactlyContainedOpen (ball (0 : Eucl N) R) univ :=
      ⟨isOpen_ball, (isCompact_closedBall 0 R).closure_of_subset ball_subset_closedBall,
        subset_univ _⟩
    have hmass : Y.massOn (ball (0 : Eucl N) R) ≤ ENNReal.ofReal Y.mass.toReal := by
      rw [ENNReal.ofReal_toReal hM]
      exact Y.massOn_mono (subset_univ _)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    -- Steps 3–6: a continuous form `ω`, `tsupport ω ⊆ B_R`, `|ω| ≤ 1`, nearly attains
    -- `∫_{B_R} |κ| dμ`.
    obtain ⟨ω, hω, hωR, hω1, -, hle⟩ := Submission.imc_mlb_exists_form_lintegral_coordNorm_le
      N k μ κ R hint ε (NNReal.coe_pos.mpr hε)
    -- Step 2: `∫ κ(ω) dμ ≤ |∫ κ(ω) dμ| ≤ M(Y).toReal`.
    have hωM : ∫ x, κ x (ω x) ∂μ ≤ Y.mass.toReal := by
      have h := (Submission.cmb_measureRepresentation_continuous_bound N k univ _ hW Y μ κ hY
        Y.mass.toReal 1 ENNReal.toReal_nonneg hmass ω hω hωR hω1).2
      rw [mul_one] at h
      exact (le_abs_self _).trans h
    calc _ ≤ ENNReal.ofReal (∫ x, κ x (ω x) ∂μ + ε) := hle
      _ ≤ ENNReal.ofReal (Y.mass.toReal + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = Y.mass + ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg, ENNReal.ofReal_toReal hM,
          ENNReal.ofReal_coe_nnreal]
  -- Monotone convergence along the directed exhaustion `⋃_R B_R = ℝ^N`; no measurability of the
  -- integrand is needed.
  calc _ = ∫⁻ x in ⋃ R : ℕ, ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
        (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ := by
        rw [iUnion_ball_nat, Measure.restrict_univ]
    _ = ⨆ R : ℕ, ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
        (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ :=
        setLIntegral_iUnion_of_directed _
          (Monotone.directed_le fun _ _ h => ball_subset_ball (Nat.cast_le.mpr h))
    _ ≤ Y.mass := iSup_le hball
/-- Riesz–Fischer (the `L¹`-limit step in the proof of Simon Ch. 6, Lemma 3.13): if the `fₙ` are
`μ`-a.e. strongly measurable with `∑ₙ ∫⁻ ‖fₙ₊₁ − fₙ‖ₑ dμ < ∞`, then `fₙ → g` `μ`-a.e. for a
`μ`-a.e. strongly measurable `g`, and `∫⁻ ‖fₙ − g‖ₑ dμ → 0`. -/
theorem Submission.imc_ae_tendsto_of_summable_lintegral :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → X → E), (∀ n, AEStronglyMeasurable (f n) μ) → (∑' n, ∫⁻ x, ‖f (n + 1) x - f n x‖ₑ ∂μ) ≠ ∞ → ∃ g : X → E, AEStronglyMeasurable g μ ∧ (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧ Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ∂μ) atTop (𝓝 0) := by
  intro X _ μ E _ _ f hf hsum
  -- Step 1: the increments `dₙ = ‖fₙ₊₁ − fₙ‖ₑ` have a.e. finite sum (`lintegral_tsum`).
  set d : ℕ → X → ℝ≥0∞ := fun n x => ‖f (n + 1) x - f n x‖ₑ
  have hd : ∀ n, AEMeasurable (d n) μ := fun n => ((hf (n + 1)).sub (hf n)).enorm
  have hS : ∫⁻ x, ∑' n, d n x ∂μ = ∑' n, ∫⁻ x, d n x ∂μ := lintegral_tsum hd
  have hfin : ∀ᵐ x ∂μ, ∑' n, d n x < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hd) (by rw [hS]; exact hsum)
  -- Step 2: where the sum is finite, `(fₙ x)` is Cauchy.
  have hedist : ∀ x n, edist (f n x) (f (n + 1) x) ≤ d n x := fun x n => by
    rw [edist_comm, edist_eq_enorm_sub]
  have hcauchy : ∀ᵐ x ∂μ, CauchySeq (fun n => f n x) := by
    filter_upwards [hfin] with x hx
    exact cauchySeq_of_edist_le_of_tsum_ne_top (fun n => d n x) (hedist x) hx.ne
  -- Step 3: the limit `g`, a.e. strongly measurable as an a.e. limit.
  set g : X → E := fun x => limUnder atTop (fun n => f n x)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    filter_upwards [hcauchy] with x hx
    exact hx.tendsto_limUnder
  refine ⟨g, aestronglyMeasurable_of_tendsto_ae atTop hf hlim, hlim, ?_⟩
  -- Step 4: `‖fₙ − g‖ₑ ≤ ∑_{m ≥ n} dₘ` a.e.
  have htail : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ₑ ≤ ∑' m, d (n + m) x := by
    intro n
    filter_upwards [hfin, hlim] with x hx hxl
    rw [← edist_eq_enorm_sub]
    exact edist_le_tsum_of_edist_le_of_tendsto (fun m => d m x) (hedist x) hxl n
  -- Step 5: integrate; the tails of a finite series tend to `0`.
  have hbound : ∀ n, ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤ ∑' m, ∫⁻ x, d (n + m) x ∂μ := by
    intro n
    calc ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤ ∫⁻ x, ∑' m, d (n + m) x ∂μ := lintegral_mono_ae (htail n)
      _ = ∑' m, ∫⁻ x, d (n + m) x ∂μ := lintegral_tsum fun m => hd (n + m)
  have htend : Tendsto (fun n => ∑' m, ∫⁻ x, d (n + m) x ∂μ) atTop (𝓝 0) := by
    have := ENNReal.tendsto_sum_nat_add (fun m => ∫⁻ x, d m x ∂μ) hsum
    simpa [add_comm] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend (fun n => bot_le) hbound
/-- Splitting of the blown-up weighted integral (Simon Ch. 3, Remark 1.8(1)): for `C ⊆ M` and all
small `t > 0`, `∫_M φ(η_t) θ = θ(y) ∫_C φ(η_t) + ∫_C φ(η_t) (θ − θ(y)) + ∫_{M∖C} φ(η_t) θ`. -/
theorem Submission.lpf_wtc_wtt_blowup_integral_split : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ x in M, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)) = θ y * ∫ x in C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q)) + ∫ x in C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y) ∂(μHE[n] : Measure (Eucl Q)) + ∫ x in M \ C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n M C θ y φ hM hC hCM ⟨r, hr, hCr, hθr⟩
  -- Step 1: `tsupport φ ⊆ B_R(0)` and `|φ| ≤ A`.
  obtain ⟨R, -, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- Step 2: `t R < r` for all sufficiently small `t > 0`; fix such a `t`.
  have hlim : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.mul_const R
  filter_upwards [hlim.eventually (eventually_lt_nhds hr), self_mem_nhdsWithin] with t htR ht
  -- Step 3: `F = φ ∘ η_t` is continuous, bounded by `A`, and vanishes off `B̄_r(y)`.
  have hcont : Continuous fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) :=
    (map_continuous φ).comp ((continuous_id.sub continuous_const).const_smul t⁻¹)
  have hzero : ∀ x ∉ closedBall y r, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro x hx
    by_contra hne
    have hball := hR (subset_tsupport _ (Function.mem_support.2 hne))
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg (le_of_lt ht), inv_mul_lt_iff₀ ht] at hball
    exact hx (mem_closedBall.2 (by rw [dist_eq_norm]; linarith))
  suffices key : ∀ F : Eucl Q → ℝ, Continuous F → (∀ x, ‖F x‖ ≤ A) →
      (∀ x ∉ closedBall y r, F x = 0) →
      ∫ x in M, F x * θ x ∂(μHE[n] : Measure (Eucl Q)) =
        θ y * ∫ x in C, F x ∂(μHE[n] : Measure (Eucl Q)) +
          ∫ x in C, F x * (θ x - θ y) ∂(μHE[n] : Measure (Eucl Q)) +
            ∫ x in M \ C, F x * θ x ∂(μHE[n] : Measure (Eucl Q)) from
    key _ hcont (fun x => hA _) hzero
  intro F hFc hFA hF0
  generalize (μHE[n] : Measure (Eucl Q)) = μ at hM hC hCr hθr ⊢
  -- Step 4: `F θ` is integrable on `M ∩ B̄_r(y)`, and vanishes on the rest of `M`.
  have hFθM : IntegrableOn (fun x => F x * θ x) M μ := by
    refine IntegrableOn.of_ae_sdiff_eq_zero
      (hθr.bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hFA)) hM
      (Eventually.of_forall fun x hx => ?_)
    rw [hF0 x fun h => hx.2 ⟨hx.1, h⟩, zero_mul]
  -- Step 5: `F` is integrable on `C ∩ B̄_r(y)` (finite measure), and vanishes on the rest of `C`.
  have hFC : IntegrableOn F C μ :=
    (Measure.integrableOn_of_bounded hCr.ne hFc.aestronglyMeasurable
      (Eventually.of_forall hFA)).of_ae_sdiff_eq_zero hC
        (Eventually.of_forall fun x hx => hF0 x fun h => hx.2 ⟨hx.1, h⟩)
  -- Step 6: derived integrabilities on `C` and `M \ C`.
  have hFθC : IntegrableOn (fun x => F x * θ x) C μ := hFθM.mono_set hCM
  have hFθMC : IntegrableOn (fun x => F x * θ x) (M \ C) μ := hFθM.mono_set sdiff_subset
  have hθF : IntegrableOn (fun x => θ y * F x) C μ := hFC.const_mul _
  have hFd : IntegrableOn (fun x => F x * (θ x - θ y)) C μ :=
    (hFθC.sub hθF).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  -- Step 7: split `M = C ∪ (M \ C)`.
  have h7 : ∫ x in M, F x * θ x ∂μ = ∫ x in C, F x * θ x ∂μ + ∫ x in M \ C, F x * θ x ∂μ := by
    conv_lhs => rw [← union_sdiff_cancel hCM]
    exact setIntegral_union₀ disjoint_sdiff_right.aedisjoint (hM.diff hC) hFθC hFθMC
  -- Step 8: split the weight on `C`.
  have h8 : ∫ x in C, F x * θ x ∂μ =
      θ y * ∫ x in C, F x ∂μ + ∫ x in C, F x * (θ x - θ y) ∂μ := by
    rw [← integral_const_mul, ← integral_add hθF hFd]
    congr 1
    funext x
    ring
  -- Step 9: combine.
  rw [h7, h8]

/-- If `C` is `Hⁿ`-null-measurable, `θ` is continuous at `y` within `C` and
`Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for small `ρ > 0`, then
`t⁻ⁿ ∫_C φ(η_{y,t}(x)) (θ(x) - θ(y)) dHⁿ(x) → 0` as `t → 0⁺`.  With `tsupport φ ⊆ B_R(0)` and
`|φ| ≤ A`, the integrand vanishes off `B̄_{tR}(y)` and is at most `A ε₁` on `C ∩ B̄_{tR}(y)` once
`tR < δ(ε₁)`, so the integral is at most `A ε₁ K (tR)ⁿ`. -/
theorem Submission.lpf_wtc_wtt_continuity_error_vanishes :
    ∀ (Q n : ℕ) (C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q)
      (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ),
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → ContinuousWithinAt θ C y →
      (∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n)) →
      Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in C,
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y)
          ∂(μHE[n] : Measure (Eucl Q))) (𝓝[>] 0) (𝓝 0) := by
  intro Q n C θ y φ hC hθ hK
  obtain ⟨K, hK⟩ := hK
  -- `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A`.
  obtain ⟨R, hR, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- For `t > 0`, `φ(η_t(x)) = 0` off `B̄_{tR}(y)`.
  have hloc : ∀ t : ℝ, 0 < t → ∀ x, x ∉ closedBall y (t * R) →
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro t ht x hx
    by_contra hne
    have hmem := hRφ (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos ht, inv_mul_lt_iff₀ ht] at hmem
    exact hx (mem_closedBall.2 ((dist_eq_norm x y).trans_le hmem.le))
  -- `tR → 0` within `(0, ∞)`, so the density bound holds at `ρ = tR` for small `t > 0`.
  have hRt : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const R
  have hRt' : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hRt, eventually_nhdsWithin_of_forall fun t ht => mul_pos ht hR⟩
  have hKt := hRt'.eventually hK
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := A * K * R ^ n with hc
  have hc0 : 0 ≤ c := by positivity
  set ε₁ : ℝ := ε / (2 * (c + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ, hθδ⟩ := Metric.continuousWithinAt_iff.1 hθ ε₁ hε₁0
  filter_upwards [hKt, hRt.eventually (Iio_mem_nhds hδ), self_mem_nhdsWithin] with t htK htδ ht
  have ht0 : 0 < t := ht
  set μ : Measure (Eucl Q) := (μHE[n] : Measure (Eucl Q))
  set f : Eucl Q → ℝ := fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y)
    with hf
  set B : Set (Eucl Q) := closedBall y (t * R)
  -- `μ⌞C`-a.e., `|f| ≤ A ε₁ 1_B`.
  have hpt : ∀ᵐ x ∂μ.restrict C, ENNReal.ofReal ‖f x‖ ≤
      B.indicator (fun _ => ENNReal.ofReal (A * ε₁)) x := by
    filter_upwards [ae_restrict_mem₀ hC] with x hxC
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB]
      refine ENNReal.ofReal_le_ofReal ?_
      have hxy : dist x y < δ := (mem_closedBall.1 hxB).trans_lt htδ
      have h1 : ‖θ x - θ y‖ ≤ ε₁ := by
        rw [← dist_eq_norm]; exact (hθδ hxC hxy).le
      simp only [hf, norm_mul]
      exact mul_le_mul (hA _) h1 (norm_nonneg _) hA0
    · rw [indicator_of_notMem hxB]
      simp [hf, hloc t ht0 x hxB]
  -- `∫⁻_C |f| ≤ A ε₁ μ(C ∩ B) ≤ A ε₁ K (tR)ⁿ < ∞`.
  have hlin : ∫⁻ x in C, ENNReal.ofReal ‖f x‖ ∂μ ≤
      ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) := by
    calc ∫⁻ x in C, ENNReal.ofReal ‖f x‖ ∂μ
        ≤ ∫⁻ x in C, B.indicator (fun _ => ENNReal.ofReal (A * ε₁)) x ∂μ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (A * ε₁) * μ (C ∩ B) := by
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, inter_comm]
      _ ≤ ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) := by
        gcongr
  have hfin : ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top)
  -- `|∫_C f| ≤ A ε₁ K (tR)ⁿ`.
  have hnorm : ‖∫ x in C, f x ∂μ‖ ≤ A * ε₁ * (K * (t * R) ^ n) := by
    refine (norm_integral_le_lintegral_norm f).trans ?_
    refine (ENNReal.toReal_mono hfin hlin).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal]
  -- Rescaling: `t⁻ⁿ |∫_C f| ≤ c ε₁ ≤ ε / 2 < ε`.
  rw [dist_zero_right, norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos ht0]
  calc (t ^ n)⁻¹ * ‖∫ x in C, f x ∂μ‖
      ≤ (t ^ n)⁻¹ * (A * ε₁ * (K * (t * R) ^ n)) := by gcongr
    _ = c * ε₁ := by
      rw [hc, mul_pow]
      field_simp
    _ ≤ (c + 1) * ε₁ := by gcongr; linarith
    _ = ε / 2 := by
      rw [hε₁]
      field_simp
    _ < ε := by linarith

/-- Zero `θ`-weighted `n`-density of `D` at `y` kills the blow-up integrals (Simon Ch. 3,
Remark 1.8(1)): if `(∫⁻_{D ∩ B̄_ρ(y)} θ dHⁿ) / ρⁿ → 0` as `ρ ↓ 0`, then for every `φ ∈ C_c(ℝ^Q)`,
`(tⁿ)⁻¹ ∫_D φ(η_{y,t}(x)) θ(x) dHⁿ(x) → 0` as `t ↓ 0`.  No integrability of `θ` is assumed. -/
theorem Submission.lpf_wtc_wtt_remainder_vanishes : ∀ (Q n : ℕ) (D : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ), NullMeasurableSet D (μHE[n] : Measure (Eucl Q)) → (∀ x ∈ D, 0 ≤ θ x) → Tendsto (fun ρ : ℝ => (∫⁻ x in D ∩ closedBall y ρ, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q))) (𝓝[>] 0) (𝓝 0) := by
  intro Q n D θ y φ hD hθ hlim
  set μ : Measure (Eucl Q) := μHE[n]
  -- Step 1: `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A` (so `A ≥ 0`).
  obtain ⟨R, hR, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  obtain ⟨A, hA⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- Step 2: for `t > 0`, `φ (η_t x) = 0` whenever `x ∉ B̄_{tR}(y)`.
  have hloc : ∀ t : ℝ, 0 < t → ∀ x, x ∉ closedBall y (t * R) →
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro t ht x hx
    by_contra hne
    have hmem := hRφ (subset_tsupport φ (Function.mem_support.2 hne))
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg ht.le, inv_mul_lt_iff₀ ht] at hmem
    exact hx (mem_closedBall_iff_norm.2 hmem.le)
  -- Step 3: compose the density hypothesis with `t ↦ tR`, which tends to `0` within `(0, ∞)`.
  have hTR : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun t : ℝ => t * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos ht hR
  have hq := hlim.comp hTR
  -- (a) eventually `q (tR) < ∞`;
  have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal (θ x) ∂μ)
      / ENNReal.ofReal ((t * R) ^ n) < ⊤ :=
    hq.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  -- (b) `b t = A Rⁿ toReal (q (tR)) → 0`.
  have hb : Tendsto (fun t : ℝ => A * R ^ n * ((∫⁻ x in D ∩ closedBall y (t * R),
      ENNReal.ofReal (θ x) ∂μ) / ENNReal.ofReal ((t * R) ^ n)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hq).const_mul (A * R ^ n)
    rw [ENNReal.toReal_zero, mul_zero] at h0
    exact h0
  -- Step 4: squeeze; fix `t > 0` with `q (tR) < ∞`.
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [hfin, self_mem_nhdsWithin] with t hqt ht
  have ht' : (0 : ℝ) < t := ht
  have htR : 0 < t * R := mul_pos ht' hR
  set L := ∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal (θ x) ∂μ
  -- Step 5: `L (tR) < ∞`.
  have hLtop : L ≠ ⊤ := by
    intro hLt
    rw [hLt, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hqt
    exact lt_irrefl _ hqt
  -- Steps 6–7: `∫⁻_D ofReal |φ(η_t x) θ(x)| ≤ ofReal A · L (tR)`.
  have hlint : ∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖
      ∂μ ≤ ENNReal.ofReal A * L := by
    calc ∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖ ∂μ
        ≤ ∫⁻ x in D, (closedBall y (t * R)).indicator
            (fun x => ENNReal.ofReal A * ENNReal.ofReal (θ x)) x ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hD] with x hx
          by_cases hxB : x ∈ closedBall y (t * R)
          · simp only [indicator_of_mem hxB]
            rw [← ENNReal.ofReal_mul hA0, norm_mul, Real.norm_of_nonneg (hθ x hx)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hA _) (hθ x hx))
          · rw [hloc t ht' x hxB, zero_mul, norm_zero, ENNReal.ofReal_zero]
            exact zero_le
      _ = ∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal A * ENNReal.ofReal (θ x) ∂μ := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm (closedBall y (t * R)) D]
      _ = ENNReal.ofReal A * L := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 8: `|∫_D φ(η_t x) θ(x)| ≤ A · toReal (L (tR))`, with no integrability needed.
  have hint : ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
      ≤ A * L.toReal := by
    calc ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
        ≤ (∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖
            ∂μ).toReal := norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal A * L).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop) hlint
      _ = A * L.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0]
  -- Step 9: rescaling, `(tⁿ)⁻¹ A toReal (L (tR)) = A Rⁿ toReal (q (tR))`.
  have htn : 0 < t ^ n := pow_pos ht' n
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [norm_mul, norm_inv, Real.norm_of_nonneg htn.le, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_pos htR n).le, mul_pow]
  calc (t ^ n)⁻¹ * ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
      ≤ (t ^ n)⁻¹ * (A * L.toReal) := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 htn.le)
    _ = A * R ^ n * (L.toReal / (t ^ n * R ^ n)) := by
      field_simp [htn.ne', hRn.ne']

/-- Change of variables for `Hⁿ`-integrals over blow-ups: `η = η_{y,r}`, `η(x) = r⁻¹(x − y)`,
pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so `∫_{η(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η dHⁿ` for every set
`S` and every `g` (both sides are Bochner set integrals). -/
theorem Submission.lpf_wtc_blowup_setIntegral_image :
    ∀ (Q n : ℕ) (y : Eucl Q) (r : ℝ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ), 0 < r →
      ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, g z ∂(μHE[n] : Measure (Eucl Q)) =
        (r ^ n)⁻¹ * ∫ x in S, g (Poincare.SimonGMT.Chapter03.blowUpMap y r x)
          ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n y r S g hr
  -- `η = blowUpMap y r`, `η x = r⁻¹ • (x - y)`, is a homeomorphism of `ℝ^Q`.
  let e : Eucl Q ≃ₜ Eucl Q :=
    (Homeomorph.addRight (-y)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl Q → Eucl Q) = Poincare.SimonGMT.Chapter03.blowUpMap y r := by
    funext x
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = y + r • B`.
  have hmp : MeasurePreserving (Poincare.SimonGMT.Chapter03.blowUpMap y r)
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl Q))) μHE[n] := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap y r ⁻¹' B =
        (fun z => y + z) '' ((fun z => r • z) '' B) := by
      ext x
      simp only [mem_preimage, mem_image, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · intro hx
        exact ⟨r • r⁻¹ • (x - y), ⟨r⁻¹ • (x - y), hx, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left y), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Density bound at a tangent point (Simon Ch. 3, Remark 1.5(3), boundedness part): if `T` is
the approximate tangent space (Def. 1.4) of `S` at `y` and `Hⁿ(S ∩ B̄_r(y)) < ∞` for some `r > 0`,
then `Hⁿ(S ∩ B̄_ρ(y)) ≤ K ρⁿ` for all sufficiently small `ρ > 0`. -/
theorem Submission.lpf_wtc_density_bound_of_tangent : ∀ (Q n : ℕ) (S : Set (Eucl Q)) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y T → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y r) < ∞) → ∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n) := by
  intro Q n S y T hT ⟨r, hr, hfin⟩
  -- Step 1: the cut-off `φ₀(z) = min(1, max(0, 2 - |z|))`, an element of `C_c(ℝ^Q, ℝ)` with
  -- `0 ≤ φ₀ ≤ 1`, `φ₀ = 1` on `B̄₁(0)` and `φ₀ = 0` off `B̄₂(0)`.
  have hzero : ∀ z : Eucl Q, 2 ≤ ‖z‖ → min 1 (max 0 (2 - ‖z‖)) = (0 : ℝ) := fun z hz => by
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  let φ₀ : CompactlySupportedContinuousMap (Eucl Q) ℝ :=
    ⟨⟨fun z => min 1 (max 0 (2 - ‖z‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) fun z hz =>
        hzero z (not_le.1 (mt mem_closedBall_zero_iff.2 hz)).le⟩
  have hφ₀ : ∀ z, φ₀ z = min 1 (max 0 (2 - ‖z‖)) := fun _ => rfl
  have hφ₀01 : ∀ z, 0 ≤ φ₀ z ∧ φ₀ z ≤ 1 := fun z => by
    rw [hφ₀]
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hφ₀one : ∀ z, ‖z‖ ≤ 1 → φ₀ z = 1 := fun z hz => by
    rw [hφ₀]
    exact min_eq_left (le_max_of_le_right (by linarith))
  set L₀ : ℝ := ∫ z in (T : Set (Eucl Q)), φ₀ z ∂(μHE[n] : Measure (Eucl Q))
  refine ⟨(L₀ + 1).toNNReal, ?_⟩
  -- Step 2: the blow-up integrals of `φ₀` tend to `L₀`, so they are eventually `≤ L₀ + 1`;
  -- also eventually `0 < ρ < r / 2`.
  filter_upwards [(hT.2 φ₀).eventually (eventually_le_nhds (lt_add_one L₀)),
    Ioo_mem_nhdsGT (half_pos hr)] with ρ hρ ⟨hρ0, hρr⟩
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  have hnorm : ∀ x, ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ = ρ⁻¹ * dist x y := by
    intro x
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hρ0), dist_eq_norm]
  have hcont : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y ρ) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hsub : ∀ s ≤ r, S ∩ closedBall y s ⊆ S ∩ closedBall y r := fun s hs =>
    inter_subset_inter_right _ (closedBall_subset_closedBall hs)
  -- Step 3: `ψ = φ₀ ∘ η_{y,ρ}` is integrable on `S` (it is bounded by `1_{B̄_{2ρ}(y)}` and
  -- `Hⁿ(S ∩ B̄_{2ρ}(y)) < ∞`) and dominates `1_{B̄_ρ(y)}`.
  have hψint : Integrable (fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x))
      ((μHE[n] : Measure (Eucl Q)).restrict S) := by
    refine Integrable.mono' (g := (closedBall y (2 * ρ)).indicator fun _ => (1 : ℝ)) ?_
      (φ₀.continuous.comp hcont).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact ne_top_of_le_ne_top hfin.ne (measure_mono (hsub _ (by linarith)))
    · by_cases hx : x ∈ closedBall y (2 * ρ)
      · rw [indicator_of_mem hx, Real.norm_of_nonneg (hφ₀01 _).1]
        exact (hφ₀01 _).2
      · have h2 : 2 ≤ ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ := by
          rw [mem_closedBall, not_le] at hx
          rw [hnorm, le_inv_mul_iff₀ hρ0]
          linarith
        rw [indicator_of_notMem hx, hφ₀, hzero _ h2, norm_zero]
  have hle : (μHE[n] : Measure (Eucl Q)).real (S ∩ closedBall y ρ) ≤
      ∫ x in S, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x)
        ∂(μHE[n] : Measure (Eucl Q)) := by
    rw [inter_comm, ← measureReal_restrict_apply measurableSet_closedBall,
      ← integral_indicator_one measurableSet_closedBall]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hψint (ae_of_all _ fun x => ?_)
    · exact indicator_nonneg (fun _ _ => zero_le_one) x
    · by_cases hx : x ∈ closedBall y ρ
      · have h1 : ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ ≤ 1 := by
          rw [hnorm, inv_mul_le_iff₀ hρ0, mul_one]
          exact hx
        rw [indicator_of_mem hx, Pi.one_apply]
        exact (hφ₀one _ h1).ge
      · rw [indicator_of_notMem hx]
        exact (hφ₀01 _).1
  -- Step 4: by the blow-up identity, `∫_S ψ = ρⁿ ∫_{η_{y,ρ}(S)} φ₀ ≤ (L₀ + 1) ρⁿ`.
  have hS : ∫ x in S, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x)
        ∂(μHE[n] : Measure (Eucl Q)) =
      ρ ^ n * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y ρ '' S, φ₀ z
        ∂(μHE[n] : Measure (Eucl Q)) := by
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y ρ S φ₀ hρ0,
      mul_inv_cancel_left₀ hρn.ne']
  have hfinρ : (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (measure_mono (hsub _ (by linarith)))
  calc (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y ρ)
      = ENNReal.ofReal ((μHE[n] : Measure (Eucl Q)).real (S ∩ closedBall y ρ)) :=
        (ofReal_measureReal hfinρ).symm
    _ ≤ ENNReal.ofReal ((L₀ + 1) * ρ ^ n) := by
        refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
        rw [hS, mul_comm]
        exact mul_le_mul_of_nonneg_right hρ hρn.le
    _ = (L₀ + 1).toNNReal * ENNReal.ofReal (ρ ^ n) := ENNReal.ofReal_mul' hρn.le
/-- Density bound at a weighted tangent point (Simon Ch. 3, Remark 1.8(1)): if `T` is the
approximate tangent space of `M` at `y` with respect to `θ` (Definition 1.7), `θ ≥ 0` on `M`,
`θ(y) > 0`, `C ⊆ M` is null-measurable with `θ|C` continuous at `y`, `Hⁿ(C ∩ B̄_r(y)) < ∞` and `θ`
is `Hⁿ`-integrable on `M ∩ B̄_r(y)` for some `r > 0`, then `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all
sufficiently small `ρ > 0`. -/
theorem Submission.imc_wte_density_bound_of_weightedTangent : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∀ x ∈ M, 0 ≤ θ x) → 0 < θ y → HasWeightedApproximateTangentSpaceAt n M θ y T → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ContinuousWithinAt θ C y → ∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n) := by
  intro Q n M C θ y T hM hC hCM hθ hθy hT ⟨r, hr, hfin, hint⟩ hθC
  -- Step 1: the cut-off `φ₀(z) = min(1, max(0, 2 - |z|))`, an element of `C_c(ℝ^Q, ℝ)` with
  -- `0 ≤ φ₀ ≤ 1`, `φ₀ = 1` on `B̄₁(0)` and `φ₀ = 0` off `B̄₂(0)`.
  have hzero : ∀ z : Eucl Q, 2 ≤ ‖z‖ → min 1 (max 0 (2 - ‖z‖)) = (0 : ℝ) := fun z hz => by
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  let φ₀ : CompactlySupportedContinuousMap (Eucl Q) ℝ :=
    ⟨⟨fun z => min 1 (max 0 (2 - ‖z‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) fun z hz =>
        hzero z (not_le.1 (mt mem_closedBall_zero_iff.2 hz)).le⟩
  have hφ₀ : ∀ z, φ₀ z = min 1 (max 0 (2 - ‖z‖)) := fun _ => rfl
  have hφ₀01 : ∀ z, 0 ≤ φ₀ z ∧ φ₀ z ≤ 1 := fun z => by
    rw [hφ₀]
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hφ₀one : ∀ z, ‖z‖ ≤ 1 → φ₀ z = 1 := fun z hz => by
    rw [hφ₀]
    exact min_eq_left (le_max_of_le_right (by linarith))
  set L₀ : ℝ := ∫ z in (T : Set (Eucl Q)), φ₀ z ∂(μHE[n] : Measure (Eucl Q))
  -- Step 2: `θ > θ(y)/2` on `C` near `y`, since `θ|C` is continuous at `y` and `θ(y) > 0`.
  obtain ⟨δ, hδ, hδθ⟩ := Metric.continuousWithinAt_iff.1 hθC (θ y / 2) (half_pos hθy)
  refine ⟨((θ y * L₀ + 1) / (θ y / 2)).toNNReal, ?_⟩
  -- Step 3: the weighted blow-up integrals of `φ₀` tend to `θ(y) L₀`, so they are eventually
  -- `≤ θ(y) L₀ + 1`; also eventually `0 < ρ < min(r/2, δ)`.
  filter_upwards [(hT.2 φ₀).eventually (eventually_le_nhds (lt_add_one (θ y * L₀))),
    Ioo_mem_nhdsGT (lt_min (half_pos hr) hδ)] with ρ hρ ⟨hρ0, hρrδ⟩
  have hρr : ρ < r / 2 := hρrδ.trans_le (min_le_left _ _)
  have hρδ : ρ < δ := hρrδ.trans_le (min_le_right _ _)
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  have hnorm : ∀ x, ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ = ρ⁻¹ * dist x y := by
    intro x
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hρ0), dist_eq_norm]
  have hcont : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y ρ) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  -- Step 4: `ψ = (φ₀ ∘ η_{y,ρ}) θ` is integrable on `M ∩ B̄_r(y)` (`|φ₀| ≤ 1`) and vanishes off
  -- `B̄_r(y)` (as `2ρ < r`), so it is integrable on `M`; it is nonnegative on `M`.
  have hψM : IntegrableOn (fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x) M
      (μHE[n] : Measure (Eucl Q)) := by
    have hψr : IntegrableOn (fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x)
        (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q)) :=
      Integrable.bdd_mul (c := 1) hint (φ₀.continuous.comp hcont).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (hφ₀01 _).1]
          exact (hφ₀01 _).2)
    refine hψr.of_ae_sdiff_eq_zero hM (ae_of_all _ fun x hx => ?_)
    have hxr : r < dist x y := not_le.1 fun h => hx.2 ⟨hx.1, h⟩
    have h2 : 2 ≤ ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ := by
      rw [hnorm, le_inv_mul_iff₀ hρ0]
      linarith
    rw [hφ₀, hzero _ h2, zero_mul]
  have hψ0 : 0 ≤ᵐ[(μHE[n] : Measure (Eucl Q)).restrict M]
      fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x := by
    filter_upwards [ae_restrict_mem₀ hM] with x hx
    exact mul_nonneg (hφ₀01 _).1 (hθ x hx)
  -- Step 5: `ψ ≥ θ(y)/2` on `C ∩ B̄_ρ(y) ⊆ M`, so `(θ(y)/2) Hⁿ(C ∩ B̄_ρ(y)) ≤ ∫_M ψ`.
  have hA : NullMeasurableSet (C ∩ closedBall y ρ) (μHE[n] : Measure (Eucl Q)) :=
    hC.inter measurableSet_closedBall.nullMeasurableSet
  have hAM : C ∩ closedBall y ρ ⊆ M := inter_subset_left.trans hCM
  have hfinρ : (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (measure_mono (inter_subset_inter_right _
      (closedBall_subset_closedBall (by linarith))))
  have hle : θ y / 2 * (μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ) ≤
      ∫ x in M, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
        ∂(μHE[n] : Measure (Eucl Q)) := by
    calc θ y / 2 * (μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ)
        = ∫ _ in C ∩ closedBall y ρ, θ y / 2 ∂(μHE[n] : Measure (Eucl Q)) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in C ∩ closedBall y ρ, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
            ∂(μHE[n] : Measure (Eucl Q)) := by
          refine setIntegral_mono_ae_restrict (integrableOn_const hfinρ) (hψM.mono_set hAM) ?_
          filter_upwards [ae_restrict_mem₀ hA] with x hx
          have h1 : ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ ≤ 1 := by
            rw [hnorm, inv_mul_le_iff₀ hρ0, mul_one]
            exact hx.2
          have hθx := hδθ hx.1 ((mem_closedBall.1 hx.2).trans_lt hρδ)
          rw [Real.dist_eq, abs_lt] at hθx
          rw [hφ₀one _ h1, one_mul]
          linarith [hθx.1]
      _ ≤ ∫ x in M, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
            ∂(μHE[n] : Measure (Eucl Q)) :=
          setIntegral_mono_set hψM hψ0 hAM.eventuallySubset
  -- Step 6: by the blow-up identity (`y + ρ η_{y,ρ}(x) = x`), `∫_M ψ = ρⁿ W(ρ)`, where `W(ρ)` is
  -- the weighted blow-up integral of `φ₀`.
  have hη : ∀ x, y + ρ • Poincare.SimonGMT.Chapter03.blowUpMap y ρ x = x := fun x => by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ0.ne', add_sub_cancel]
  have hW : ∫ x in M, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
        ∂(μHE[n] : Measure (Eucl Q)) =
      ρ ^ n * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y ρ '' M, φ₀ z * θ (y + ρ • z)
        ∂(μHE[n] : Measure (Eucl Q)) := by
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y ρ M _ hρ0, mul_inv_cancel_left₀ hρn.ne']
    simp_rw [hη]
  -- Step 7: `(θ(y)/2) Hⁿ(C ∩ B̄_ρ(y)) ≤ (θ(y) L₀ + 1) ρⁿ`; divide by `θ(y)/2 > 0`.
  have hkey : (μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ) ≤
      (θ y * L₀ + 1) / (θ y / 2) * ρ ^ n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (half_pos hθy)]
    have hup := mul_le_mul_of_nonneg_left hρ hρn.le
    rw [← hW] at hup
    linarith
  calc (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ)
      = ENNReal.ofReal ((μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ)) :=
        (ofReal_measureReal hfinρ).symm
    _ ≤ ENNReal.ofReal ((θ y * L₀ + 1) / (θ y / 2) * ρ ^ n) := ENNReal.ofReal_le_ofReal hkey
    _ = ((θ y * L₀ + 1) / (θ y / 2)).toNNReal * ENNReal.ofReal (ρ ^ n) :=
        ENNReal.ofReal_mul' hρn.le
/-- Transfer of approximate tangent planes (Simon Ch. 3, proof of Theorem 1.6 "⇒", step 2).  If
`T` is the approximate tangent space of `N` at `y`, `Hⁿ(N ∩ B̄_r(y)) < ∞` for some `r > 0` and
`Hⁿ((C ∖ N) ∩ B̄_ρ(y))`, `Hⁿ((N ∖ C) ∩ B̄_ρ(y))` are `o(ρⁿ)`, then `T` is the approximate tangent
space of `C` at `y`.  For `φ ∈ C_c` with `|φ| ≤ A` and `tsupport φ ⊆ B_R(0)`, the blow-up formula
`lpf_wtc_blowup_setIntegral_image` localizes both blow-up integrals to `B = B̄_{λR}(y)`, and
splitting `C ∩ B`, `N ∩ B` along `C ∩ N ∩ B` gives, for small `λ > 0`,
`|∫_{η_{y,λ}(C)} φ - ∫_{η_{y,λ}(N)} φ| ≤ A Rⁿ (q₁(λR) + q₂(λR))`, where `q₁, q₂` are the two
density quotients of the hypotheses. -/
theorem Submission.lpf_wtc_tangent_transfer :
    ∀ (Q n : ℕ) (C N : Set (Eucl Q)) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)),
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) →
      NullMeasurableSet N (μHE[n] : Measure (Eucl Q)) →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N y T →
      (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (N ∩ closedBall y r) < ∞) →
      Tendsto (fun ρ : ℝ => (μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y ρ) /
        ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun ρ : ℝ => (μHE[n] : Measure (Eucl Q)) ((N \ C) ∩ closedBall y ρ) /
        ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C y T := by
  intro Q n C N y T hC hN hNT hfin hCN hNC
  obtain ⟨r, hr, hNr⟩ := hfin
  -- The dimension condition is inherited from `N`.
  refine ⟨hNT.1, fun φ => ?_⟩
  -- `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A`.
  obtain ⟨R, hR, hRsupp⟩ :=
    (HasCompactSupport.isCompact φ.hasCompactSupport).isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- `t ↦ t * R` maps `𝓝[>] 0` into itself, so `q₁(tR), q₂(tR) → 0`.
  have hmap : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun t : ℝ => t * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos ht hR
  have hCN' := hCN.comp hmap
  have hNC' := hNC.comp hmap
  -- The error bound `A Rⁿ (q₁(tR) + q₂(tR))` tends to `0`.
  have hbound : Tendsto (fun t : ℝ => A * R ^ n *
      (((μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y (t * R)) /
          ENNReal.ofReal ((t * R) ^ n)).toReal +
        ((μHE[n] : Measure (Eucl Q)) ((N \ C) ∩ closedBall y (t * R)) /
          ENNReal.ofReal ((t * R) ^ n)).toReal)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hCN'
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hNC'
    simpa using (h1.add h2).const_mul (A * R ^ n)
  -- The blow-up integrals of `C` and `N` are asymptotically equal.
  have key : Tendsto (fun t : ℝ =>
      (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y t '' C, φ z ∂(μHE[n] : Measure (Eucl Q))) -
        ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y t '' N, φ z ∂(μHE[n] : Measure (Eucl Q)))
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * R < r :=
      (hmap.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hr)
    have hfin₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y (t * R)) /
          ENNReal.ofReal ((t * R) ^ n) < ∞ :=
      hCN'.eventually (gt_mem_nhds ENNReal.zero_lt_top)
    filter_upwards [self_mem_nhdsWithin, hsmall, hfin₁] with t ht htr htfin
    have ht : 0 < t := ht
    -- Localization: `φ ∘ η_{y,t}` vanishes off `B = B̄_{tR}(y)`.
    have hvan : ∀ x, x ∉ closedBall y (t * R) →
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
      intro x hx
      by_contra hne
      apply hx
      have h1 : Poincare.SimonGMT.Chapter03.blowUpMap y t x ∈ ball (0 : Eucl Q) R :=
        hRsupp (subset_tsupport _ hne)
      rw [mem_ball, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
        Real.norm_of_nonneg ht.le, inv_mul_lt_iff₀ ht] at h1
      rw [mem_closedBall, dist_eq_norm]
      exact h1.le
    have hloc : ∀ S : Set (Eucl Q),
        ∫ x in S, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q)) =
          ∫ x in S ∩ closedBall y (t * R), φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x)
            ∂(μHE[n] : Measure (Eucl Q)) := by
      intro S
      rw [← setIntegral_indicator measurableSet_closedBall]
      congr 1
      funext x
      by_cases hx : x ∈ closedBall y (t * R)
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hvan x hx]
    -- Finiteness of the pieces: `tR < r` and `q₁(tR) < ∞`.
    have hBr : closedBall y (t * R) ⊆ closedBall y r := closedBall_subset_closedBall htr.le
    have hNB : (μHE[n] : Measure (Eucl Q)) (N ∩ closedBall y (t * R)) < ∞ :=
      (measure_mono (inter_subset_inter_right N hBr)).trans_lt hNr
    have hP₂ : (μHE[n] : Measure (Eucl Q)) ((N \ C) ∩ closedBall y (t * R)) < ∞ :=
      (measure_mono (inter_subset_inter_left _ sdiff_subset)).trans_lt hNB
    have hP₁ : (μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y (t * R)) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at htfin
      exact lt_irrefl _ htfin
    have hCB : (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y (t * R)) < ∞ := by
      have hsub : C ∩ closedBall y (t * R) ⊆
          (N ∩ closedBall y (t * R)) ∪ ((C \ N) ∩ closedBall y (t * R)) := by
        rintro x ⟨hxC, hxB⟩
        by_cases hxN : x ∈ N
        · exact Or.inl ⟨hxN, hxB⟩
        · exact Or.inr ⟨⟨hxC, hxN⟩, hxB⟩
      exact (measure_mono hsub).trans_lt
        ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hNB, hP₁⟩))
    -- `φ ∘ η_{y,t}` is continuous and bounded by `A`, hence integrable on finite-measure sets.
    have hcont : Continuous fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) :=
      (map_continuous φ).comp (show Continuous fun x : Eucl Q => t⁻¹ • (x - y) by fun_prop)
    have hint : ∀ S : Set (Eucl Q), (μHE[n] : Measure (Eucl Q)) S < ∞ →
        IntegrableOn (fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x)) S
          (μHE[n] : Measure (Eucl Q)) := fun S hS =>
      Measure.integrableOn_of_bounded hS.ne hcont.aestronglyMeasurable
        (Eventually.of_forall fun x => hA _)
    have hnorm : ∀ S : Set (Eucl Q), (μHE[n] : Measure (Eucl Q)) S < ∞ →
        ‖∫ x in S, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x)
          ∂(μHE[n] : Measure (Eucl Q))‖ ≤ A * ((μHE[n] : Measure (Eucl Q)) S).toReal :=
      fun S hS => by
        rw [← measureReal_def]
        exact norm_setIntegral_le_of_norm_le_const hS fun x _ => hA _
    -- Split `C ∩ B` and `N ∩ B` along the common part `C ∩ N ∩ B`.
    have hdC := integral_inter_add_sdiff₀ hN (hint _ hCB)
    have hdN := integral_inter_add_sdiff₀ hC (hint _ hNB)
    have e₀ : C ∩ closedBall y (t * R) ∩ N = N ∩ closedBall y (t * R) ∩ C := by
      ext x; simp only [mem_inter_iff]; tauto
    have e₁ : (C ∩ closedBall y (t * R)) \ N = (C \ N) ∩ closedBall y (t * R) := by
      ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
    have e₂ : (N ∩ closedBall y (t * R)) \ C = (N \ C) ∩ closedBall y (t * R) := by
      ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
    rw [e₀, e₁] at hdC
    rw [e₂] at hdN
    -- `|∫_{η(C)} φ - ∫_{η(N)} φ| = t⁻ⁿ |∫_{P₁} φ ∘ η - ∫_{P₂} φ ∘ η| ≤ t⁻ⁿ A (Hⁿ(P₁) + Hⁿ(P₂))`.
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t C φ ht,
      Submission.lpf_wtc_blowup_setIntegral_image Q n y t N φ ht, ← mul_sub, hloc C, hloc N,
      ← hdC, ← hdN, add_sub_add_left_eq_sub, norm_mul, norm_inv, norm_pow,
      Real.norm_of_nonneg ht.le]
    have hpow : 0 < (t * R) ^ n := pow_pos (mul_pos ht hR) n
    have hle := (norm_sub_le _ _).trans (add_le_add (hnorm _ hP₁) (hnorm _ hP₂))
    refine (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq ?_
    rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_ofReal hpow.le, mul_pow]
    field_simp
  -- Conclusion: `∫_{η(C)} φ = ∫_{η(N)} φ + (∫_{η(C)} φ - ∫_{η(N)} φ) → ∫_T φ + 0`.
  have h := (hNT.2 φ).add key
  rw [add_zero] at h
  exact h.congr fun t => add_sub_cancel _ _

/-- Simon Ch. 3, Remark 1.8(1): if `T` is the approximate tangent space of `C ⊆ M` at `y ∈ C`
(Definition 1.4), `θ ≥ 0` is `Hⁿ`-integrable on `M` near `y`, `θ|C` is continuous at `y` and
`θ Hⁿ ⌞ (M ∖ C)` has `n`-density `0` at `y`, then `T` is the approximate tangent space of `M` at
`y` with respect to `θ` (Definition 1.7).  After the change of variables `z = η_{y,t}(x)`, the
weighted blow-up integral is `θ(y) ∫_{η_{y,t}(C)} φ`, which tends to `θ(y) ∫_T φ`, plus the
oscillation of `θ` along `C` and the contribution of `M ∖ C`, both of which tend to `0`. -/
theorem Submission.lpf_wtc_weighted_tangent_transfer :
    ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)),
      NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) →
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → y ∈ C →
      (∀ x ∈ M, 0 ≤ θ x) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C y T →
      (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧
        IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) →
      ContinuousWithinAt θ C y →
      Tendsto (fun ρ : ℝ => (∫⁻ x in (M \ C) ∩ closedBall y ρ, ENNReal.ofReal (θ x)
        ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      HasWeightedApproximateTangentSpaceAt n M θ y T := by
  intro Q n M C θ y T hM hC hCM _ hθ hT hr hθC hdens
  -- `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all small `ρ > 0`.
  have hK := Submission.lpf_wtc_density_bound_of_tangent Q n C y T hT
    (hr.imp fun _ h => ⟨h.1, h.2.1⟩)
  refine ⟨hT.1, fun φ => ?_⟩
  -- Main term: `(tⁿ)⁻¹ ∫_C φ ∘ η_{y,t} = ∫_{η_{y,t}(C)} φ → ∫_T φ`.
  have h₁ : Tendsto (fun t : ℝ => θ y * ((t ^ n)⁻¹ * ∫ x in C,
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q))))
      (𝓝[>] 0) (𝓝 (θ y * ∫ z in (T : Set (Eucl Q)), φ z ∂(μHE[n] : Measure (Eucl Q)))) := by
    refine ((hT.2 φ).const_mul (θ y)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t C φ ht]
  -- The oscillation of `θ` along `C` and the contribution of `M ∖ C` vanish in the limit.
  have h₂ := Submission.lpf_wtc_wtt_continuity_error_vanishes Q n C θ y φ hC hθC hK
  have h₃ := Submission.lpf_wtc_wtt_remainder_vanishes Q n (M \ C) θ y φ (hM.diff hC)
    (fun x hx => hθ x hx.1) hdens
  have h := (h₁.add h₂).add h₃
  rw [add_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Submission.lpf_wtc_wtt_blowup_integral_split Q n M C θ y φ hM hC hCM hr]
    with t (ht : 0 < t) hsplit
  -- Change of variables `z = η_{y,t}(x)`, under which `y + t • z = x`.
  have hη : ∀ x, y + t • Poincare.SimonGMT.Chapter03.blowUpMap y t x = x := fun x => by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ ht.ne', add_sub_cancel]
  rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t M _ ht]
  simp_rw [hη]
  rw [hsplit]
  ring
/-- Converse weighted transfer (Simon Ch. 3, Remark 1.8(1)): if `T` is the approximate tangent
space of `M` at `y` with respect to `θ` (Def. 1.7), `C ⊆ M`, `θ|C` is continuous at `y` and
`θ Hⁿ⌞(M ∖ C)` has `n`-density `0` at `y`, then `T` is the approximate tangent space of `C` at `y`
(Def. 1.4).  For `φ ∈ C_c(ℝ^Q)` and small `t > 0`,
`θ(y) t⁻ⁿ ∫_C φ(η_t) = t⁻ⁿ ∫_M φ(η_t) θ - t⁻ⁿ ∫_C φ(η_t) (θ - θ(y)) - t⁻ⁿ ∫_{M∖C} φ(η_t) θ`,
where the first term tends to `θ(y) ∫_T φ` and the other two tend to `0`. -/
theorem Submission.imc_wte_approxTangent_of_weightedTangent : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∀ x ∈ M, 0 ≤ θ x) → 0 < θ y → HasWeightedApproximateTangentSpaceAt n M θ y T → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ContinuousWithinAt θ C y → Tendsto (fun ρ : ℝ => (∫⁻ x in (M \ C) ∩ closedBall y ρ, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C y T := by
  intro Q n M C θ y T hM hC hCM hθ hθy hW hr hθC hdens
  -- Step 2: `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all small `ρ > 0`.
  have hK := Submission.imc_wte_density_bound_of_weightedTangent Q n M C θ y T hM hC hCM hθ hθy
    hW hr hθC
  -- Step 1: `dim T = n`; fix `φ ∈ C_c(ℝ^Q)`.
  refine ⟨hW.1, fun φ => ?_⟩
  -- Step 3: `a(t) = t⁻ⁿ ∫_M φ(η_t) θ → θ(y) ∫_T φ`, since `y + t η_t(x) = x`.
  have ha : Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in M,
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)))
      (𝓝[>] 0) (𝓝 (θ y * ∫ z in (T : Set (Eucl Q)), φ z ∂(μHE[n] : Measure (Eucl Q)))) := by
    refine (hW.2 φ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hη : ∀ x, y + t • Poincare.SimonGMT.Chapter03.blowUpMap y t x = x := fun x => by
      rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ (ne_of_gt ht), add_sub_cancel]
    have h := Submission.lpf_wtc_blowup_setIntegral_image Q n y t M
      (fun z => φ z * θ (y + t • z)) ht
    simp only [hη] at h
    exact h
  -- Steps 4–5: the continuity error on `C` and the remainder on `M ∖ C` vanish.
  have hb := Submission.lpf_wtc_wtt_continuity_error_vanishes Q n C θ y φ hC hθC hK
  have hc := Submission.lpf_wtc_wtt_remainder_vanishes Q n (M \ C) θ y φ (hM.diff hC)
    (fun x hx => hθ x hx.1) hdens
  -- Steps 6–7: `t⁻ⁿ ∫_C φ(η_t) = θ(y)⁻¹ (a(t) - b(t) - c(t)) → ∫_T φ`.
  have hm := ((ha.sub hb).sub hc).const_mul (θ y)⁻¹
  rw [sub_zero, sub_zero, ← mul_assoc, inv_mul_cancel₀ hθy.ne', one_mul] at hm
  -- Step 8: back to the blow-ups `η_t(C)`.
  refine hm.congr' ?_
  filter_upwards [Submission.lpf_wtc_wtt_blowup_integral_split Q n M C θ y φ hM hC hCM hr,
    self_mem_nhdsWithin] with t hsplit ht
  rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t C φ ht, hsplit]
  field_simp
  ring
/-- Upper Density Theorem on `ℝ^Q` (Simon Ch. 1, 3.6, localized as in Remark 3.7(2)) for
`ν = (Hⁿ ⌞ S).withDensity g`: if `∫⁻_{S ∩ K} g dHⁿ < ∞` for every compact `K`, then
`ν(B̄_ρ(y)) / ρⁿ → 0` as `ρ → 0+` for `Hⁿ`-a.e. `y ∉ S`. -/
theorem Submission.imc_ae_zero_density_off_set :
    ∀ (Q n : ℕ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ≥0∞), NullMeasurableSet S (μHE[n] : Measure (Eucl Q)) → (∀ K : Set (Eucl Q), IsCompact K → ∫⁻ x in S ∩ K, g x ∂(μHE[n] : Measure (Eucl Q)) < ∞) → ∀ᵐ y ∂(μHE[n] : Measure (Eucl Q)), y ∉ S → Tendsto (fun ρ : ℝ => (∫⁻ x in S ∩ closedBall y ρ, g x ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
  intro Q n S g hS hfin
  set μ : Measure (Eucl Q) := μHE[n] with hμ
  -- Step 1: `ν = (μ ⌞ S).withDensity g`, so `ν B = ∫⁻_{S ∩ B} g dμ` for Borel `B`.
  set ν : Measure (Eucl Q) := (μ.restrict S).withDensity g with hν
  have hνB : ∀ B : Set (Eucl Q), MeasurableSet B → ν B = ∫⁻ x in S ∩ B, g x ∂μ := by
    intro B hB
    rw [hν, withDensity_apply _ hB, Measure.restrict_restrict hB, inter_comm B S]
  -- Step 2: the Borel hull `A ⊇ S` of `S`; `ν` does not charge `Aᶜ`.
  set A : Set (Eucl Q) := toMeasurable μ S
  have hAm : MeasurableSet A := measurableSet_toMeasurable μ S
  have hνA : ν Aᶜ = 0 := by
    rw [hνB _ hAm.compl,
      (disjoint_compl_right_iff_subset.mpr (subset_toMeasurable μ S)).inter_eq,
      Measure.restrict_empty, lintegral_zero_measure]
  -- `diam B̄_s(c) ≤ 2s`.
  have hdiam : ∀ (c : Eucl Q) (s : ℝ), ediam (closedBall c s) ≤ ENNReal.ofReal (2 * s) :=
    fun c s => ediam_le_of_forall_dist_le fun y hy z hz => by
      have := dist_triangle_right y z c
      rw [mem_closedBall] at hy hz
      linarith
  -- Step 3 (Upper Density Theorem, Simon Ch. 1, 3.6): for a finite `m` with `m Aᶜ = 0`, the
  -- points `y ∉ A` of upper density `> ε` form an `Hⁿ`-null set.  Proof: a closed `C ⊆ A`
  -- with `m (A \ C) < k⁻¹`, then a Vitali 5r-covering by disjoint balls of radius `< 1/(k+1)`
  -- missing `C`, whose total `ρⁿ`-cost is at most `k⁻¹ / ε`.
  have hcore : ∀ m : Measure (Eucl Q), m univ ≠ ∞ → m Aᶜ = 0 → ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ∞ →
      μH[n] {y | y ∉ A ∧ ∀ δ > 0, ∃ ρ ∈ Ioo 0 δ,
        ε * ENNReal.ofReal ρ ^ n < m (closedBall y ρ)} = 0 := by
    intro m hm hmA ε hε0 hεtop
    set Z := {y | y ∉ A ∧ ∀ δ > 0, ∃ ρ ∈ Ioo 0 δ,
      ε * ENNReal.ofReal ρ ^ n < m (closedBall y ρ)}
    have : IsFiniteMeasure m := ⟨lt_top_iff_ne_top.mpr hm⟩
    have hstep : ∀ k : ℕ, ∃ u : Set (Eucl Q × ℝ), u.Countable ∧
        (∀ b ∈ u, b.2 ∈ Ioo 0 (1 / ((k : ℝ) + 1))) ∧
        Z ⊆ ⋃ b ∈ u, closedBall b.1 (5 * b.2) ∧
        ε * ∑' b : u, ENNReal.ofReal b.1.2 ^ n ≤ (k : ℝ≥0∞)⁻¹ := by
      intro k
      obtain ⟨C, hCA, hCc, hCm⟩ := hAm.exists_isClosed_sdiff_lt (μ := m) (measure_ne_top m A)
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k))
      let t : Set (Eucl Q × ℝ) := {b | b.1 ∈ Z ∧ b.2 ∈ Ioo 0 (1 / ((k : ℝ) + 1)) ∧
        closedBall b.1 b.2 ⊆ Cᶜ ∧ ε * ENNReal.ofReal b.2 ^ n < m (closedBall b.1 b.2)}
      obtain ⟨u, hut, hudisj, hucov⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall t Prod.fst Prod.snd
          (1 / ((k : ℝ) + 1)) (fun b hb => hb.2.1.2.le) 5 (by norm_num)
      have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb =>
        (nonempty_ball.mpr (hut hb).2.1.1).mono ball_subset_interior_closedBall
      refine ⟨u, hucount, fun b hb => (hut hb).2.1, ?_, ?_⟩
      · -- each `y ∈ Z` lies outside the closed `C ⊆ A`, so it centers small good balls `⊆ Cᶜ`
        intro y hy
        obtain ⟨δ₀, hδ₀, hδ₀C⟩ := Metric.isOpen_iff.mp hCc.isOpen_compl y fun h => hy.1 (hCA h)
        obtain ⟨ρ, hρ, hρm⟩ := hy.2 (min δ₀ (1 / ((k : ℝ) + 1))) (by positivity)
        have hρC : closedBall y ρ ⊆ Cᶜ :=
          (closedBall_subset_ball (hρ.2.trans_le (min_le_left _ _))).trans hδ₀C
        obtain ⟨b, hbu, hb⟩ :=
          hucov (y, ρ) ⟨hy, ⟨hρ.1, hρ.2.trans_le (min_le_right _ _)⟩, hρC, hρm⟩
        exact mem_iUnion₂.mpr ⟨b, hbu, hb (mem_closedBall_self hρ.1.le)⟩
      · have := hucount.to_subtype
        calc ε * ∑' b : u, ENNReal.ofReal b.1.2 ^ n
            = ∑' b : u, ε * ENNReal.ofReal b.1.2 ^ n := ENNReal.tsum_mul_left.symm
          _ ≤ ∑' b : u, m (closedBall b.1.1 b.1.2 ∩ Cᶜ) := ENNReal.tsum_le_tsum fun b => by
              rw [inter_eq_left.mpr (hut b.2).2.2.1]
              exact (hut b.2).2.2.2.le
          _ = m (⋃ b : u, closedBall b.1.1 b.1.2 ∩ Cᶜ) := (measure_iUnion
              (fun i j hij => (hudisj i.2 j.2 (Subtype.coe_ne_coe.mpr hij)).mono
                inter_subset_left inter_subset_left)
              (fun _ => measurableSet_closedBall.inter hCc.isOpen_compl.measurableSet)).symm
          _ ≤ m Cᶜ := measure_mono (iUnion_subset fun _ => inter_subset_right)
          _ ≤ m ((A \ C) ∪ Aᶜ) := measure_mono fun x hx => by
              by_cases h : x ∈ A
              exacts [Or.inl ⟨h, hx⟩, Or.inr h]
          _ ≤ m (A \ C) + m Aᶜ := measure_union_le _ _
          _ ≤ (k : ℝ≥0∞)⁻¹ := by
              rw [hmA, add_zero]
              exact hCm.le
    choose u hucount hurad hucov husum using hstep
    have : ∀ k, Countable (u k) := fun k => (hucount k).to_subtype
    refine le_antisymm ?_ bot_le
    calc μH[n] Z ≤ liminf (fun k => ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ))
          atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) Z
            (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) ?_
            (fun k (b : u k) => closedBall b.1.1 (5 * b.1.2)) ?_ ?_
          · simpa using ENNReal.tendsto_ofReal
              ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10)
          · refine Eventually.of_forall fun k b => (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
            have := (hurad k b.1 b.2).2
            linarith
          · refine Eventually.of_forall fun k y hy => ?_
            obtain ⟨b, hbu, hb⟩ := mem_iUnion₂.mp (hucov k hy)
            exact mem_iUnion.mpr ⟨⟨b, hbu⟩, hb⟩
      _ ≤ liminf (fun k : ℕ => 10 ^ n * ((k : ℝ≥0∞)⁻¹ / ε)) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
          calc ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)
              ≤ ∑' b : u k, 10 ^ n * ENNReal.ofReal b.1.2 ^ n :=
                ENNReal.tsum_le_tsum fun b => by
                  rw [ENNReal.rpow_natCast, ← mul_pow]
                  gcongr
                  refine (hdiam _ _).trans ?_
                  rw [← ENNReal.ofReal_ofNat 10, ← ENNReal.ofReal_mul (by norm_num)]
                  exact ENNReal.ofReal_le_ofReal (by linarith)
            _ = 10 ^ n * ∑' b : u k, ENNReal.ofReal b.1.2 ^ n := ENNReal.tsum_mul_left
            _ ≤ 10 ^ n * ((k : ℝ≥0∞)⁻¹ / ε) := by
                gcongr
                rw [ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop), mul_comm]
                exact husum k
      _ = 0 := by
          refine Tendsto.liminf_eq ?_
          simpa using ENNReal.Tendsto.const_mul
            (ENNReal.Tendsto.div_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hε0))
            (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
  -- Step 4 (Simon Ch. 1, Remark 3.7(2)): localize to the compact balls `B̄_{2/3}(x)` (finite
  -- `ν`-mass) around each point `x` of the exceptional set, and use `μHE[n] = c • μH[n]`.
  have hmain : ∀ᵐ y ∂μ, y ∉ A →
      Tendsto (fun ρ : ℝ => ν (closedBall y ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    rw [ae_iff]
    apply measure_null_of_locally_null
    intro x _
    set m := ν.restrict (closedBall x (2 / 3)) with hm_def
    have hm : m univ ≠ ∞ := by
      rw [hm_def, Measure.restrict_apply_univ, hνB _ measurableSet_closedBall]
      exact (hfin _ (isCompact_closedBall x _)).ne
    have hmA : m Aᶜ = 0 := by
      rw [hm_def, Measure.restrict_apply hAm.compl]
      exact measure_mono_null inter_subset_left hνA
    have hr : (0 : ℝ) < 1 / 3 := by norm_num
    refine ⟨_ ∩ ball x (1 / 3), inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
    rw [hμ, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    refine (congrArg _ (measure_mono_null ?_ (measure_iUnion_null fun k : ℕ =>
      hcore m hm hmA ((k : ℝ≥0∞) + 1)⁻¹ (by simp) (by simp)))).trans (smul_zero _)
    -- a non-tending quotient exceeds some `(k + 1)⁻¹` at arbitrarily small radii
    rintro y ⟨hy, hyx⟩
    simp only [mem_ofPred_eq, not_imp] at hy
    obtain ⟨hyA, hyT⟩ := hy
    rw [ENNReal.tendsto_nhds_zero] at hyT
    push Not at hyT
    obtain ⟨ε, hε, hfreq⟩ := hyT
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.mpr ⟨k, hyA, fun δ hδ => ?_⟩
    obtain ⟨ρ, hρf, hρ⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hδ hr))).exists
    refine ⟨ρ, ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩, ?_⟩
    have hsub : closedBall y ρ ⊆ closedBall x (2 / 3) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      rw [mem_ball] at hyx
      linarith [dist_triangle z y x, hρ.2.trans_le (min_le_right δ (1 / 3))]
    rw [hm_def, Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hsub,
      ← ENNReal.ofReal_pow hρ.1.le]
    refine ENNReal.mul_lt_of_lt_div (lt_of_le_of_lt ?_ hρf)
    exact (ENNReal.inv_le_inv.mpr (by simp)).trans hk.le
  -- Step 5: transfer from the hull `A` back to `S` (they agree `μ`-a.e.).
  filter_upwards [hmain, hS.toMeasurable_ae_eq] with y hy hyA hyS
  refine (hy fun h => hyS (hyA ▸ h)).congr fun ρ => ?_
  rw [hνB _ measurableSet_closedBall]
/-- Change of variables for `Hⁿ`-integrals over blow-ups: `η = η_{y,r}`, `η(x) = r⁻¹(x − y)`,
pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so `∫_{η(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η dHⁿ` for every set
`S` and every `g` (both sides are Bochner set integrals). -/
theorem Submission.lpf_wtc_blowup_setIntegral_image :
    ∀ (Q n : ℕ) (y : Eucl Q) (r : ℝ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ), 0 < r →
      ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, g z ∂(μHE[n] : Measure (Eucl Q)) =
        (r ^ n)⁻¹ * ∫ x in S, g (Poincare.SimonGMT.Chapter03.blowUpMap y r x)
          ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n y r S g hr
  -- `η = blowUpMap y r`, `η x = r⁻¹ • (x - y)`, is a homeomorphism of `ℝ^Q`.
  let e : Eucl Q ≃ₜ Eucl Q :=
    (Homeomorph.addRight (-y)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl Q → Eucl Q) = Poincare.SimonGMT.Chapter03.blowUpMap y r := by
    funext x
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = y + r • B`.
  have hmp : MeasurePreserving (Poincare.SimonGMT.Chapter03.blowUpMap y r)
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl Q))) μHE[n] := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap y r ⁻¹' B =
        (fun z => y + z) '' ((fun z => r • z) '' B) := by
      ext x
      simp only [mem_preimage, mem_image, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · intro hx
        exact ⟨r • r⁻¹ • (x - y), ⟨r⁻¹ • (x - y), hx, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left y), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Locality of approximate tangent spaces (Simon Ch. 3, Def. 1.4): if `E ⊆ E'` are
`Hᵏ`-null-measurable and `Hᵏ(E' ∩ K) < ∞` for every compact `K`, then for `Hᵏ`-a.e. `x ∈ E`
and every subspace `Q`, `Q` is the approximate tangent space of `E` at `x` iff it is that of
`E'` at `x`.  By the Upper Density Theorem `Hᵏ((E' \ E) ∩ B̄_ρ(x)) = o(ρᵏ)` at such `x`, and by
the dilation identity the blow-up integrals of `E` and `E'` then differ by `o(1)`. -/
theorem Submission.imc_approxTangent_iff_of_subset :
    ∀ (N k : ℕ) (E E' : Set (Eucl N)), E ⊆ E' → NullMeasurableSet E (μHE[k] : Measure (Eucl N)) →
      NullMeasurableSet E' (μHE[k] : Measure (Eucl N)) →
      (∀ K : Set (Eucl N), IsCompact K → (μHE[k] : Measure (Eucl N)) (E' ∩ K) < ∞) →
      ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N),
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E x Q ↔
          Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E' x Q := by
  intro N k E E' hEE' hE hE' hfin
  -- Step 1: `Hᵏ((E' \ E) ∩ B̄_ρ(x)) / ρᵏ → 0` as `ρ → 0+`, for `Hᵏ`-a.e. `x ∈ E`.
  have hS : NullMeasurableSet (E' \ E) (μHE[k] : Measure (Eucl N)) := hE'.diff hE
  have hSfin : ∀ K : Set (Eucl N), IsCompact K →
      ∫⁻ _ in (E' \ E) ∩ K, (1 : ℝ≥0∞) ∂(μHE[k] : Measure (Eucl N)) < ∞ := by
    intro K hK
    rw [setLIntegral_one]
    exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hfin K hK)
  filter_upwards [ae_restrict_of_ae
      (Submission.imc_ae_zero_density_off_set N k (E' \ E) (fun _ => 1) hS hSfin),
    ae_restrict_mem₀ hE] with x hx hxE Q
  have hdens := hx fun h => h.2 hxE
  simp only [setLIntegral_one] at hdens
  -- Steps 2–3: for every `f ∈ C_c(ℝᴺ)` the blow-up integrals of `E'` and `E` differ by `o(1)`.
  have key : ∀ f : CompactlySupportedContinuousMap (Eucl N) ℝ, Tendsto (fun r : ℝ =>
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E', f y ∂(μHE[k] : Measure (Eucl N))) -
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E, f y ∂(μHE[k] : Measure (Eucl N)))
      (𝓝[>] 0) (𝓝 0) := by
    intro f
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    obtain ⟨R, hR, hRf⟩ :=
      f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Eucl N)
    -- `f ∘ η_{x,r}` vanishes off `B̄_{Rr}(x)`.
    have hvan : ∀ r : ℝ, 0 < r → ∀ z, z ∉ closedBall x (R * r) →
        f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
      intro r hr z hz
      by_contra hne
      have hmem := hRf (subset_tsupport f hne)
      rw [mem_closedBall, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr] at hmem
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      linarith [mul_comm R r]
    -- For `r > 0`: `|I_{E'}(r) - I_E(r)| ≤ C Rᵏ Hᵏ((E' \ E) ∩ B̄_{Rr}(x)) / (Rr)ᵏ`.
    have hbound : ∀ r : ℝ, 0 < r →
        ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E', f y
            ∂(μHE[k] : Measure (Eucl N))) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E, f y
            ∂(μHE[k] : Measure (Eucl N))‖ ≤
        C * R ^ k * ((μHE[k] : Measure (Eucl N)) ((E' \ E) ∩ closedBall x (R * r)) /
          ENNReal.ofReal ((R * r) ^ k)).toReal := by
      intro r hr
      have hcont : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) := by
        refine f.continuous.comp ?_
        unfold Poincare.SimonGMT.Chapter03.blowUpMap
        fun_prop
      -- `f ∘ η_{x,r}` is continuous with compact support, and `Hᵏ ⌞ E'` is finite on compacts.
      have hint : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) E'
          (μHE[k] : Measure (Eucl N)) := by
        have : IsFiniteMeasureOnCompacts ((μHE[k] : Measure (Eucl N)).restrict E') := by
          refine ⟨fun K hK => ?_⟩
          rw [Measure.restrict_apply hK.measurableSet, inter_comm]
          exact hfin K hK
        exact hcont.integrable_of_hasCompactSupport
          (HasCompactSupport.intro (isCompact_closedBall x (R * r)) (hvan r hr))
      have hsplit : (∫ z in E', f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[k] : Measure (Eucl N))) -
          ∫ z in E, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[k] : Measure (Eucl N)) =
          ∫ z in (E' \ E) ∩ closedBall x (R * r), f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[k] : Measure (Eucl N)) := by
        rw [← setIntegral_sdiff₀ hE hint hEE']
        exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hS inter_subset_left
          (Eventually.of_forall fun z hz => hvan r hr z fun h => hz.2 ⟨hz.1, h⟩)
      have hfinB : (μHE[k] : Measure (Eucl N)) ((E' \ E) ∩ closedBall x (R * r)) < ∞ :=
        (measure_mono (inter_subset_inter_left _ sdiff_subset)).trans_lt
          (hfin _ (isCompact_closedBall x (R * r)))
      rw [Submission.lpf_wtc_blowup_setIntegral_image N k x r E' f hr,
        Submission.lpf_wtc_blowup_setIntegral_image N k x r E f hr, ← mul_sub, hsplit, norm_mul,
        norm_inv, norm_pow, Real.norm_of_nonneg hr.le, ENNReal.toReal_div,
        ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
      calc (r ^ k)⁻¹ * ‖∫ z in (E' \ E) ∩ closedBall x (R * r),
            f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[k] : Measure (Eucl N))‖
          ≤ (r ^ k)⁻¹ *
              (C * (μHE[k] : Measure (Eucl N)).real ((E' \ E) ∩ closedBall x (R * r))) :=
            mul_le_mul_of_nonneg_left
              (norm_setIntegral_le_of_norm_le_const hfinB fun z _ => hC _) (by positivity)
        _ = C * R ^ k * ((μHE[k] : Measure (Eucl N)).real ((E' \ E) ∩ closedBall x (R * r)) /
              (R * r) ^ k) := by
            rw [mul_pow]
            field_simp
    -- `ρ = R r → 0+` as `r → 0+`, so the bound tends to `0` by Step 1.
    have hlin : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hR hr
    have hlim := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hdens.comp hlin)).const_mul (C * R ^ k)
    rw [ENNReal.toReal_zero, mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with r hr using hbound r hr
  -- Step 4: the blow-up integrals of `E` and `E'` have the same limits.
  constructor
  · rintro ⟨hdim, hlim⟩
    exact ⟨hdim, fun f => by simpa using (hlim f).add (key f)⟩
  · rintro ⟨hdim, hlim⟩
    exact ⟨hdim, fun f => by simpa using (hlim f).sub (key f)⟩
/-- Lusin decomposition (Simon Ch. 3, Remark 1.8(1)): a positive weight `θ`, `Hⁿ`-integrable on
`M ∩ K` for compact `K ⊆ V`, is continuous on countably many compact pieces `C k ⊆ M` of finite
`Hⁿ`-measure which cover `M` up to an `Hⁿ`-null set. -/
theorem Submission.lpf_wtc_lusin_compact_pieces :
    ∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ), IsOpen V → M ⊆ V →
      NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
        IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) →
      ∃ C : ℕ → Set (Eucl Q), (∀ k, IsCompact (C k)) ∧ (∀ k, C k ⊆ M) ∧
        (∀ k, ContinuousOn θ (C k)) ∧ (∀ k, (μHE[n] : Measure (Eucl Q)) (C k) < ∞) ∧
        (μHE[n] : Measure (Eucl Q)) (M \ ⋃ k, C k) = 0 := by
  intro Q n V M θ hV hMV hM hθ hint
  set μ : Measure (Eucl Q) := μHE[n]
  -- Compact sets `K i = F i ∩ closedBall 0 i ⊆ V` covering `V`.
  obtain ⟨F, hFc, hFV, hFU, hFmono⟩ := hV.exists_iUnion_isClosed
  set K : ℕ → Set (Eucl Q) := fun i => F i ∩ closedBall 0 i
  have hKc : ∀ i, IsCompact (K i) := fun i => (isCompact_closedBall 0 (i : ℝ)).inter_left (hFc i)
  have hKV : ∀ i, K i ⊆ V := fun i => inter_subset_left.trans (hFV i)
  have hcover : ∀ x ∈ V, ∃ i, x ∈ K i := by
    intro x hx
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    exact ⟨max i j, hFmono (le_max_left i j) hi,
      mem_closedBall_zero_iff.2 (hj.trans (Nat.cast_le.2 (le_max_right i j)))⟩
  -- Lusin's theorem for a Borel set `E` of finite measure and a Borel function `g`.
  have lusin : ∀ (E : Set (Eucl Q)) (g : Eucl Q → ℝ), MeasurableSet E → μ E ≠ ∞ → Measurable g →
      ∃ G : ℕ → Set (Eucl Q), (∀ l, IsClosed (G l)) ∧ (∀ l, G l ⊆ E) ∧
        (∀ l, ContinuousOn g (G l)) ∧ μ (E \ ⋃ l, G l) = 0 := by
    intro E g hE hμE hg
    have : IsFiniteMeasure (μ.restrict E) := isFiniteMeasure_restrict.2 hμE
    -- A measurable `S` is relatively open in some closed `H ⊆ E` with `μ (E \ H) < δ`.
    have step : ∀ S : Set (Eucl Q), MeasurableSet S → ∀ δ : ℝ≥0∞, δ ≠ 0 →
        ∃ H, IsClosed H ∧ H ⊆ E ∧ μ (E \ H) < δ ∧ ∃ O, IsOpen O ∧ S ∩ H = O ∩ H := by
      intro S hS δ hδ
      have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
      obtain ⟨H₁, hH₁S, hH₁c, hH₁⟩ :=
        (hE.inter hS).exists_isClosed_sdiff_lt (μ := μ.restrict E) (measure_ne_top _ _) hδ2
      obtain ⟨H₂, hH₂S, hH₂c, hH₂⟩ :=
        (hE.diff hS).exists_isClosed_sdiff_lt (μ := μ.restrict E) (measure_ne_top _ _) hδ2
      refine ⟨H₁ ∪ H₂, hH₁c.union hH₂c,
        union_subset (hH₁S.trans inter_subset_left) (hH₂S.trans sdiff_subset), ?_,
        H₂ᶜ, hH₂c.isOpen_compl, ?_⟩
      · calc μ (E \ (H₁ ∪ H₂)) ≤ μ ((E ∩ S) \ H₁ ∪ (E \ S) \ H₂) := by
              refine measure_mono fun x hx => ?_
              by_cases hxS : x ∈ S
              · exact Or.inl ⟨⟨hx.1, hxS⟩, fun h => hx.2 (Or.inl h)⟩
              · exact Or.inr ⟨⟨hx.1, hxS⟩, fun h => hx.2 (Or.inr h)⟩
          _ ≤ μ ((E ∩ S) \ H₁) + μ ((E \ S) \ H₂) := measure_union_le _ _
          _ = μ.restrict E ((E ∩ S) \ H₁) + μ.restrict E ((E \ S) \ H₂) := by
              rw [Measure.restrict_eq_self _ (sdiff_subset.trans inter_subset_left),
                Measure.restrict_eq_self _ (sdiff_subset.trans sdiff_subset)]
          _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hH₁ hH₂
          _ = δ := ENNReal.add_halves δ
      · ext x
        constructor
        · rintro ⟨hxS, hxH⟩
          exact ⟨fun h => (hH₂S h).2 hxS, hxH⟩
        · rintro ⟨hxO, hxH | hxH⟩
          · exact ⟨(hH₁S hxH).2, Or.inl hxH⟩
          · exact absurd hxH hxO
    -- Doing this for `g⁻¹(q, ∞)` and `g⁻¹(-∞, q)`, `q ∈ ℚ`, makes `g` continuous on `⋂ H`.
    have piece : ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ H, IsClosed H ∧ H ⊆ E ∧ μ (E \ H) < ε ∧ ContinuousOn g H := by
      intro ε hε
      obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × Bool)
      set S : ℚ × Bool → Set (Eucl Q) := fun p =>
        bif p.2 then g ⁻¹' Ioi (p.1 : ℝ) else g ⁻¹' Iio (p.1 : ℝ)
      have hS : ∀ p, MeasurableSet (S p) := by
        rintro ⟨q, b⟩
        cases b
        · exact hg measurableSet_Iio
        · exact hg measurableSet_Ioi
      choose H hHc hHE hHμ O hOo hSO using fun p =>
        step (S p) (hS p) (δ p) (ENNReal.coe_ne_zero.2 (hδpos p).ne')
      refine ⟨⋂ p, H p, isClosed_iInter hHc, (iInter_subset _ (0, true)).trans (hHE _), ?_, ?_⟩
      · calc μ (E \ ⋂ p, H p) = μ (⋃ p, E \ H p) := by rw [sdiff_iInter]
          _ ≤ ∑' p, μ (E \ H p) := measure_iUnion_le _
          _ ≤ ∑' p, (δ p : ℝ≥0∞) := ENNReal.tsum_le_tsum fun p => (hHμ p).le
          _ < ε := hδsum
      · intro x hx
        have hxH : ∀ p, x ∈ H p := mem_iInter.1 hx
        have key : ∀ p, x ∈ S p → ∀ᶠ y in 𝓝[⋂ p, H p] x, y ∈ S p := by
          intro p hxp
          have hxO : x ∈ O p := ((hSO p).subset ⟨hxp, hxH p⟩).1
          filter_upwards [mem_nhdsWithin_of_mem_nhds ((hOo p).mem_nhds hxO),
            self_mem_nhdsWithin] with y hyO hyH
          exact ((hSO p).symm.subset ⟨hyO, mem_iInter.1 hyH p⟩).1
        refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
        · obtain ⟨q, haq, hqx⟩ := exists_rat_btwn ha
          filter_upwards [key (q, true) hqx] with y hy
          exact haq.trans hy
        · obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn hb
          filter_upwards [key (q, false) hxq] with y hy
          exact lt_trans hy hqb
    choose G hGc hGE hGμ hGcont using fun l : ℕ =>
      piece ((l : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top l))
    refine ⟨G, hGc, hGE, hGcont, ?_⟩
    by_contra h
    obtain ⟨l, hl⟩ := ENNReal.exists_inv_nat_lt h
    exact lt_asymm (hl.trans_le (measure_mono (sdiff_subset_sdiff_right (subset_iUnion G l))))
      (hGμ l)
  -- A Borel representative `g` of `θ` on `M`, and a Borel core `B ⊆ M` on which `θ = g`.
  have hMU : M = ⋃ i, M ∩ K i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hx => (hcover x (hMV hx)).imp fun i hi => ⟨hx, hi⟩, fun ⟨_, hx, _⟩ => hx⟩
  have hθm : AEMeasurable θ (μ.restrict M) := by
    rw [hMU]
    exact aemeasurable_iUnion_iff.2 fun i => Integrable.aemeasurable (hint (K i) (hKc i) (hKV i))
  set g := hθm.mk θ
  have hg : Measurable g := hθm.measurable_mk
  have hbad : μ {x | ¬(x ∈ M → θ x = g x)} = 0 := ae_iff.1 ((ae_restrict_iff'₀ hM).1 hθm.ae_eq_mk)
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null hbad
  obtain ⟨B₀, hB₀M, hB₀m, hB₀ae⟩ := hM.exists_measurable_subset_ae_eq
  set B := B₀ \ Z
  have hBm : MeasurableSet B := hB₀m.diff hZm
  have hBM : B ⊆ M := sdiff_subset.trans hB₀M
  have hθgB : ∀ x ∈ B, θ x = g x := fun x hx => by
    by_contra h
    exact hx.2 (hZsub fun hh => h (hh (hBM hx)))
  have hMB : μ (M \ B) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null (ae_eq_set.1 hB₀ae).2 hZ0)
    by_cases hxB₀ : x ∈ B₀
    · exact Or.inr (by_contra fun hz => hx.2 ⟨hxB₀, hz⟩)
    · exact Or.inl ⟨hx.1, hxB₀⟩
  -- Borel pieces `E i j = B ∩ K i ∩ {g > 1/(j+1)}` of finite measure.
  set E : ℕ → ℕ → Set (Eucl Q) := fun i j => B ∩ K i ∩ g ⁻¹' Ioi ((j : ℝ) + 1)⁻¹
  have hEm : ∀ i j, MeasurableSet (E i j) := fun i j =>
    (hBm.inter (hKc i).isClosed.measurableSet).inter (hg measurableSet_Ioi)
  have hEfin : ∀ i j, μ (E i j) ≠ ∞ := by
    intro i j htop
    have hc : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hle : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ * μ (E i j) ≤ ∫⁻ x in M ∩ K i, ‖θ x‖ₑ ∂μ :=
      calc ENNReal.ofReal ((j : ℝ) + 1)⁻¹ * μ (E i j)
          = ∫⁻ _ in E i j, ENNReal.ofReal ((j : ℝ) + 1)⁻¹ ∂μ := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in E i j, ‖θ x‖ₑ ∂μ := setLIntegral_mono' (hEm i j) fun x hx => by
            rw [Real.enorm_eq_ofReal_abs, hθgB x hx.1.1]
            exact ENNReal.ofReal_le_ofReal (hx.2.le.trans (le_abs_self _))
        _ ≤ ∫⁻ x in M ∩ K i, ‖θ x‖ₑ ∂μ :=
            lintegral_mono_set fun x hx => ⟨hBM hx.1.1, hx.1.2⟩
    have hlt := hle.trans_lt (hint (K i) (hKc i) (hKV i)).2
    rw [htop, ENNReal.mul_top hc] at hlt
    exact lt_irrefl _ hlt
  -- Lusin on each `E i j`; the pieces, enumerated by `Nat.unpair`, are the `C k`.
  choose G hGc hGE hGcont hGnull using fun i j => lusin (E i j) g (hEm i j) (hEfin i j) hg
  refine ⟨fun k => G k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2, fun k => ?_, fun k => ?_,
    fun k => ?_, fun k => ?_, ?_⟩
  · exact (hKc _).of_isClosed_subset (hGc _ _ _)
      ((hGE _ _ _).trans (inter_subset_left.trans inter_subset_right))
  · exact (hGE _ _ _).trans (inter_subset_left.trans (inter_subset_left.trans hBM))
  · exact (hGcont _ _ _).congr fun x hx => hθgB x ((hGE _ _ _) hx).1.1
  · exact (measure_mono (hGE _ _ _)).trans_lt (lt_top_iff_ne_top.2 (hEfin _ _))
  · refine measure_mono_null (fun x hx => ?_) (measure_union_null hMB
      (measure_iUnion_null fun i => measure_iUnion_null fun j => hGnull i j))
    obtain ⟨hxM, hxC⟩ := hx
    by_cases hxB : x ∈ B
    · right
      obtain ⟨i, hi⟩ := hcover x (hMV hxM)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt ((hθgB x hxB) ▸ hθ x hxM)
      refine mem_iUnion₂.2 ⟨i, j, ⟨⟨hxB, hi⟩, by simpa [one_div] using hj⟩, fun hxG => hxC ?_⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hxG
      exact mem_iUnion.2 ⟨Nat.pair i (Nat.pair j l), by simpa [Nat.unpair_pair] using hl⟩
    · exact Or.inl ⟨hxM, hxB⟩

/-- Simon Ch. 3, Remark 1.8(1): for `Hᵏ`-a.e. `x ∈ E` and every subspace `Q`, `Q` is the
approximate tangent space of `E` at `x` with respect to `θ` (Definition 1.7) iff it is the
approximate tangent space of `E` at `x` (Definition 1.4).  Off an `Hᵏ`-null set, `x` lies in a
compact Lusin piece `C ⊆ E` on which `θ` is continuous, and both `Hᵏ ⌞ (E ∖ C)` and
`θ Hᵏ ⌞ (E ∖ C)` have `k`-density `0` at `x`.  Both tangent conditions then transfer between `E`
and `C`. -/
theorem Submission.imc_weightedTangent_iff_approxTangent : ∀ (N k : ℕ) (E : Set (Eucl N)) (θ : Eucl N → ℝ), NullMeasurableSet E (μHE[k] : Measure (Eucl N)) → (∀ K : Set (Eucl N), IsCompact K → (μHE[k] : Measure (Eucl N)) (E ∩ K) < ∞) → (∀ x ∈ E, 0 < θ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ (E ∩ K) (μHE[k] : Measure (Eucl N))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N), HasWeightedApproximateTangentSpaceAt k E θ x Q ↔ Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E x Q := by
  intro N k E θ hE hEfin hθ hθint
  -- Step 2: compact pieces `C i ⊆ E`, `θ|C i` continuous, covering `E` up to an `Hᵏ`-null set.
  obtain ⟨C, hCc, hCE, hθC, hCfin, hEC⟩ := Submission.lpf_wtc_lusin_compact_pieces N k univ E θ
    isOpen_univ (subset_univ E) hE hθ fun K hK _ => hθint K hK
  have hCm : ∀ i, NullMeasurableSet (C i) (μHE[k] : Measure (Eucl N)) := fun i =>
    (hCc i).isClosed.measurableSet.nullMeasurableSet
  have hS : ∀ i, NullMeasurableSet (E \ C i) (μHE[k] : Measure (Eucl N)) := fun i =>
    hE.diff (hCm i)
  -- Step 3: `Hᵏ ⌞ (E ∖ C i)` and `θ Hᵏ ⌞ (E ∖ C i)` have `k`-density `0` at a.e. `x ∉ E ∖ C i`.
  have hdens₁ : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl N)), x ∉ E \ C i →
      Tendsto (fun ρ : ℝ => (μHE[k] : Measure (Eucl N)) ((E \ C i) ∩ closedBall x ρ) /
        ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) := by
    intro i
    have h := Submission.imc_ae_zero_density_off_set N k (E \ C i) (fun _ => 1) (hS i)
      fun K hK => by
        simp only [setLIntegral_one]
        exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hEfin K hK)
    simpa only [setLIntegral_one] using h
  have hdens₂ : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl N)), x ∉ E \ C i →
      Tendsto (fun ρ : ℝ => (∫⁻ y in (E \ C i) ∩ closedBall x ρ, ENNReal.ofReal (θ y)
        ∂(μHE[k] : Measure (Eucl N))) / ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) := fun i =>
    Submission.imc_ae_zero_density_off_set N k (E \ C i) (fun y => ENNReal.ofReal (θ y)) (hS i)
      fun K hK => (lintegral_mono_set (inter_subset_inter_left K sdiff_subset)).trans_lt
        (hθint K hK).lintegral_lt_top
  -- `Hᵏ ⌞ E`-a.e. `x` lies in some piece `C i`.
  have hcov : ∀ᵐ x ∂(μHE[k] : Measure (Eucl N)), x ∈ E → x ∈ ⋃ i, C i :=
    measure_mono_null (fun x hx => not_imp.1 hx) hEC
  filter_upwards [ae_restrict_mem₀ hE, ae_restrict_of_ae (ae_all_iff.2 hdens₁),
    ae_restrict_of_ae (ae_all_iff.2 hdens₂), (ae_restrict_iff'₀ hE).2 hcov]
    with x hxE hx₁ hx₂ hxC Q
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxC
  have hxS : x ∉ E \ C i := fun h => h.2 hi
  -- Steps 4–7 at `x` are carried out on the piece `C i`; collect the data they need.
  have h₀ : Tendsto (fun ρ : ℝ => (μHE[k] : Measure (Eucl N)) ((C i \ E) ∩ closedBall x ρ) /
      ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) := by
    simp only [sdiff_eq_empty.2 (hCE i), empty_inter, measure_empty, ENNReal.zero_div]
    exact tendsto_const_nhds
  have hθ₀ : ∀ y ∈ E, 0 ≤ θ y := fun y hy => (hθ y hy).le
  have hCr : (μHE[k] : Measure (Eucl N)) (C i ∩ closedBall x 1) < ∞ :=
    (measure_mono inter_subset_left).trans_lt (hCfin i)
  have hr : ∃ r : ℝ, 0 < r ∧ (μHE[k] : Measure (Eucl N)) (C i ∩ closedBall x r) < ∞ ∧
      IntegrableOn θ (E ∩ closedBall x r) (μHE[k] : Measure (Eucl N)) :=
    ⟨1, one_pos, hCr, hθint _ (isCompact_closedBall x 1)⟩
  have hθx : ContinuousWithinAt θ (C i) x := (hθC i).continuousWithinAt hi
  constructor
  · -- (⇒) weighted tangent of `E` ⇒ tangent of `C i` ⇒ tangent of `E`.
    intro hw
    exact Submission.lpf_wtc_tangent_transfer N k E (C i) x Q hE (hCm i)
      (Submission.imc_wte_approxTangent_of_weightedTangent N k E (C i) θ x Q hE (hCm i) (hCE i)
        hθ₀ (hθ x hxE) hw hr hθx (hx₂ i hxS))
      ⟨1, one_pos, hCr⟩ (hx₁ i hxS) h₀
  · -- (⇐) tangent of `E` ⇒ tangent of `C i` ⇒ weighted tangent of `E`.
    intro hu
    exact Submission.lpf_wtc_weighted_tangent_transfer N k E (C i) θ x Q hE (hCm i) (hCE i) hi hθ₀
      (Submission.lpf_wtc_tangent_transfer N k (C i) E x Q (hCm i) hE hu
        ⟨1, one_pos, hEfin _ (isCompact_closedBall x 1)⟩ h₀ (hx₁ i hxS))
      hr hθx (hx₂ i hxS)
/-- Orthonormal frames of the same subspace have the same simple `n`-vector up to sign (Simon
Ch. 6, 3.1: `ξ(x) = τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM` is determined by `TₓM` up
to sign).  `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q = span τ = span τ'`.  Restricted to
`Q`, an `n`-covector `ω` is an alternating `n`-form on the `n`-dimensional space `Q`, so
`ω(τ') = b.det(b') ω(τ)` (`AlternatingMap.eq_smul_basis_det`, as in the determinant computation
after (3.4), p. 147), and `b.det(b') = ±1` because the change of basis between orthonormal bases
is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.fiw_ims_frame_sign :
    ∀ (P n : ℕ) (τ τ' : Fin n → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ τ' →
      Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') →
      simpleNVector τ' = simpleNVector τ ∨ simpleNVector τ' = -simpleNVector τ := by
  intro P n τ τ' hτ hτ' hspan
  set Q : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ)
  -- Step 1: `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`.
  let b : Module.Basis (Fin n) ℝ Q := Module.Basis.span hτ.linearIndependent
  let b' : Module.Basis (Fin n) ℝ Q :=
    (Module.Basis.span hτ'.linearIndependent).map (LinearEquiv.ofEq _ _ hspan.symm)
  have hb : Q.subtype ∘ b = τ :=
    funext fun i => Module.Basis.coe_span_apply hτ.linearIndependent i
  have hb' : Q.subtype ∘ b' = τ' := by
    funext i
    simp [b']
  have hbo : Orthonormal ℝ b := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb]
    exact hτ
  have hbo' : Orthonormal ℝ b' := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb']
    exact hτ'
  -- Step 2: the restriction `f = ω ∘ Q.subtype` of an `n`-covector `ω` is an alternating
  -- `n`-form on `Q`, so `f = f b • b.det`; evaluated at `b'` this is `ω τ' = b.det b' * ω τ`.
  have key : ∀ ω : Covector (Eucl P) n, ω τ' = b.det b' * ω τ := by
    intro ω
    have h := DFunLike.congr_fun
      ((ω.toAlternatingMap.compLinearMap Q.subtype).eq_smul_basis_det b) ⇑b'
    rw [AlternatingMap.smul_apply, smul_eq_mul] at h
    change ω (Q.subtype ∘ b') = ω (Q.subtype ∘ b) * b.det b' at h
    rw [hb, hb'] at h
    rw [h, mul_comm]
  -- Step 3: `b.det b' = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : b.det b' = 1 ∨ b.det b' = -1 := by
    simpa using (b.toOrthonormalBasis hbo).det_to_matrix_orthonormalBasis_real
      (b'.toOrthonormalBasis hbo')
  -- Step 4: extensionality, as `simpleNVector v ω = ω v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key ω, hd, one_mul]
  · right
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key ω, hd, neg_one_mul]

/-- Pointwise eventual limits of rectifiable triples are rectifiable triples (Simon Ch. 6, 3.13,
last paragraph of the proof: `ξ_Q(x) ∈ Λₙ(TₓM_Q)`, `TₓM₊ = TₓM_Q` up to small measure, hence
`ξ(x) ∈ Λₙ(TₓM₊)`).  With `θⱼ, θ₀ ≥ 1` the sets `Mⱼ`, `M₀` have locally finite `Hᵏ` measure.
`M₀` lies in `⋃ⱼ Mⱼ` up to an `Hᵏ`-null set, so it is countably rectifiable, and `ξ₀` is the
a.e. limit of `Mⱼ.indicator ξⱼ`, so it is a.e. strongly measurable.  For a.e. `x ∈ M₀ ∩ Mⱼ` a
weighted tangent space of `(Mⱼ, θⱼ)` at `x` is one of `(M₀, θ₀)`: weighted and unweighted
tangent spaces agree a.e. (Ch. 3, Remark 1.8(1); `imc_weightedTangent_iff_approxTangent`), and
the approximate tangent spaces of `Mⱼ ∩ M₀` agree a.e. with those of `Mⱼ` and of `M₀`
(`imc_approxTangent_iff_of_subset`).  At such `x`, for `j ≥ J(x)` the frames `τʲ` orienting
`ξⱼ(x)` all span the unique weighted tangent space of `(M₀, θ₀)` at `x`, so
`ξⱼ(x) ∈ {s, -s}` with `s = simpleNVector τᴶ` (`fiw_ims_frame_sign`); this set is closed, hence
contains `ξ₀(x) = lim ξⱼ(x)`. -/
theorem Submission.imc_isRectifiableTriple_of_eventually_mem :
    ∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k) (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), (∀ j, IsRectifiableTriple (univ : Set (Eucl N)) k (M j) (θ j) (ξ j)) → (∀ j, ∀ x ∈ M j, 1 ≤ θ j x) → NullMeasurableSet M₀ (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M₀, 1 ≤ θ₀ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict M₀), (∀ᶠ j in atTop, x ∈ M j) ∧ Tendsto (fun j => ξ j x) atTop (𝓝 (ξ₀ x))) → IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ := by
  have hA := Submission.imc_approxTangent_iff_of_subset
  have hB := Submission.imc_weightedTangent_iff_approxTangent
  have hFrame := Submission.fiw_ims_frame_sign
  intro N k M θ ξ M₀ θ₀ ξ₀ hTri hθ1 hM₀ hθ₀1 hθ₀int hpt
  set H : Measure (Eucl N) := (μHE[k] : Measure (Eucl N)) with hH
  -- Step 1: `ϑ ≥ 1` on `E` and `ϑ` integrable on `E ∩ K` give `H (E ∩ K) < ∞`.
  have hfinGen : ∀ (E : Set (Eucl N)) (ϑ : Eucl N → ℝ), NullMeasurableSet E H →
      (∀ x ∈ E, 1 ≤ ϑ x) → ∀ K : Set (Eucl N), IsCompact K → IntegrableOn ϑ (E ∩ K) H →
      H (E ∩ K) < ∞ := by
    intro E ϑ hE h1 K hK hint
    have hEK : NullMeasurableSet (E ∩ K) H := hE.inter hK.measurableSet.nullMeasurableSet
    calc H (E ∩ K) = ∫⁻ _x in E ∩ K, 1 ∂H := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in E ∩ K, ‖ϑ x‖ₑ ∂H := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hEK] with x hx
          have h := h1 x hx.1
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by linarith)]
          exact ENNReal.one_le_ofReal.mpr h
      _ < ∞ := hint.hasFiniteIntegral
  have hfin : ∀ j, ∀ K : Set (Eucl N), IsCompact K → H (M j ∩ K) < ∞ := fun j K hK =>
    hfinGen (M j) (θ j) (hTri j).nullMeasurableSet (hθ1 j) K hK
      ((hTri j).integrableOn K hK (subset_univ K))
  have hfin₀ : ∀ K : Set (Eucl N), IsCompact K → H (M₀ ∩ K) < ∞ := fun K hK =>
    hfinGen M₀ θ₀ hM₀ hθ₀1 K hK (hθ₀int K hK)
  -- Step 5 (i)–(iv): weighted ↔ unweighted for `(Mⱼ, θⱼ)` and `(M₀, θ₀)`, and locality of
  -- unweighted tangent spaces for `Mⱼ ∩ M₀ ⊆ Mⱼ` and `Mⱼ ∩ M₀ ⊆ M₀`.
  have hBj : ∀ j, ∀ᵐ x ∂(H.restrict (M j)), ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j) x Q := fun j =>
    hB N k (M j) (θ j) (hTri j).nullMeasurableSet (hfin j) (hTri j).pos
      (fun K hK => (hTri j).integrableOn K hK (subset_univ K))
  have hB₀ : ∀ᵐ x ∂(H.restrict M₀), ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k M₀ x Q :=
    hB N k M₀ θ₀ hM₀ hfin₀ (fun x hx => lt_of_lt_of_le one_pos (hθ₀1 x hx)) hθ₀int
  have hAj : ∀ j, ∀ᵐ x ∂(H.restrict (M j ∩ M₀)), ∀ Q : Submodule ℝ (Eucl N),
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j ∩ M₀) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j) x Q := fun j =>
    hA N k (M j ∩ M₀) (M j) inter_subset_left ((hTri j).nullMeasurableSet.inter hM₀)
      (hTri j).nullMeasurableSet (hfin j)
  have hA₀ : ∀ j, ∀ᵐ x ∂(H.restrict (M j ∩ M₀)), ∀ Q : Submodule ℝ (Eucl N),
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j ∩ M₀) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k M₀ x Q := fun j =>
    hA N k (M j ∩ M₀) M₀ inter_subset_right ((hTri j).nullMeasurableSet.inter hM₀) hM₀ hfin₀
  -- Step 5 (T_j): for `H⌞M₀`-a.e. `x ∈ Mⱼ`, weighted tangent spaces of `(Mⱼ, θⱼ)` at `x` are
  -- weighted tangent spaces of `(M₀, θ₀)`.
  have hTj : ∀ j, ∀ᵐ x ∂(H.restrict M₀), x ∈ M j → ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x Q →
        HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x Q := by
    intro j
    have hjM : NullMeasurableSet (M j ∩ M₀) H := (hTri j).nullMeasurableSet.inter hM₀
    have h1 := (ae_restrict_iff'₀ (hTri j).nullMeasurableSet).1 (hBj j)
    have h2 := (ae_restrict_iff'₀ hjM).1 (hAj j)
    have h3 := (ae_restrict_iff'₀ hjM).1 (hA₀ j)
    have h4 := (ae_restrict_iff'₀ hM₀).1 hB₀
    rw [ae_restrict_iff'₀ hM₀]
    filter_upwards [h1, h2, h3, h4] with x h1 h2 h3 h4 hx0 hxj Q hW
    exact (h4 hx0 Q).2 ((h3 ⟨hxj, hx0⟩ Q).1 ((h2 ⟨hxj, hx0⟩ Q).2 ((h1 hxj Q).1 hW)))
  -- Step 6 (O_j): the orientation of `(Mⱼ, θⱼ, ξⱼ)`, read `H⌞M₀`-a.e. on `Mⱼ`.
  have hOj : ∀ j, ∀ᵐ x ∂(H.restrict M₀), x ∈ M j → ∃ τ : Fin k → Eucl N, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x (Submodule.span ℝ (range τ)) ∧
      (ξ j x = simpleNVector τ ∨ ξ j x = -simpleNVector τ) := fun j =>
    ae_restrict_of_ae ((ae_restrict_iff'₀ (hTri j).nullMeasurableSet).1 (hTri j).orients)
  -- Step 7: orientation of the limit; `ξⱼ(x) ∈ {s, -s}` for `j ≥ J`, a closed set.
  have horients : ∀ᵐ x ∂(H.restrict M₀), ∃ τ : Fin k → Eucl N, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x (Submodule.span ℝ (range τ)) ∧
      (ξ₀ x = simpleNVector τ ∨ ξ₀ x = -simpleNVector τ) := by
    have hTall := ae_all_iff.2 hTj
    have hOall := ae_all_iff.2 hOj
    have hmem : ∀ᵐ x ∂(H.restrict M₀), x ∈ M₀ := ae_restrict_mem₀ hM₀
    filter_upwards [hpt, hTall, hOall, hmem] with x hx hT hO hxM
    obtain ⟨hev, hlim⟩ := hx
    have hθx : θ₀ x ≠ 0 := (lt_of_lt_of_le one_pos (hθ₀1 x hxM)).ne'
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    choose! τ hτon hτW hτξ using hO
    refine ⟨τ J, hτon J (hJ J le_rfl), hT J (hJ J le_rfl) _ (hτW J (hJ J le_rfl)), ?_⟩
    set s := simpleNVector (τ J) with hs
    have hmem' : ∀ᶠ j in atTop, ξ j x ∈ ({s, -s} : Set (NVector (Eucl N) k)) := by
      filter_upwards [eventually_ge_atTop J] with j hj
      have hxj : x ∈ M j := hJ j hj
      have hspan : Submodule.span ℝ (range (τ J)) = Submodule.span ℝ (range (τ j)) :=
        HasWeightedApproximateTangentSpaceAt.unique hθx
          (hT J (hJ J le_rfl) _ (hτW J (hJ J le_rfl))) (hT j hxj _ (hτW j hxj))
      have hsign := hFrame N k (τ J) (τ j) (hτon J (hJ J le_rfl)) (hτon j hxj) hspan
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hτξ j hxj with h | h <;> rcases hsign with h' | h'
      · exact Or.inl (by rw [h, h'])
      · exact Or.inr (by rw [h, h'])
      · exact Or.inr (by rw [h, h'])
      · exact Or.inl (by rw [h, h']; ext α; simp [s])
    have hcl : IsClosed ({s, -s} : Set (NVector (Eucl N) k)) := (Set.toFinite _).isClosed
    simpa using hcl.mem_of_tendsto hlim hmem'
  -- Step 3: `M₀ ⊆ (M₀ \ ⋃ⱼ Mⱼ) ∪ ⋃ⱼ Mⱼ`, the first set being `H`-null.
  have hcr : CountablyRectifiable k M₀ := by
    have hZ : H (M₀ \ ⋃ j, M j) = 0 := by
      have h : ∀ᵐ x ∂(H.restrict M₀), x ∈ ⋃ j, M j := by
        filter_upwards [hpt] with x hx
        obtain ⟨j, hj⟩ := hx.1.exists
        exact mem_iUnion.2 ⟨j, hj⟩
      rw [ae_restrict_iff'₀ hM₀, ae_iff] at h
      refine measure_mono_null (fun x hx => ?_) h
      simp only [Set.mem_ofPred_eq, not_imp]
      exact ⟨hx.1, hx.2⟩
    let S : ℕ → Set (Eucl N) := fun i => Nat.casesOn i (M₀ \ ⋃ j, M j) (fun j => M j)
    have hS : ∀ i, CountablyRectifiable k (S i) := by
      intro i
      cases i with
      | zero => exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hZ
      | succ j => exact (hTri j).countablyRectifiable
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion S hS).mono fun x hx => ?_
    by_cases h : x ∈ ⋃ j, M j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨j + 1, hj⟩
    · exact mem_iUnion.2 ⟨0, ⟨hx, h⟩⟩
  -- Step 4: `ξ₀` is the `H⌞M₀`-a.e. limit of `Mⱼ.indicator ξⱼ`.  The pseudo-metrizable
  -- structure of `NVector (Eucl N) k` is supplied by hand: its topology is
  -- `ContinuousLinearMap.topologicalSpace`, which is the operator-norm topology.
  have hmeas : AEStronglyMeasurable ξ₀ (H.restrict M₀) := by
    have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl N) k) :=
      ⟨⟨inferInstance, rfl, @EMetric.instIsCountablyGeneratedUniformity (NVector (Eucl N) k) _⟩⟩
    have hg : ∀ j, AEStronglyMeasurable ((M j).indicator (ξ j)) (H.restrict M₀) := fun j =>
      ((aestronglyMeasurable_indicator_iff₀ (hTri j).nullMeasurableSet).2
        (hTri j).aestronglyMeasurable).restrict
    refine aestronglyMeasurable_of_tendsto_ae atTop hg ?_
    filter_upwards [hpt] with x hx
    refine hx.2.congr' ?_
    filter_upwards [hx.1] with j hj
    rw [indicator_of_mem hj]
  -- Step 8: assemble the fields.
  exact { subset := subset_univ _, nullMeasurableSet := hM₀, countablyRectifiable := hcr,
          pos := fun x hx => lt_of_lt_of_le one_pos (hθ₀1 x hx),
          integrableOn := fun K hK _ => hθ₀int K hK,
          aestronglyMeasurable := hmeas, orients := horients }

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
