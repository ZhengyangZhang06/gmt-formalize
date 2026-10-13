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

/-- Simon Ch. 6, proof of 8.2 (the blow-up step): if `Q` is the weighted approximate tangent
space of `(M, θ)` at `x` (Ch. 3, 1.7), then for every continuous compactly supported `f`,
`(rⁿ)⁻¹ ∫_M θ(y) f(r⁻¹(y − x)) dHⁿ(y) → θ(x) ∫_Q f dHⁿ` as `r ↓ 0`.  The change of variables
`z = η_{x,r}(y) = r⁻¹(y − x)` turns the left side into the blow-up integral
`∫_{η_{x,r}(M)} f(z) θ(x + r z) dHⁿ(z)` of the tangent condition. -/
theorem Submission.ind_ab_rescaled_tangent_limit :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)) (f : Eucl P → ℝ), HasWeightedApproximateTangentSpaceAt n M θ x Q → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in M, θ y * f (r⁻¹ • (y - x)) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), f z ∂(μHE[n] : Measure (Eucl P)))) := by
  intro P n M θ x Q f hQ hf hfc
  -- The tangent condition, tested with `f ∈ C_c(ℝ^P)`; both sides agree for every `r > 0`.
  refine (hQ.2 ⟨⟨f, hf⟩, hfc⟩).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  -- `η = blowUpMap x r`, `η y = r⁻¹ • (y - x)`, is a homeomorphism of `ℝ^P`.
  let e : Eucl P ≃ₜ Eucl P :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl P → Eucl P) = Poincare.SimonGMT.Chapter03.blowUpMap x r := by
    funext y
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap x r) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = x + r • B`.
  have hmp : MeasurePreserving (Poincare.SimonGMT.Chapter03.blowUpMap x r)
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) μHE[n] := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' B =
        (fun z => x + z) '' ((fun z => r • z) '' B) := by
      ext y
      simp only [mem_preimage, mem_image, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · intro hy
        exact ⟨r • r⁻¹ • (y - x), ⟨r⁻¹ • (y - x), hy, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  -- Change of variables: `∫_{η(M)} g dHⁿ = (rⁿ)⁻¹ ∫_M g ∘ η dHⁿ`.
  rw [hmp.setIntegral_image_emb hemb _ M, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  -- `x + r • η y = y`.
  have hy : x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r y = y := by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hr.ne', add_sub_cancel]
  simp only [hy]
  exact mul_comm _ _

/-- Weighted ball growth at a point with a weighted approximate tangent space `Q`:
`∫_{M ∩ B̄_s(x)} θ dHⁿ ≤ C sⁿ` for all small `s > 0`.  Test the rescaled tangent limit
`(sⁿ)⁻¹ ∫_M θ(y) f₀(s⁻¹(y − x)) dHⁿ(y) → θ(x) ∫_Q f₀ dHⁿ` against the bump
`f₀(z) = max(0, min(1, 2 − ‖z‖))`, which is `1` on `B̄_1(0)` and `0` off `B̄_2(0)`. -/
theorem Submission.ind_ab_weighted_ball_growth :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)),
      NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) →
      (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))) →
      HasWeightedApproximateTangentSpaceAt n M θ x Q →
      ∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤
          C * ENNReal.ofReal (s ^ n) := by
  intro P n M θ x Q hM hθ hint hQ
  -- The bump `f₀`: continuous, `0 ≤ f₀ ≤ 1`, `f₀ = 1` on `B̄_1(0)`, `f₀ = 0` off `B̄_2(0)`.
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Eucl P → ℝ, f₀ = fun z => max 0 (min 1 (2 - ‖z‖)) := ⟨_, rfl⟩
  have hf₀c : Continuous f₀ := by
    rw [hf₀]
    exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hf₀nn : ∀ z, 0 ≤ f₀ z := fun z => by rw [hf₀]; exact le_max_left _ _
  have hf₀le : ∀ z, f₀ z ≤ 1 := fun z => by
    rw [hf₀]; exact max_le zero_le_one (min_le_left _ _)
  have hf₀one : ∀ z : Eucl P, ‖z‖ ≤ 1 → f₀ z = 1 := by
    intro z hz
    rw [hf₀]
    simp only
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hf₀zero : ∀ z : Eucl P, 2 < ‖z‖ → f₀ z = 0 := by
    intro z hz
    rw [hf₀]
    simp only
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  have hf₀cs : HasCompactSupport f₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) 2) (fun z hz => ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hf₀zero z hz
  -- `I(s) = (sⁿ)⁻¹ ∫_M θ(y) f₀(s⁻¹(y − x)) dHⁿ(y) → L`, so eventually `I(s) ≤ L + 1`.
  have hlim := Submission.ind_ab_rescaled_tangent_limit P n M θ x Q f₀ hQ hf₀c hf₀cs
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      L = θ x * ∫ z in (Q : Set (Eucl P)), f₀ z ∂(μHE[n] : Measure (Eucl P)) := ⟨_, rfl⟩
  rw [← hL] at hlim
  have hev := hlim.eventually (ge_mem_nhds (lt_add_one L))
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hspos
  have hs0 : 0 < s := hspos
  -- `g_s(y) = θ(y) f₀(s⁻¹(y − x))` is integrable on `M ∩ B̄_{2s}(x)` and vanishes off it.
  have hgint : IntegrableOn (fun y => θ y * f₀ (s⁻¹ • (y - x))) M (μHE[n] : Measure (Eucl P)) := by
    have h1 : IntegrableOn (fun y => θ y * f₀ (s⁻¹ • (y - x))) (M ∩ closedBall x (2 * s))
        (μHE[n] : Measure (Eucl P)) := by
      refine Integrable.mul_bdd (c := 1) (hint _ (isCompact_closedBall x (2 * s))) ?_ ?_
      · exact (hf₀c.comp
          (by fun_prop : Continuous fun y : Eucl P => s⁻¹ • (y - x))).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (hf₀nn _)]; exact hf₀le _
    refine h1.of_ae_sdiff_eq_zero hM (Eventually.of_forall fun y hy => ?_)
    have hy2 : y ∉ closedBall x (2 * s) := fun h => hy.2 ⟨hy.1, h⟩
    rw [mem_closedBall, not_le, dist_eq_norm] at hy2
    have h2 : 2 < ‖s⁻¹ • (y - x)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), lt_inv_mul_iff₀ hs0]
      linarith
    show θ y * f₀ (s⁻¹ • (y - x)) = 0
    rw [hf₀zero _ h2, mul_zero]
  have hgnn : 0 ≤ᵐ[(μHE[n] : Measure (Eucl P)).restrict M] fun y => θ y * f₀ (s⁻¹ • (y - x)) := by
    filter_upwards [ae_restrict_mem₀ hM] with y hy
    exact mul_nonneg (hθ y hy) (hf₀nn _)
  have hball : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ closedBall x s)),
      y ∈ closedBall x s :=
    ae_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (ae_restrict_mem measurableSet_closedBall)
  -- On `B̄_s(x)`, `g_s = θ`; so the ball integral is at most `∫_M g_s = sⁿ I(s) ≤ sⁿ (L + 1)`.
  calc ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P))
      = ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y * f₀ (s⁻¹ • (y - x)))
          ∂(μHE[n] : Measure (Eucl P)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hball] with y hy
        rw [mem_closedBall, dist_eq_norm] at hy
        have h1 : ‖s⁻¹ • (y - x)‖ ≤ 1 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), inv_mul_le_iff₀ hs0]
          linarith
        rw [hf₀one _ h1, mul_one]
    _ ≤ ∫⁻ y in M, ENNReal.ofReal (θ y * f₀ (s⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P)) :=
        lintegral_mono' (Measure.restrict_mono inter_subset_left le_rfl) le_rfl
    _ = ENNReal.ofReal (∫ y in M, θ y * f₀ (s⁻¹ • (y - x)) ∂(μHE[n] : Measure (Eucl P))) :=
        (ofReal_integral_eq_lintegral_ofReal hgint hgnn).symm
    _ ≤ ENNReal.ofReal (s ^ n * (L + 1)) :=
        ENNReal.ofReal_le_ofReal ((inv_mul_le_iff₀ (pow_pos hs0 n)).1 hs)
    _ = (Real.toNNReal (L + 1) : ℝ≥0∞) * ENNReal.ofReal (s ^ n) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hs0.le n), mul_comm]
        rfl
/-- Weighted Lebesgue points of the orientation of a rectifiable triple (Simon Ch. 1, 3.23 with
3.11(3); Steps 1–3 of the proof of Ch. 6, 8.2).  For `Hⁿ⌞M`-a.e. `x`,
`(∫_{M ∩ B̄_s(x)} θ(y) ‖ξ(y) − ξ(x)‖ dHⁿ(y)) / (∫_{M ∩ B̄_s(x)} θ dHⁿ) → 0` as `s ↓ 0`
(`ℝ≥0∞`-valued).  With `λ = (Hⁿ⌞M) ⌞ θ`, `λ(B̄_s(x))` is the denominator, `λ` is locally finite
and mutually absolutely continuous with `Hⁿ⌞M` (`θ > 0` on `M`), and `ξ` is locally
`λ`-integrable as `‖ξ‖ ≤ 1` a.e.; the claim is Lebesgue differentiation of `ξ` with respect to
`λ` along the Besicovitch Vitali family of closed balls. -/
theorem Submission.ind_ab_weighted_lebesgue_point :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) := by
  intro P n M θ ξ h
  -- Step 1: `‖ξ‖ ≤ 1` a.e. on `M`, since `|α(τ)| ≤ ‖α‖ ∏ ‖τᵢ‖ = ‖α‖` for orthonormal `τ`.
  have hunit : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ y‖ ≤ 1 := by
    filter_upwards [h.orients] with y hy
    obtain ⟨τ, hτ, -, hξ⟩ := hy
    have hs : ∀ α : Covector (Eucl P) n, |α τ| ≤ ‖α‖ := by
      intro α
      have h1 := ContinuousAlternatingMap.le_opNorm α τ
      have h2 : ∏ i, ‖τ i‖ = 1 := by simp [hτ.1]
      simpa [h2] using h1
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun α => ?_)
    rw [one_mul]
    rcases hξ with hξ | hξ
    · rw [hξ, simpleNVector_apply, Real.norm_eq_abs]; exact hs α
    · rw [hξ, neg_apply, simpleNVector_apply, norm_neg, Real.norm_eq_abs]
      exact hs α
  -- Step 2: `θ` is a.e.-strongly measurable for `Hⁿ⌞M`, being integrable on each `M ∩ B̄_k(0)`.
  have hθm : AEStronglyMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ k : ℕ, M ∩ closedBall (0 : Eucl P) k := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_ge ‖y‖
        exact ⟨k, hy, hk⟩
      · rintro ⟨k, hy, -⟩
        exact hy
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro k
    exact (h.integrableOn _ (isCompact_closedBall 0 k) (subset_univ _)).aestronglyMeasurable
  have hwm : AEMeasurable (fun y => ENNReal.ofReal (θ y)) ((μHE[n] : Measure (Eucl P)).restrict M) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hθm.aemeasurable
  -- Step 3: the weighted measure `λ = (Hⁿ⌞M) ⌞ θ`, finite on closed balls.
  obtain ⟨lam, hlam⟩ : ∃ lam : Measure (Eucl P),
      lam = ((μHE[n] : Measure (Eucl P)).restrict M).withDensity (fun y => ENNReal.ofReal (θ y)) :=
    ⟨_, rfl⟩
  have hball : ∀ (z : Eucl P) (s : ℝ), lam (closedBall z s) =
      ∫⁻ y in M ∩ closedBall z s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) := by
    intro z s
    rw [hlam, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
  have hfin : ∀ (z : Eucl P) (s : ℝ), lam (closedBall z s) < ⊤ := by
    intro z s
    rw [hball]
    exact (h.integrableOn _ (isCompact_closedBall z s) (subset_univ _)).lintegral_lt_top
  have : IsLocallyFiniteMeasure lam :=
    ⟨fun z => ⟨closedBall z 1, closedBall_mem_nhds z one_pos, hfin z 1⟩⟩
  -- Step 4: `λ ≪ Hⁿ⌞M`, and `Hⁿ⌞M ≪ λ` since `θ > 0` on `M`.
  have hac1 : lam ≪ (μHE[n] : Measure (Eucl P)).restrict M := by
    rw [hlam]; exact withDensity_absolutelyContinuous _ _
  have hac2 : (μHE[n] : Measure (Eucl P)).restrict M ≪ lam := by
    rw [hlam]
    refine withDensity_absolutelyContinuous' hwm ?_
    filter_upwards [ae_restrict_mem₀ h.nullMeasurableSet] with y hy
    exact (ENNReal.ofReal_pos.2 (h.pos y hy)).ne'
  -- Steps 5–6: `ξ` is locally `λ`-integrable; Lebesgue–Besicovitch differentiation.
  have hdiff := VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (E := NVector (Eucl P) n)
    (Besicovitch.vitaliFamily lam) (f := ξ) (by
      intro z
      refine ⟨closedBall z 1, closedBall_mem_nhds z one_pos, ?_⟩
      refine Measure.integrableOn_of_bounded (M := 1) (hfin z 1).ne ?_ ?_
      · exact h.aestronglyMeasurable.mono_ac hac1
      · exact ae_restrict_of_ae (hac1.ae_le hunit))
  filter_upwards [hac2.ae_le hdiff] with x hx
  have hx' := hx.comp (Besicovitch.tendsto_filterAt lam x)
  -- Step 7: the `λ`-quotient over `B̄_s(x)` is the weighted `Hⁿ`-quotient over `M ∩ B̄_s(x)`.
  refine hx'.congr (fun s => ?_)
  simp only [Function.comp]
  rw [hball x s]
  congr 1
  rw [hlam, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hwm.restrict _
      measurableSet_closedBall (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict measurableSet_closedBall, inter_comm]
  rfl
/-- The orientation error term of the blow-up (Simon Ch. 6, proof of 8.2): write
`b(s) = ∫⁻_{M ∩ B̄_s(x)} θ dHⁿ` and `a(s) = ∫⁻_{M ∩ B̄_s(x)} θ ‖ξ - ξ(x)‖ₑ dHⁿ`.  If
`b(s) ≤ C sⁿ` for small `s > 0` and `a(s) / b(s) → 0`, then for every continuous compactly
supported `ω`, `∫_M θ(y) (ξ(y) - ξ(x))(r⁻ⁿ ω(r⁻¹(y - x))) dHⁿ(y) → 0` as `r → 0⁺`.
With `tsupport ω ⊆ B̄_R(0)` and `‖ω‖ ≤ B`, the integral has extended norm at most
`B Rⁿ · a(R r) / (R r)ⁿ`, and `a(s) / sⁿ ≤ C · a(s) / b(s) → 0`. -/
theorem Submission.ind_ab_orientation_error_vanishes :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (x : Eucl P) (ω : Eucl P → Covector (Eucl P) n), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → Continuous ω → HasCompactSupport ω → (∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤ C * ENNReal.ofReal (s ^ n)) → Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
  intro P n M θ ξ x ω hM hθ hω hωc hgrowth hratio
  obtain ⟨C, hC⟩ := hgrowth
  -- An estimate in `[0, ∞]`: if `0 < d < ∞`, `b ≤ c d` and `a / b < 1`, then `a / d ≤ c (a / b)`.
  have key : ∀ (a b d : ℝ≥0∞) (c : ℝ≥0), d ≠ 0 → d ≠ ⊤ → b ≤ c * d → a / b < 1 →
      a / d ≤ c * (a / b) := by
    intro a b d c hd0 hdtop hbd hab
    rw [ENNReal.div_le_iff hd0 hdtop]
    by_cases hb0 : b = 0
    · have ha0 : a = 0 := by
        by_contra hne
        rw [hb0, ENNReal.div_zero hne] at hab
        exact absurd hab (not_lt.2 le_top)
      rw [ha0]; exact zero_le
    · have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hdtop) hbd
      calc a = (a / b) * b := (ENNReal.div_mul_cancel hb0 hbtop).symm
        _ ≤ (a / b) * ((c : ℝ≥0∞) * d) := by gcongr
        _ = (c : ℝ≥0∞) * (a / b) * d := by ring
  -- The normalized error `a(s) / sⁿ` tends to `0`.
  have hε : Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s,
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / ENNReal.ofReal (s ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∫⁻ y in M ∩ closedBall x s,
        ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
          ENNReal.ofReal (s ^ n) ≤
        (C : ℝ≥0∞) * ((∫⁻ y in M ∩ closedBall x s,
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) := by
      filter_upwards [hC, hratio.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from zero_lt_one)),
        self_mem_nhdsWithin] with s hbs hrs hs
      have hs' : (0 : ℝ) < s := hs
      exact key _ _ _ C (ENNReal.ofReal_pos.2 (pow_pos hs' n)).ne' ENNReal.ofReal_ne_top hbs hrs
    have h2 := ENNReal.Tendsto.const_mul hratio (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun _ => zero_le) h1
  -- A radius `R > 0` with `tsupport ω ⊆ B̄_R(0)` and a bound `B` for `‖ω‖`.
  obtain ⟨R₀, hR₀⟩ := (hωc.isCompact.isBounded).subset_closedBall (0 : Eucl P)
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ tsupport ω ⊆ closedBall (0 : Eucl P) R :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos,
      hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨B, hB⟩ := hωc.exists_bound_of_continuous hω
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  -- For `r > 0` the integrand vanishes off `B̄_{Rr}(x)` and is bounded on `M` by
  -- `(rⁿ)⁻¹ B θ ‖ξ - ξ(x)‖`.
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal ((r ^ n)⁻¹ * B) *
          ∫⁻ y in M ∩ closedBall x (R * r), ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ
            ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hpt : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict M),
        ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ ≤
          (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y := by
      filter_upwards [ae_restrict_mem₀ hM] with y hy
      by_cases hyB : y ∈ closedBall x (R * r)
      · rw [indicator_of_mem hyB]
        have hcn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hr.le n)
        have hreal : ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ ≤
            ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by
          rw [norm_mul, Real.norm_of_nonneg (hθ y hy)]
          have hθy := hθ y hy
          calc θ y * ‖(ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖
              ≤ θ y * (‖ξ y - ξ x‖ * ‖(r ^ n)⁻¹ • ω (r⁻¹ • (y - x))‖) := by
                gcongr
                exact (ξ y - ξ x).le_opNorm _
            _ ≤ θ y * (‖ξ y - ξ x‖ * ((r ^ n)⁻¹ * B)) := by
                gcongr
                rw [norm_smul, Real.norm_of_nonneg hcn]
                gcongr
                exact hB _
            _ = ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by ring
        calc ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
            = ENNReal.ofReal ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ :=
              (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal (((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖)) := ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ) := by
              have he : ENNReal.ofReal ‖ξ y - ξ x‖ = ‖ξ y - ξ x‖ₑ :=
                ofReal_norm (E := NVector (Eucl P) n) _
              rw [ENNReal.ofReal_mul (mul_nonneg hcn hB0), ENNReal.ofReal_mul (hθ y hy), he]
      · rw [indicator_of_notMem hyB]
        have hω0 : ω (r⁻¹ • (y - x)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hyB
          have h1 := hRsub hmem
          rw [mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          linarith
        simp [hω0]
    calc ∫⁻ y in M, ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
          ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ y in M, (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y
            ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hpt
      _ = ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)
            ∂(μHE[n] : Measure (Eucl P)) := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Rewrite the bound as `B Rⁿ · a(R r) / (R r)ⁿ`.
  have hbound2 : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal (B * R ^ n) * ((∫⁻ y in M ∩ closedBall x (R * r),
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            ENNReal.ofReal ((R * r) ^ n)) := by
    intro r hr
    refine (hbound r hr).trans (le_of_eq ?_)
    have hRr : 0 < R * r := mul_pos hRpos hr
    have hd0 : ENNReal.ofReal ((R * r) ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hRr n)).ne'
    have hdt : ENNReal.ofReal ((R * r) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
    conv_lhs => rw [← ENNReal.div_mul_cancel hd0 hdt (b := ∫⁻ y in M ∩ closedBall x (R * r),
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)))]
    rw [mul_comm _ (ENNReal.ofReal ((R * r) ^ n)), ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) hB0)]
    congr 2
    rw [mul_pow]
    field_simp
  -- As `r → 0⁺`, `R r → 0⁺`, so the bound tends to `0`.
  have hcomp : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hRpos hr
  have hlim := ENNReal.Tendsto.const_mul (hε.comp hcomp)
    (Or.inr (ENNReal.ofReal_ne_top (r := B * R ^ n)))
  rw [mul_zero] at hlim
  rw [tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound2 r hr

/-- Blow-up of `τ(M, θ, ξ)` at a.e. point (Simon Ch. 6, proof of 8.2, display (7)): for
`Hⁿ`-a.e. `x ∈ M`, every weighted approximate tangent space `Q` of `(M, θ)` at `x` and every
continuous compactly supported `n`-form `ω`,
`τ(M, θ, ξ)(r⁻ⁿ ω ∘ η_{x,r}) → θ(x) ∫_Q ⟨ω, ξ(x)⟩ dHⁿ` as `r ↓ 0`, `η_{x,r}(y) = r⁻¹(y − x)`. -/
theorem Submission.ind_ae_blowup_limit :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt n M θ x Q →
        ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω →
          Tendsto (fun r : ℝ => tauAction n M θ ξ (fun y => (r ^ n)⁻¹ • ω (r⁻¹ • (y - x))))
            (𝓝[>] 0)
            (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), ξ x (ω z) ∂(μHE[n] : Measure (Eucl P)))) := by
  have htan := @Submission.ind_ab_rescaled_tangent_limit
  have hgrowth := @Submission.ind_ab_weighted_ball_growth
  have hleb := @Submission.ind_ab_weighted_lebesgue_point
  have herr := @Submission.ind_ab_orientation_error_vanishes
  intro P n M θ ξ hT
  have hθ0 : ∀ y ∈ M, 0 ≤ θ y := fun y hy => (hT.pos y hy).le
  have hθK : ∀ K : Set (Eucl P), IsCompact K →
      IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    fun K hK => hT.integrableOn K hK (subset_univ K)
  -- `‖ξ‖ ≤ 1` a.e. on `M`: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal.
  have hξ1 : ∀ᵐ y ∂(μHE[n] : Measure (Eucl P)).restrict M, ‖ξ y‖ ≤ 1 := by
    filter_upwards [hT.orients] with y hy
    obtain ⟨τ, hτ, -, hξy⟩ := hy
    have hs : ∀ α : Covector (Eucl P) n, ‖α τ‖ ≤ 1 * ‖α‖ := fun α => by
      rw [one_mul]
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
    rcases hξy with h | h
    · rw [h, simpleNVector_apply]
      exact hs α
    · rw [h, neg_apply, simpleNVector_apply, norm_neg]
      exact hs α
  filter_upwards [hleb P n M θ ξ hT] with x hx
  intro Q hQ ω hω hωc
  -- Growth `∫⁻_{M ∩ B̄_s(x)} θ ≤ C sⁿ`, and the orientation error `E(r) → 0`.
  have hC := hgrowth P n M θ x Q hT.nullMeasurableSet hθ0 hθK hQ
  have hE := herr P n M θ ξ x ω hT.nullMeasurableSet hθ0 hω hωc hC hx
  -- The main term `A(r)`, tested with `f = ⟨ω, ξ(x)⟩ ∈ C_c(ℝ^P)`.
  have hA := htan P n M θ x Q (fun z => ξ x (ω z)) hQ ((ξ x).continuous.comp hω)
    (hωc.comp_left (map_zero (ξ x)))
  have hlim := hA.add hE
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Set.mem_Ioi] at hr
  -- `τ(M, θ, ξ)(ω_r) = A(r) + E(r)` for `r > 0`, `ω_r(y) = r⁻ⁿ ω(r⁻¹(y − x))`.
  obtain ⟨B, hB⟩ := hω.bounded_above_of_compact_support hωc
  set c : ℝ := (r ^ n)⁻¹
  set K : Set (Eucl P) := (fun z => x + r • z) '' tsupport ω
  have hK : IsCompact K := hωc.isCompact.image (by fun_prop)
  have hzero : ∀ y ∉ K, ω (r⁻¹ • (y - x)) = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      hy ⟨r⁻¹ • (y - x), hmem, show x + r • r⁻¹ • (y - x) = y by
        rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
  have hbound : ∀ y, ‖c • ω (r⁻¹ • (y - x))‖ ≤ |c| * B := fun y => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg c)
  have hωr : Continuous fun y => c • ω (r⁻¹ • (y - x)) := by fun_prop
  have hIA : IntegrableOn (fun y => θ y * ξ x (c • ω (r⁻¹ • (y - x)))) M
      (μHE[n] : Measure (Eucl P)) := by
    refine IntegrableOn.of_ae_sdiff_eq_zero (s := M ∩ K) ?_ hT.nullMeasurableSet
      (Eventually.of_forall ?_)
    · refine (hθK K hK).mul_bdd (c := ‖ξ x‖ * (|c| * B)) ?_ (Eventually.of_forall fun y => ?_)
      · exact ((ξ x).continuous.comp hωr).aestronglyMeasurable
      · exact ((ξ x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))
    · rintro y ⟨hyM, hyMK⟩
      have hyK : y ∉ K := fun h => hyMK ⟨hyM, h⟩
      simp [hzero y hyK]
  have hIE : IntegrableOn (fun y => θ y * (ξ y - ξ x) (c • ω (r⁻¹ • (y - x)))) M
      (μHE[n] : Measure (Eucl P)) := by
    refine IntegrableOn.of_ae_sdiff_eq_zero (s := M ∩ K) ?_ hT.nullMeasurableSet
      (Eventually.of_forall ?_)
    · have hξK : ∀ᵐ y ∂(μHE[n] : Measure (Eucl P)).restrict (M ∩ K), ‖ξ y‖ ≤ 1 :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left hξ1
      have hξm : AEStronglyMeasurable (fun y => ξ y - ξ x)
          ((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)) :=
        (hT.aestronglyMeasurable.mono_set inter_subset_left).sub aestronglyMeasurable_const
      refine (hθK K hK).mul_bdd (c := (1 + ‖ξ x‖) * (|c| * B)) ?_ ?_
      · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hξm
          hωr.aestronglyMeasurable
      · filter_upwards [hξK] with y hy
        calc ‖(ξ y - ξ x) (c • ω (r⁻¹ • (y - x)))‖
            ≤ ‖ξ y - ξ x‖ * ‖c • ω (r⁻¹ • (y - x))‖ := (ξ y - ξ x).le_opNorm _
          _ ≤ (1 + ‖ξ x‖) * (|c| * B) := by
            refine mul_le_mul ?_ (hbound y) (norm_nonneg _) (by positivity)
            calc ‖ξ y - ξ x‖ ≤ ‖ξ y‖ + ‖ξ x‖ := norm_sub_le (ξ y) (ξ x)
              _ ≤ 1 + ‖ξ x‖ := by linarith
    · rintro y ⟨hyM, hyMK⟩
      have hyK : y ∉ K := fun h => hyMK ⟨hyM, h⟩
      simp [hzero y hyK]
  have hsplit : (fun y => θ y * ξ y (c • ω (r⁻¹ • (y - x)))) = fun y =>
      θ y * ξ x (c • ω (r⁻¹ • (y - x))) + θ y * (ξ y - ξ x) (c • ω (r⁻¹ • (y - x))) := by
    funext y
    rw [sub_apply]
    ring
  simp only [tauAction]
  rw [hsplit, integral_add hIA hIE, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_smul, smul_eq_mul]
  ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
