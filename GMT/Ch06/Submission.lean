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

theorem Submission.ind_pi_ss_cycle_slice_boundary : ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ) (t : ℝ) (S : GeometricCurrentOn U m), IsOpen U → T.boundary = 0 → IsSlice T f t S → ∃ A : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ f x < t} A ∧ A.boundary = S := by
  intro P m U T f t S hU hT hSl
  -- Unfold `IsSlice` (4.6): `S = ∂A − B` with `A = T ⌞ Aₜ`, `B = (∂T) ⌞ Aₜ`, where
  -- `Aₜ = {x ∈ U : f x < t}` and `B ω = ∫_{Aₜ} ⟨ω, v⟩ dμ` for a representation `(μ, v)` of `∂T`.
  obtain ⟨A, B, hA, ⟨hmeas, μ, v, hrep, hB⟩, hS⟩ := hSl
  -- `B = 0`, i.e. uniqueness of restrictions for the zero current `∂T`: testing `∂T = 0` with
  -- `g ω` (`g ∈ C_c^∞(U)`) shows that `⟨ω, v⟩` integrates to zero against every such `g`, so it
  -- vanishes `μ`-a.e. on `U ⊇ Aₜ`.
  have hB0 : ∀ ω : TestFormOn U m, B ω = 0 := by
    intro ω
    have hae : ∀ᵐ x ∂μ, x ∈ U → v x ((ω : DifferentialForm (Eucl P) m) x) = 0 := by
      refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hrep ω).1.locallyIntegrable.locallyIntegrableOn U) (fun g hg hgc hgU => ?_)
      let gω : TestFormOn U m := ⟨fun x => g x • (ω : DifferentialForm (Eucl P) m) x,
        ⟨hg.smul ω.property.1.1, hgc.smul_right⟩,
        (tsupport_smul_subset_left _ _).trans hgU⟩
      calc ∫ x, g x • v x ((ω : DifferentialForm (Eucl P) m) x) ∂μ
          = ∫ x, v x ((gω : DifferentialForm (Eucl P) m) x) ∂μ := by
            congr 1
            funext x
            exact (map_smul (v x) (g x) _).symm
        _ = T.boundary gω := ((hrep gω).2).symm
        _ = 0 := by rw [hT, GeometricCurrentOn.zero_apply]
    rw [hB ω]
    exact integral_eq_zero_of_ae
      ((ae_restrict_iff' hmeas).2 (hae.mono fun x hx hxA => hx hxA.1))
  -- Hence `S = ∂A − 0 = ∂A`, with `A` the restriction of `T` to `Aₜ`.
  refine ⟨A, hA, GeometricCurrentOn.ext fun ω => ?_⟩
  rw [hS ω, hB0 ω, sub_zero]
/-- Simon Ch. 6, (2.8)–(2.9): for `W ⊂⊂ U` and `S = X ⌞ A`, `M_W(S) ≤ M_W(X)`.  For an
admissible `ω`, `S(ω) = ∫_A ⟨ω, v⟩ dμ`.  By regularity of the finite measure `|⟨ω, v⟩| μ` there
are a closed `F ⊆ A` and an open `G ⊇ A` with `∫_{G \ F} |⟨ω, v⟩| dμ < ε`; a smooth
`ψ : ℝ^P → [0, 1]` equal to `1` on `F` with support `G` makes `ψ ω` admissible and
`S(ω) ≤ X(ψ ω) + ε ≤ M_W(X) + ε`. -/
theorem Submission.ind_pi_ss_restriction_massOn_le : ∀ (P k : ℕ) (U W A : Set (Eucl P)) (X S : GeometricCurrentOn U k), IsOpen U → CompactlyContainedOpen W U → IsRestriction X A S → S.massOn W ≤ X.massOn W := by
  intro P k U W A X S _ _ hR
  obtain ⟨hA, μ, v, hrep, hS⟩ := hR
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  set f : Eucl P → ℝ := fun x => v x ((ω : DifferentialForm (Eucl P) k) x)
  have hfi : Integrable f μ := (hrep ω).1
  -- The finite measure `ν = |f| μ`.
  set ν : Measure (Eucl P) := μ.withDensity (fun x => ‖f x‖ₑ) with hν_def
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfi.2.ne
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by simp [hε.ne']
  obtain ⟨F, hFA, hFc, hνF⟩ := hA.exists_isClosed_sdiff_lt (μ := ν) (measure_ne_top ν A) hε2
  obtain ⟨G, hAG, hGo, -, hνG⟩ := hA.exists_isOpen_sdiff_lt (μ := ν) (measure_ne_top ν A) hε2
  obtain ⟨ψ, hψs, hψr, hψsupp, hψ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hGo hFc (hFA.trans hAG)
  -- The cut-off test form `ψ ω`.
  have hω_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) :=
    ω.2.1.1
  have hω_cpt : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
  let ω' : TestFormOn U k := ⟨fun x => ψ x • (ω : DifferentialForm (Eucl P) k) x,
    ⟨hψs.smul hω_smooth, HasCompactSupport.smul_left (f := ψ) hω_cpt⟩,
    (tsupport_smul_subset_right _ _).trans ω.2.2⟩
  have hω' : ω' ∈ massAdmissibleOn U k W := by
    refine ⟨(tsupport_smul_subset_right _ _).trans hω.1, fun x => ?_⟩
    change covectorEuclideanNorm (ψ x • (ω : DifferentialForm (Eucl P) k) x) ≤ 1
    have h0 := hψr ⟨x, rfl⟩
    rw [hsmul, abs_of_nonneg h0.1]
    calc ψ x * covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ 1 * 1 :=
          mul_le_mul h0.2 (hω.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hω'f : ∀ x, v x ((ω' : DifferentialForm (Eucl P) k) x) = ψ x * f x := by
    intro x
    change v x (ψ x • (ω : DifferentialForm (Eucl P) k) x) = ψ x * f x
    rw [map_smul, smul_eq_mul]
  have hψf : Integrable (fun x => ψ x * f x) μ := by
    simpa only [hω'f] using (hrep ω').1
  have hXω' : X ω' = ∫ x, ψ x * f x ∂μ := by
    simpa only [hω'f] using (hrep ω').2
  have hGF : MeasurableSet (G \ F) := hGo.measurableSet.diff hFc.measurableSet
  -- Pointwise: `1_A f - ψ f ≤ 1_{G \ F} |f|`.
  have hpt : ∀ x, A.indicator f x - ψ x * f x ≤ (G \ F).indicator (fun x => |f x|) x := by
    intro x
    have h0 := hψr ⟨x, rfl⟩
    have hnn : 0 ≤ (G \ F).indicator (fun x => |f x|) x :=
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
    by_cases hxF : x ∈ F
    · rw [Set.indicator_of_mem (hFA hxF), (hψ1 x).1 hxF, one_mul, sub_self]
      exact hnn
    · by_cases hxG : x ∈ G
      · rw [Set.indicator_of_mem (show x ∈ G \ F from ⟨hxG, hxF⟩)]
        by_cases hxA : x ∈ A
        · rw [Set.indicator_of_mem hxA]
          nlinarith [le_abs_self (f x), abs_nonneg (f x), h0.1, h0.2]
        · rw [Set.indicator_of_notMem hxA]
          nlinarith [neg_abs_le (f x), abs_nonneg (f x), h0.1, h0.2]
      · have hψ0 : ψ x = 0 := by
          by_contra h
          exact hxG (hψsupp ▸ (Function.mem_support.mpr h))
        rw [Set.indicator_of_notMem (fun h => hxG (hAG h)), hψ0, zero_mul, sub_zero]
        exact hnn
  have hνGF : ν (G \ F) < ε := by
    calc ν (G \ F) ≤ ν ((G \ A) ∪ (A \ F)) := measure_mono fun x hx => by
          by_cases hxA : x ∈ A
          · exact Or.inr ⟨hxA, hx.2⟩
          · exact Or.inl ⟨hx.1, hxA⟩
      _ ≤ ν (G \ A) + ν (A \ F) := measure_union_le _ _
      _ < (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := ENNReal.add_lt_add hνG hνF
      _ = ε := ENNReal.add_halves _
  have hint : ∫ x in G \ F, |f x| ∂μ ≤ ε := by
    have h1 : ∫ x in G \ F, |f x| ∂μ = (ν (G \ F)).toReal := by
      rw [hν_def, withDensity_apply _ hGF]
      simp_rw [← Real.norm_eq_abs]
      exact integral_norm_eq_lintegral_enorm hfi.aestronglyMeasurable.restrict
    rw [h1]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hνGF.le
  have hest : S ω ≤ X ω' + ε := by
    have hdiff : S ω - X ω' = ∫ x, (A.indicator f x - ψ x * f x) ∂μ := by
      rw [hS ω, hXω', integral_sub (hfi.indicator hA) hψf, integral_indicator hA]
    have hle : ∫ x, (A.indicator f x - ψ x * f x) ∂μ ≤
        ∫ x, (G \ F).indicator (fun x => |f x|) x ∂μ :=
      integral_mono ((hfi.indicator hA).sub hψf) (hfi.abs.indicator hGF) hpt
    rw [integral_indicator hGF] at hle
    linarith
  calc ENNReal.ofReal (S ω) ≤ ENNReal.ofReal (X ω' + ε) := ENNReal.ofReal_le_ofReal hest
    _ ≤ ENNReal.ofReal (X ω') + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (X ω') + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ X.massOn W + ε := by gcongr; exact X.le_massOn hω'
theorem Submission.ind_pi_ss_cycle_slice_boundary : ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ) (t : ℝ) (S : GeometricCurrentOn U m), IsOpen U → T.boundary = 0 → IsSlice T f t S → ∃ A : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ f x < t} A ∧ A.boundary = S := by
  intro P m U T f t S hU hT hSl
  -- Unfold `IsSlice` (4.6): `S = ∂A − B` with `A = T ⌞ Aₜ`, `B = (∂T) ⌞ Aₜ`, where
  -- `Aₜ = {x ∈ U : f x < t}` and `B ω = ∫_{Aₜ} ⟨ω, v⟩ dμ` for a representation `(μ, v)` of `∂T`.
  obtain ⟨A, B, hA, ⟨hmeas, μ, v, hrep, hB⟩, hS⟩ := hSl
  -- `B = 0`, i.e. uniqueness of restrictions for the zero current `∂T`: testing `∂T = 0` with
  -- `g ω` (`g ∈ C_c^∞(U)`) shows that `⟨ω, v⟩` integrates to zero against every such `g`, so it
  -- vanishes `μ`-a.e. on `U ⊇ Aₜ`.
  have hB0 : ∀ ω : TestFormOn U m, B ω = 0 := by
    intro ω
    have hae : ∀ᵐ x ∂μ, x ∈ U → v x ((ω : DifferentialForm (Eucl P) m) x) = 0 := by
      refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hrep ω).1.locallyIntegrable.locallyIntegrableOn U) (fun g hg hgc hgU => ?_)
      let gω : TestFormOn U m := ⟨fun x => g x • (ω : DifferentialForm (Eucl P) m) x,
        ⟨hg.smul ω.property.1.1, hgc.smul_right⟩,
        (tsupport_smul_subset_left _ _).trans hgU⟩
      calc ∫ x, g x • v x ((ω : DifferentialForm (Eucl P) m) x) ∂μ
          = ∫ x, v x ((gω : DifferentialForm (Eucl P) m) x) ∂μ := by
            congr 1
            funext x
            exact (map_smul (v x) (g x) _).symm
        _ = T.boundary gω := ((hrep gω).2).symm
        _ = 0 := by rw [hT, GeometricCurrentOn.zero_apply]
    rw [hB ω]
    exact integral_eq_zero_of_ae
      ((ae_restrict_iff' hmeas).2 (hae.mono fun x hx hxA => hx hxA.1))
  -- Hence `S = ∂A − 0 = ∂A`, with `A` the restriction of `T` to `Aₜ`.
  refine ⟨A, hA, GeometricCurrentOn.ext fun ω => ?_⟩
  rw [hS ω, hB0 ω, sub_zero]

/-- **Slices of a cycle (Simon Ch. 6, 4.5(1)–(2), 4.6, 4.10).**  For `X ∈ 𝒟_{m+1}(U)` with
`∂X = 0` and locally finite mass, `d` `L`-Lipschitz and `a < b`, there are restrictions
`A_t = X ⌞ {d < t}` and a measurable `g` with `M_W(∂A_t) ≤ g(t)` on `(a, b)` and
`∫⁻_{(a,b)} g ≤ L · M_W(X)`.  As `M_V(∂X) = M_V(0) = 0`, `SlicingTheorem` gives slices
`S_t = ⟨X, d, t⟩`, and `∂A_t = S_t` by `ind_pi_ss_cycle_slice_boundary`.  The band
`{a < d < b} = {|d - (a + b)/2| < (b - a)/2}` is a sublevel set of an `L`-Lipschitz function, so
the same lemma gives the restriction `R = X ⌞ {a < d < b}` used by the mass clause of 4.10
(`‖Dd‖ ≤ L`); finally `M_W(R) ≤ M_W(X)` by `ind_pi_ss_restriction_massOn_le`. -/
theorem Submission.ind_pi_ss_cycle_slice_family : SlicingTheorem → ∀ (P m : ℕ) (U W : Set (Eucl P)) (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ), IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b → X.boundary = 0 → (∀ V, CompactlyContainedOpen V U → X.massOn V < ∞) → ∃ (A : ℝ → GeometricCurrentOn U (m + 1)) (g : ℝ → ℝ≥0∞), Measurable g ∧ (∀ t, IsRestriction X {x | x ∈ U ∧ d x < t} (A t)) ∧ (∀ t ∈ Ioo a b, (A t).boundary.massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * X.massOn W := by
  intro hST P m U W X d L a b hU hW hd hab hX0 hXfin
  -- Step 1: `M_V(∂X) = M_V(0) = 0`, so `X` satisfies the hypotheses of `SlicingTheorem`.
  have hfin : ∀ V, CompactlyContainedOpen V U →
      X.massOn V < ∞ ∧ X.boundary.massOn V < ∞ := by
    intro V hV
    have h0 : (0 : GeometricCurrentOn U m).massOn V = 0 := by
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, -, rfl⟩
      simp
    rw [hX0, h0]
    exact ⟨hXfin V hV, ENNReal.zero_lt_top⟩
  -- Step 2: the slices `S_t = ⟨X, d, t⟩` and the mass clause of 4.10 for `d`.
  obtain ⟨S, hS, -, -, hSmass⟩ := hST P m U hU X hfin d L hd.lipschitzOnWith
  -- Step 3: `A_t = X ⌞ {d < t}` with `∂A_t = S_t`.
  choose A hAres hAbd using fun t =>
    Submission.ind_pi_ss_cycle_slice_boundary P m U X d t (S t) hU hX0 (hS t)
  -- Step 4: `R = X ⌞ {a < d < b}`, as the band is the sublevel set `{|d - c| < r}` of the
  -- `L`-Lipschitz function `|d - c|`, `c = (a + b)/2`, `r = (b - a)/2`.
  have hc : LipschitzWith L fun x => |d x - (a + b) / 2| := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    calc dist |d x - (a + b) / 2| |d y - (a + b) / 2|
        = |(|d x - (a + b) / 2| - |d y - (a + b) / 2|)| := Real.dist_eq _ _
      _ ≤ |(d x - (a + b) / 2) - (d y - (a + b) / 2)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = dist (d x) (d y) := by rw [sub_sub_sub_cancel_right, Real.dist_eq]
      _ ≤ L * dist x y := hd.dist_le_mul x y
  obtain ⟨S', hS', -⟩ := hST P m U hU X hfin (fun x => |d x - (a + b) / 2|) L hc.lipschitzOnWith
  obtain ⟨R, hR, -⟩ := Submission.ind_pi_ss_cycle_slice_boundary P m U X
    (fun x => |d x - (a + b) / 2|) ((b - a) / 2) (S' ((b - a) / 2)) hU hX0 (hS' _)
  have hRband : IsRestriction X {x | x ∈ U ∧ a < d x ∧ d x < b} R := by
    have hband : {x | x ∈ U ∧ a < d x ∧ d x < b} =
        {x | x ∈ U ∧ |d x - (a + b) / 2| < (b - a) / 2} := by
      ext x
      simp only [mem_ofPred_eq, abs_sub_lt_iff]
      constructor
      · rintro ⟨hx, h₁, h₂⟩
        exact ⟨hx, by linarith, by linarith⟩
      · rintro ⟨hx, h₁, h₂⟩
        exact ⟨hx, by linarith, by linarith⟩
    rw [hband]
    exact hR
  -- Step 5: the mass clause of 4.10 on `W`, with `‖Dd‖ ≤ L` everywhere.
  have hDd : ∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ d x‖₊ ≤ L :=
    ae_of_all _ fun x _ => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_fderiv_le_of_lipschitz ℝ hd
  obtain ⟨g, hg, hgS, hgint⟩ :=
    hSmass W hW.1 (subset_closure.trans hW.2.2) L hDd a b hab R hRband
  -- Step 6: `M_W(∂A_t) = M_W(S_t) ≤ g(t)` and `∫⁻ g ≤ L · M_W(R) ≤ L · M_W(X)`.
  refine ⟨A, g, hg, hAres, fun t ht => ?_, ?_⟩
  · rw [hAbd t]
    exact hgS t ht
  · calc ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * R.massOn W := hgint
      _ ≤ (L : ℝ≥0∞) * X.massOn W := by
        gcongr
        exact Submission.ind_pi_ss_restriction_massOn_le P (m + 1) U W _ X R hU hW hRband
/-- Fatou selection of a good level (the "selection argument as in 6.7(2) of Ch. 2" in the proof
of Simon Ch. 6, 8.2): if `∫⁻_{(a,b)} g_k ≤ C < ∞` for all `k` and `E` is countable, there are
`γ ∈ (a, b) \ E`, a subsequence `σ` and `G < ∞` with `g_{σ(k)}(γ) ≤ G` for all `k`.  By Fatou,
`∫⁻_{(a,b)} liminf_k g_k ≤ C`, so `liminf_k g_k(γ) < ∞` for some `γ ∈ (a, b) \ E` (`E` is
Lebesgue-null); with `G = liminf_k g_k(γ) + 1`, `g_k(γ) < G` for infinitely many `k`. -/
theorem Submission.ind_pi_ss_fatou_level_selection :
    ∀ (g : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (C : ℝ≥0∞) (E : Set ℝ), a < b → (∀ k, Measurable (g k)) →
      C < ∞ → (∀ k, ∫⁻ t in Ioo a b, g k t ≤ C) → E.Countable →
      ∃ (γ : ℝ) (σ : ℕ → ℕ) (G : ℝ≥0∞), γ ∈ Ioo a b ∧ γ ∉ E ∧ StrictMono σ ∧ G < ∞ ∧
        ∀ k, g (σ k) γ ≤ G := by
  intro g a b C E hab hg hC hgC hE
  -- Fatou: `F = liminf_k g_k` is measurable and `∫⁻_{(a,b)} F ≤ liminf_k ∫⁻_{(a,b)} g_k ≤ C`.
  have hF : Measurable fun t => liminf (fun k => g k t) atTop := Measurable.liminf hg
  have hFC : ∫⁻ t in Ioo a b, liminf (fun k => g k t) atTop ≤ C :=
    (lintegral_liminf_le hg).trans (liminf_le_of_frequently_le' (Frequently.of_forall hgC))
  -- For a.e. `t` w.r.t. `volume⌞(a, b)`: `F t < ∞`, `t ∉ E` (`E` is Lebesgue-null), `t ∈ (a, b)`.
  have h₁ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), liminf (fun k => g k t) atTop < ∞ :=
    ae_lt_top hF (hFC.trans_lt hC).ne
  have h₂ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∉ E :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hE.measure_zero volume))
  have h₃ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∈ Ioo a b := ae_restrict_mem measurableSet_Ioo
  -- `volume (a, b) = b - a > 0`, so the a.e. filter is nontrivial and a good `γ` exists.
  have hne : (ae (volume.restrict (Ioo a b))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.2 hab
  obtain ⟨γ, hγF, hγE, hγ⟩ := (h₁.and (h₂.and h₃)).exists
  -- `G = F(γ) + 1 > liminf_k g_k(γ)`, so `g_k(γ) < G` frequently: extract `σ`.
  have hG : liminf (fun k => g k γ) atTop < liminf (fun k => g k γ) atTop + 1 :=
    ENNReal.lt_add_right hγF.ne one_ne_zero
  obtain ⟨σ, hσ, hσG⟩ := extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (h := hG))
  exact ⟨γ, σ, _, hγ, hγE, hσ, ENNReal.add_lt_top.2 ⟨hγF, ENNReal.one_lt_top⟩,
    fun k => (hσG k).le⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
