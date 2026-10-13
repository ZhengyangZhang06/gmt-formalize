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

/-- The upper limit of `f : ℝ → [0,∞]` at `0⁺` is computed along the radii `1/(n+1)`:
`limsup_{t→0⁺} f(t) = inf_{n ∈ ℕ} sup_{0<t<1/(n+1)} f(t)`.  The intervals `(0, ε)`, `ε > 0`, form
a basis of `𝓝[>] 0`, so the upper limit is `inf_{ε>0} sup_{(0,ε)} f`; each radius `1/(n+1)` is
admissible, and every `ε > 0` exceeds some `1/(n+1)`, below which the supremum is smaller. -/
theorem Submission.rectifiability_mickle_rado_limsup_eq_iInf :
    ∀ f : ℝ → ℝ≥0∞, limsup f (𝓝[>] (0 : ℝ)) =
      ⨅ n : ℕ, ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), f t := by
  intro f
  rw [(nhdsGT_basis (0 : ℝ)).limsup_eq_iInf_iSup]
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact iInf₂_le (1 / ((n : ℝ) + 1)) (by positivity)
  · refine le_iInf₂ fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine (iInf_le _ n).trans ?_
    exact biSup_mono fun t ht => ⟨ht.1, ht.2.trans hn⟩
theorem Submission.rectifiability_mickle_rado_sup_lsc : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))), (∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ')) → ∀ r : ℝ, LowerSemicontinuous (fun c : Eucl (m + 1) => ⨆ t ∈ Ioo (0 : ℝ) r, ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) := by
  intro m ψ hball r
  -- step 1: `c ↦ ψ (ball c τ)` is lower semicontinuous, by inner continuity on balls
  have hlsc : ∀ τ : ℝ, LowerSemicontinuous (fun c : Eucl (m + 1) => ψ (ball c τ)) := by
    intro τ c a ha
    change a < ψ (ball c τ) at ha
    rw [hball c τ] at ha
    obtain ⟨τ', hτ', hlt⟩ := lt_biSup_iff.1 ha
    filter_upwards [ball_mem_nhds c (sub_pos.2 hτ'.2)] with c' hc'
    refine hlt.trans_le (measure_mono ?_)
    intro z hz
    rw [mem_ball] at hz hc' ⊢
    calc dist z c' ≤ dist z c + dist c c' := dist_triangle _ _ _
      _ < τ' + (τ - τ') := by rw [dist_comm c c']; exact add_lt_add hz hc'
      _ = τ := by ring
  -- step 2: divide by the positive finite `tᵏ`, then take the supremum over `t ∈ (0, r)`
  apply lowerSemicontinuous_biSup
  intro t ht
  have hden : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht.1 _)).ne'
  exact (ENNReal.continuous_div_const _ hden).comp_lowerSemicontinuous (hlsc t)
    (fun _ _ h => ENNReal.div_le_div_right h _)
/-- Vitali covering estimate off a `ψ`-null closed set, a covering step for the Mickle–Radó
density theorem (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439).  If `K` is closed,
`ψ K = 0` and `ψ(B(z,τ)) ≤ C τᵏ` for `z ∈ K`, `0 < τ < r` (`k = m + 1`), then
`ψ(B(c₀,t)) · Lᵏ(B(0,1)) ≤ C 6ᵏ Lᵏ(B(c₀,2t) ∖ K)` for `c₀ ∈ K`, `0 < t`, `6t ≤ r`.  The balls
`B(z, d z)`, `d z = dist(z,K)`, `z ∈ B(c₀,t) ∖ K`, miss `K` and lie in `B(c₀,2t)`.  A disjoint
(hence countable) Vitali subfamily has `5`-fold enlargements covering `B(c₀,t) ∖ K`, and
`B(b, 5 d b) ⊆ B(z'_b, 6 d b)` for a nearest point `z'_b ∈ K` of `b`, where `6 d b < 6t ≤ r`. -/
theorem Submission.rectifiability_mickle_rado_vitali_bound : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ c₀ ∈ K, ∀ t : ℝ, 0 < t → 6 * t ≤ r → ψ (ball c₀ t) * (volume : Measure (Eucl (m + 1))) (ball 0 1) ≤ C * 6 ^ (m + 1) * (volume : Measure (Eucl (m + 1))) (ball c₀ (2 * t) \ K) := by
  intro m ψ K C r hK hψK hbound c₀ hc₀ t ht htr
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  set ω := μ (ball 0 1) with hω
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  have hKne : K.Nonempty := ⟨c₀, hc₀⟩
  -- step 1: `ψ(B(c₀,t)) ≤ ψ(B(c₀,t) ∖ K) + ψ(K) = ψ(B(c₀,t) ∖ K)`
  have h1 : ψ (ball c₀ t) ≤ ψ (ball c₀ t \ K) := by
    calc ψ (ball c₀ t) ≤ ψ ((ball c₀ t \ K) ∪ K) := measure_mono (fun x hx => by
          by_cases h : x ∈ K
          · exact Or.inr h
          · exact Or.inl ⟨hx, h⟩)
      _ ≤ ψ (ball c₀ t \ K) + ψ K := measure_union_le _ _
      _ = ψ (ball c₀ t \ K) := by rw [hψK, add_zero]
  set T := ball c₀ t \ K with hT
  -- step 2: on `T`, the radius `d z = dist(z, K)` satisfies `0 < d z ≤ dist(z, c₀) < t`
  set d : Eucl (m + 1) → ℝ := fun z => infDist z K with hd
  have hd_pos : ∀ z ∈ T, 0 < d z := fun z hz => (hK.notMem_iff_infDist_pos hKne).1 hz.2
  have hd_lt : ∀ z ∈ T, d z < t := fun z hz =>
    (infDist_le_dist_of_mem hc₀).trans_lt (mem_ball.1 hz.1)
  -- steps 3–4: a disjoint, hence countable, Vitali subfamily `u ⊆ T` with enlargement factor `5`
  obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    T (fun z => z) d t (fun z hz => (hd_lt z hz).le) 5 (by norm_num)
  have hu_count : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun z hz => ⟨z, mem_ball_self (hd_pos z (huT hz))⟩)
  -- step 5: recentre at nearest points `z' b ∈ K`, so that `T ⊆ ⋃_{b ∈ u} B(z' b, 6 d b)`
  have hnear : ∀ z, ∃ y ∈ K, infDist z K = dist z y := fun z => hK.exists_infDist_eq_dist hKne z
  choose z' hz'K hz'd using hnear
  have hcover : T ⊆ ⋃ b ∈ u, ball (z' b) (6 * d b) := by
    intro a ha
    obtain ⟨b, hbu, hab⟩ := hcov a ha
    have hab' : a ∈ ball b (5 * d b) := hab (mem_ball_self (hd_pos a ha))
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hab' ⊢
    have hbz : dist b (z' b) = d b := (hz'd b).symm
    calc dist a (z' b) ≤ dist a b + dist b (z' b) := dist_triangle _ _ _
      _ < 5 * d b + d b := by rw [hbz]; linarith
      _ = 6 * d b := by ring
  -- steps 6–7: as `0 < 6 d b < 6t ≤ r`, `ψ(T) ≤ ∑_{b ∈ u} C 6ᵏ (d b)ᵏ`
  have h2 : ψ T ≤ ∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
    calc ψ T ≤ ψ (⋃ b ∈ u, ball (z' b) (6 * d b)) := measure_mono hcover
      _ ≤ ∑' b : u, ψ (ball (z' b) (6 * d b)) := measure_biUnion_le ψ hu_count _
      _ ≤ ∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        have hb : (b : Eucl (m + 1)) ∈ T := huT b.2
        have hpos := hd_pos b hb
        have hlt := hd_lt b hb
        calc ψ (ball (z' b) (6 * d b)) ≤ C * ENNReal.ofReal ((6 * d b) ^ (m + 1)) :=
              hbound (z' b) (hz'K b) (6 * d b) ⟨by linarith, by linarith⟩
          _ = C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
            rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
            simp [mul_assoc]
  -- step 8: for the disjoint balls `B(b, d b) ⊆ B(c₀,2t) ∖ K`,
  -- `∑_{b ∈ u} (d b)ᵏ ω = Lᵏ(⋃_{b ∈ u} B(b, d b)) ≤ Lᵏ(B(c₀,2t) ∖ K)`
  have h3 : ∑' b : u, ENNReal.ofReal ((d b) ^ (m + 1)) * ω ≤ μ (ball c₀ (2 * t) \ K) := by
    have heq : ∀ b : u,
        ENNReal.ofReal ((d b) ^ (m + 1)) * ω = μ (ball (b : Eucl (m + 1)) (d b)) := by
      intro b
      rw [Measure.addHaar_ball μ _ (hd_pos b (huT b.2)).le, hfin]
    simp_rw [heq]
    rw [← measure_biUnion hu_count hdisj (fun _ _ => measurableSet_ball)]
    apply measure_mono
    intro y hy
    obtain ⟨b, hbu, hyb⟩ := mem_iUnion₂.1 hy
    have hbT := huT hbu
    refine ⟨?_, ?_⟩
    · rw [mem_ball] at hyb ⊢
      have hbc := mem_ball.1 hbT.1
      have := hd_lt b hbT
      calc dist y c₀ ≤ dist y b + dist b c₀ := dist_triangle _ _ _
        _ < 2 * t := by linarith
    · intro hyK
      exact Set.disjoint_left.1 (disjoint_ball_infDist (x := b) (s := K)) hyb hyK
  -- step 9: combine, pulling the constants out of the sums
  calc ψ (ball c₀ t) * ω
      ≤ (∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1))) * ω := by
        gcongr; exact h1.trans h2
    _ = C * 6 ^ (m + 1) * ∑' b : u, ENNReal.ofReal ((d b) ^ (m + 1)) * ω := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, mul_assoc]
    _ ≤ C * 6 ^ (m + 1) * μ (ball c₀ (2 * t) \ K) := by gcongr

/-- Mickle–Radó density step (Mattila, Thm 18.5, step 3 with `ε ↓ 0`): if `ψ(B(z,τ)) ≤ C τᵏ`
for `z ∈ K`, `0 < τ < r`, where `K` is closed and `ψ(K) = 0`, then the upper `k`-density of `ψ`
vanishes at `Lᵏ`-a.e. point of `K`.  At a Lebesgue density point `c ∈ K` of `K`, the Vitali
estimate `ψ(B(c,t))·ω ≤ C·6ᵏ·Lᵏ(B(c,2t) ∖ K)` together with
`Lᵏ(B̄(c,2t) ∖ K) = (2t)ᵏ·ω·(1 − R_c(2t))`, `R_c(ρ) = Lᵏ(K ∩ B̄(c,ρ))/Lᵏ(B̄(c,ρ)) → 1`, gives
`ψ(B(c,t))/tᵏ ≤ C·12ᵏ·(1 − R_c(2t)) → 0`. -/
theorem Submission.rectifiability_mickle_rado_density_zero : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → C ≠ ⊤ → 0 < r → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ᵐ c ∂((volume : Measure (Eucl (m + 1))).restrict K), limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) = 0 := by
  intro m ψ K C r hK hψK hC hr hbound
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ K, ae_restrict_mem hK.measurableSet]
    with c hc hcK
  apply Tendsto.limsup_eq
  set ω := μ (ball 0 1) with hω
  have hω0 : ω ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hωtop : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  -- the density ratio at radius 2t
  have hR2 : Tendsto (fun t : ℝ => μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))
      (𝓝[>] 0) (𝓝 1) := by
    refine hc.comp ?_
    have h2 : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] (2 * 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_const.mul continuous_id).tendsto' _ _ rfl |>.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mem_Ioi.2 (by simpa using ht))
    simpa using h2
  have hlim : Tendsto (fun t : ℝ => C * 12 ^ (m + 1) *
      (1 - μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.sub tendsto_const_nhds hR2 (Or.inl ENNReal.one_ne_top)
    have h12 : C * 12 ^ (m + 1) ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.pow_ne_top (by norm_num))
    have h2 := ENNReal.Tendsto.const_mul (a := C * 12 ^ (m + 1)) h1 (Or.inr h12)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 6 by positivity)] with t ht
  have ht0 : 0 < t := ht.1
  have h0 := Submission.rectifiability_mickle_rado_vitali_bound m ψ K C r hK hψK hbound c hcK t ht0
    (by linarith [ht.2])
  -- measure of the complement in the closed ball
  set V := μ (closedBall c (2 * t)) with hV
  set A := μ (K ∩ closedBall c (2 * t)) with hA
  have hVball : V = ENNReal.ofReal ((2 * t) ^ (m + 1)) * ω := by
    rw [hV, Measure.addHaar_closedBall μ c (by positivity), hfin]
  have hV0 : V ≠ 0 := by
    rw [hVball]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hω0
  have hVtop : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hAle : A ≤ V := measure_mono inter_subset_right
  have hdiff : μ (ball c (2 * t) \ K) ≤ V * (1 - A / V) := by
    have hsplit : μ (closedBall c (2 * t) \ K) + A = V := by
      rw [hA, inter_comm]; exact measure_sdiff_add_inter _ hK.measurableSet
    have h1 : μ (ball c (2 * t) \ K) ≤ μ (closedBall c (2 * t) \ K) :=
      measure_mono (sdiff_subset_sdiff_left ball_subset_closedBall)
    have h2 : μ (closedBall c (2 * t) \ K) = V - A :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hVtop hAle) hsplit
    have h3 : V * (1 - A / V) = V - A := by
      rw [ENNReal.mul_sub (fun _ _ => hVtop), mul_one, ENNReal.mul_div_cancel hV0 hVtop]
    rw [h3, ← h2]; exact h1
  -- conclude
  have hpowt : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
  rw [ENNReal.div_le_iff_le_mul (Or.inl hpowt) (Or.inl ENNReal.ofReal_ne_top)]
  have h2t : ENNReal.ofReal ((2 * t) ^ (m + 1)) = 2 ^ (m + 1) * ENNReal.ofReal (t ^ (m + 1)) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  have key : ψ (ball c t) * ω ≤
      (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
    calc ψ (ball c t) * ω ≤ C * 6 ^ (m + 1) * μ (ball c (2 * t) \ K) := h0
      _ ≤ C * 6 ^ (m + 1) * (V * (1 - A / V)) := by gcongr
      _ = (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
        rw [hVball, h2t]
        have : (12 : ℝ≥0∞) ^ (m + 1) = 6 ^ (m + 1) * 2 ^ (m + 1) := by
          rw [← mul_pow]; norm_num
        rw [this]; ring
  exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key

/-- **Mickle–Radó density theorem** (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439;
Mattila, Thm 18.5).  Let `ψ` be an outer measure on `ℝᵏ`, `k = m + 1`, inner continuous on open
balls, and `D` a Borel set with `ψ(D) = 0`.  Then the upper density
`ϑ(c) = limsup_{t↓0} ψ(B(c,t))/tᵏ` lies in `{0, ∞}` at `Lᵏ`-a.e. point of `D`.  With
`g_n(c) = sup_{0<t<1/(n+1)} ψ(B(c,t))/tᵏ`, each `g_n` is lower semicontinuous and `ϑ = inf_n g_n`,
so `ϑ` is Borel.  The set `{c ∈ D : 0 < ϑ(c) < ∞}` is covered by the Borel sets
`S_n = {c ∈ D : (n+1)⁻¹ < ϑ(c), g_n(c) ≤ n+1}`.  If `Lᵏ(S_n) > 0`, a compact `K ⊆ S_n` with
`Lᵏ(K) > 0` has `ψ(K) = 0` and `ψ(B(z,τ)) ≤ (n+1)τᵏ` for `z ∈ K`, `0 < τ < 1/(n+1)`; hence
`ϑ = 0` at `Lᵏ`-a.e. point of `K`, contradicting `ϑ > (n+1)⁻¹` on `K`. -/
theorem Submission.rectifiability_mickle_rado : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (D : Set (Eucl (m + 1))), (∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ')) → MeasurableSet D → ψ D = 0 → (volume : Measure (Eucl (m + 1))) {c | c ∈ D ∧ 0 < limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) < ⊤} = 0 := by
  intro m ψ D hball hD hψD
  let g : ℕ → Eucl (m + 1) → ℝ≥0∞ := fun n c =>
    ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))
  let ϑ : Eucl (m + 1) → ℝ≥0∞ := fun c =>
    limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0)
  -- step 1: `ϑ = inf_n g_n` with every `g_n` lower semicontinuous, so `ϑ` is Borel
  have hϑ : ∀ c, ϑ c = ⨅ n, g n c := fun c =>
    Submission.rectifiability_mickle_rado_limsup_eq_iInf
      (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1)))
  have hg_meas : ∀ n, Measurable (g n) := fun n =>
    (Submission.rectifiability_mickle_rado_sup_lsc m ψ hball _).measurable
  have hϑ_meas : Measurable ϑ := by
    have h : ϑ = fun c => ⨅ n, g n c := funext hϑ
    rw [h]
    exact Measurable.iInf hg_meas
  have hg_anti : ∀ c, Antitone (fun n => g n c) := by
    intro c n n' hnn'
    apply biSup_mono
    intro t ht
    refine ⟨ht.1, lt_of_lt_of_le ht.2 ?_⟩
    have h1 : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
    gcongr
  -- step 2: `{c ∈ D : 0 < ϑ c < ∞} ⊆ ⋃_n S_n` for the Borel sets `S_n`
  let S : ℕ → Set (Eucl (m + 1)) := fun n =>
    {c | c ∈ D ∧ ((n : ℝ≥0∞) + 1)⁻¹ < ϑ c ∧ g n c ≤ (n : ℝ≥0∞) + 1}
  have hS_meas : ∀ n, MeasurableSet (S n) := by
    intro n
    exact hD.inter ((measurableSet_lt measurable_const hϑ_meas).inter
      (measurableSet_le (hg_meas n) measurable_const))
  have hsub : {c | c ∈ D ∧ 0 < limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) < ⊤} ⊆ ⋃ n, S n := by
    rintro c ⟨hcD, hpos, hfin⟩
    change ϑ c < ⊤ at hfin
    change 0 < ϑ c at hpos
    rw [hϑ c] at hfin
    obtain ⟨n₀, hn₀⟩ := iInf_lt_iff.1 hfin
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hn₀.ne
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    set n := max n₀ (max N n₁) with hn
    refine mem_iUnion.2 ⟨n, hcD, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hn₁
      apply ENNReal.inv_le_inv.2
      have : n₁ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
      have : (n₁ : ℝ≥0∞) ≤ n := by exact_mod_cast this
      exact this.trans le_self_add
    · calc g n c ≤ g n₀ c := hg_anti c (le_max_left _ _)
        _ ≤ N := hN.le
        _ ≤ (n : ℝ≥0∞) := by
          have : N ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
          exact_mod_cast this
        _ ≤ (n : ℝ≥0∞) + 1 := le_self_add
  -- step 3: `Lᵏ(S_n) = 0`, via a compact `K ⊆ S_n` and the density-zero step on `K`
  have hS_null : ∀ n, (volume : Measure (Eucl (m + 1))) (S n) = 0 := by
    intro n
    by_contra hne
    obtain ⟨K, hKS, hKc, hKpos⟩ := (hS_meas n).exists_lt_isCompact (pos_iff_ne_zero.2 hne)
    have hψK : ψ K = 0 := measure_mono_null (fun x hx => (hKS hx).1) hψD
    have hbound : ∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ψ (ball z τ) ≤ ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (τ ^ (m + 1)) := by
      intro z hz τ hτ
      have h1 : ψ (ball z τ) / ENNReal.ofReal (τ ^ (m + 1)) ≤ g n z :=
        le_iSup₂ (f := fun t (_ : t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))) =>
          ψ (ball z t) / ENNReal.ofReal (t ^ (m + 1))) τ hτ
      have h2 := h1.trans (hKS hz).2.2
      rwa [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.ofReal_pos.2 (pow_pos hτ.1 _)).ne')
        (Or.inl ENNReal.ofReal_ne_top)] at h2
    have hae := Submission.rectifiability_mickle_rado_density_zero m ψ K ((n : ℝ≥0∞) + 1)
      (1 / ((n : ℝ) + 1)) hKc.isClosed hψK (by simp) (by positivity) hbound
    obtain ⟨c, hcK, hc0⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hKpos.ne' hae
    have h3 : ((n : ℝ≥0∞) + 1)⁻¹ < ϑ c := (hKS hcK).2.1
    change _ < limsup _ _ at h3
    rw [hc0] at h3
    exact (ENNReal.not_lt_zero h3).elim
  exact measure_mono_null hsub (measure_iUnion_null hS_null)

/-- For an s-finite `μ` and measurable sets `G r s ⊆ Z × Y`, increasing in `s` and with
`G r s = ⋃_{0<r'<r} G r' s` for `r > 0`, the map
`z ↦ limsup_{s→0⁺} sup_{0<r<δ} μ{y | (z, y) ∈ G r s} / (r s)ᵏ` is measurable.  Each section
measure is measurable in `z` (Tonelli).  By continuity from below along rational `r' < r` the
supremum over `r` may be taken over rational `r`, and since `F(s) ≤ (s'/s)ᵏ F(s')` for
`0 < s ≤ s'`, the supremum over `s ∈ (0, ε)` may be taken over rational `s`.  Computing the upper
limit along the radii `1/(n+1)` then gives a countable `inf`–`sup` of measurable functions. -/
theorem Submission.rectifiability_bf_limsup_sup_measurable :
    ∀ (Z Y : Type) [MeasurableSpace Z] [MeasurableSpace Y] (k : ℕ) (μ : Measure Y) (δ : ℝ)
      (G : ℝ → ℝ → Set (Z × Y)), SFinite μ → (∀ r s, MeasurableSet (G r s)) →
      (∀ r s s', s ≤ s' → G r s ⊆ G r s') →
      (∀ r s, 0 < r → G r s = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' s) →
      Measurable (fun z : Z => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ,
        μ {y | (z, y) ∈ G r s} / ENNReal.ofReal ((r * s) ^ k)) (𝓝[>] 0)) := by
  intro Z Y _ _ k μ δ G hμ hG hmono hcont
  -- `g z r s` is the section measure and `F z s` the supremum over `r ∈ (0, δ)`
  let g : Z → ℝ → ℝ → ℝ≥0∞ := fun z r s => μ {y | (z, y) ∈ G r s}
  let F : Z → ℝ → ℝ≥0∞ := fun z s => ⨆ r ∈ Ioo (0 : ℝ) δ, g z r s / ENNReal.ofReal ((r * s) ^ k)
  show Measurable fun z => limsup (F z) (𝓝[>] 0)
  have hgm : ∀ r s, Measurable fun z => g z r s := fun r s =>
    measurable_measure_prodMk_left (hG r s)
  -- `G` is monotone in `r` on `(0, ∞)`
  have hGr : ∀ s r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → G r₁ s ⊆ G r₂ s := by
    intro s r₁ r₂ h1 h12
    rcases h12.lt_or_eq with h | rfl
    · rw [hcont r₂ s (h1.trans h)]
      exact subset_biUnion_of_mem (u := fun r' => G r' s) ⟨h1, h⟩
    · exact le_rfl
  -- the supremum over `r` is a supremum over rational `r`
  have hFq : ∀ z s, 0 < s → F z s = ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
      g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := by
    intro z s hs
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      have hU : {y | (z, y) ∈ G r s} =
          ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, {y | (z, y) ∈ G (q.1 : ℝ) s} := by
        ext y
        simp only [mem_iUnion, mem_ofPred_eq]
        constructor
        · intro hy
          rw [hcont r s hr.1] at hy
          simp only [mem_iUnion] at hy
          obtain ⟨r', hr', hy'⟩ := hy
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr'.2
          exact ⟨⟨q, hr'.1.trans hq1, hq2⟩, hGr s r' q hr'.1 hq1.le hy'⟩
        · rintro ⟨q, hy⟩
          exact hGr s q r q.2.1 q.2.2.le hy
      have hdir : Directed (· ⊆ ·)
          (fun q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r} => {y | (z, y) ∈ G (q.1 : ℝ) s}) := by
        intro q₁ q₂
        refine ⟨⟨max q₁.1 q₂.1, ?_, ?_⟩, ?_, ?_⟩
        · exact lt_of_lt_of_le q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1)
        · rw [Rat.cast_max]; exact max_lt q₁.2.2 q₂.2.2
        · intro y hy
          exact hGr s q₁.1 _ q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1) hy
        · intro y hy
          exact hGr s q₂.1 _ q₂.2.1 (by exact_mod_cast le_max_right q₁.1 q₂.1) hy
      have hgr : g z r s = ⨆ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, g z (q.1 : ℝ) s := by
        show μ {y | (z, y) ∈ G r s} = _
        rw [hU]
        exact hdir.measure_iUnion
      rw [hgr, ENNReal.iSup_div]
      refine iSup_le fun q => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ) =>
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k)) q.1 ⟨q.2.1, q.2.2.trans hr.2⟩)
      apply ENNReal.div_le_div_left
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (mul_pos q.2.1 hs).le
      exact mul_le_mul_of_nonneg_right q.2.2.le hs.le
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) => g z r s / ENNReal.ofReal ((r * s) ^ k))
        (q : ℝ) hq
  have hFm : ∀ s, 0 < s → Measurable fun z => F z s := by
    intro s hs
    have : (fun z => F z s) = fun z => ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := funext fun z => hFq z s hs
    rw [this]
    exact Measurable.iSup fun q => Measurable.iSup fun _ => (hgm q s).div_const _
  -- scaling in `s`: `F z s ≤ (s'/s)ᵏ F z s'` for `0 < s ≤ s'`
  have hscale : ∀ z s s', 0 < s → s ≤ s' → F z s ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
    intro z s s' hs hss'
    refine iSup₂_le fun r hr => ?_
    have hs' : 0 < s' := hs.trans_le hss'
    have h1 : g z r s ≤ g z r s' := measure_mono (fun y hy => hmono r s s' hss' hy)
    have hA : ENNReal.ofReal ((r * s') ^ k) =
        ENNReal.ofReal ((s' / s) ^ k) * ENNReal.ofReal ((r * s) ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      congr 2
      field_simp
    have hc0 : ENNReal.ofReal ((s' / s) ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    calc g z r s / ENNReal.ofReal ((r * s) ^ k)
        ≤ g z r s' / ENNReal.ofReal ((r * s) ^ k) := ENNReal.div_le_div_right h1 _
      _ = ENNReal.ofReal ((s' / s) ^ k) * (g z r s' / ENNReal.ofReal ((r * s') ^ k)) := by
          rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
          gcongr
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            g z r s' / ENNReal.ofReal ((r * s') ^ k)) r hr
  -- the supremum over `s ∈ (0, ε)` is a supremum over rational `s`
  have hsupq : ∀ z (ε : ℝ), 0 < ε → ⨆ s ∈ Ioo (0 : ℝ) ε, F z s =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
    intro z ε hε
    apply le_antisymm
    · refine iSup₂_le fun s hs => ?_
      have hn : ∀ n : ℕ, F z s ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
          ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
        intro n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hlt : s < min ε (s * (1 + 1 / ((n : ℝ) + 1))) := by
          refine lt_min hs.2 ?_
          have := mul_pos hs.1 hpos
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        have hqε : (q : ℝ) < ε := hq2.trans_le (min_le_left _ _)
        have hq0 : 0 < (q : ℝ) := hs.1.trans hq1
        calc F z s ≤ ENNReal.ofReal (((q : ℝ) / s) ^ k) * F z q := hscale z s q hs.1 hq1.le
          _ ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
              ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
            gcongr ?_ * ?_
            · apply ENNReal.ofReal_le_ofReal
              apply pow_le_pow_left₀ (div_pos hq0 hs.1).le
              rw [div_le_iff₀ hs.1]
              have := hq2.trans_le (min_le_right _ _)
              linarith
            · exact le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε) => F z q) q
                ⟨hq0, hqε⟩
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k)) atTop
          (𝓝 1) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.tendsto_ofReal
        have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1).pow k
        simpa using this
      have htend := ENNReal.Tendsto.mul_const h1
        (Or.inl one_ne_zero) (b := ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q)
      rw [one_mul] at htend
      exact ge_of_tendsto' htend hn
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun s (_ : s ∈ Ioo (0 : ℝ) ε) => F z s) (q : ℝ) hq
  -- the upper limit along the radii `1/(n+1)`, with rational `s`
  have hform : ∀ z, limsup (F z) (𝓝[>] 0) = ⨅ n : ℕ, ⨆ q : ℚ,
      ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))), F z q := by
    intro z
    rw [Submission.rectifiability_mickle_rado_limsup_eq_iInf (F z)]
    congr 1
    funext n
    exact hsupq z _ (by positivity)
  rw [funext hform]
  exact Measurable.iInf fun n => Measurable.iSup fun q => Measurable.iSup fun hq => hFm q hq.1
/-- The parameter set of fibre witnesses (alternative T3 of the Besicovitch–Federer trichotomy in
the proof of Simon Ch. 6, 8.1) is Borel.  For `E ⊆ ℝ^N` σ-compact, `δ ∈ ℝ` and
`L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`), the set `W` of `(a, v)` admitting `x ∈ E` with
`x ≠ a`, `|x − a| < δ` and `L_v x = L_v a` is measurable.  With `E = ⋃ₙ Kₙ`, `Kₙ` compact,
`W = ⋃_{n,l} π(C_{n,l})`, where `π(x, (a, v)) = (a, v)` and `C_{n,l}` is the compact set of
`(x, (a, v))` with `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)` and
`L_v x = L_v a`. -/
theorem Submission.rectifiability_bf_witness_set_measurable : (∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → MeasurableSet {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))}) := by
  intro N m E δ hE
  -- `E = ⋃ₙ Kₙ` with every `Kₙ` compact.
  obtain ⟨K, hK, hKE⟩ := hE
  -- `(x, (a, v)) ↦ L_v x` and `(x, (a, v)) ↦ L_v a` are continuous.
  have hLc : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner continuous_fst
  have hLc' : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner
      (continuous_fst.comp continuous_snd)
  -- `C_{n,l}`: `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)`, `L_v x = L_v a`.
  let C : ℕ → ℕ → Set (Eucl N × (Eucl N × (Fin (m + 1) → Eucl N))) := fun n l =>
    (K n ×ˢ closedBall (0 : Eucl N × (Fin (m + 1) → Eucl N)) l) ∩
      ({q | 1 / ((l : ℝ) + 1) ≤ dist q.1 q.2.1} ∩ {q | dist q.1 q.2.1 ≤ δ - 1 / ((l : ℝ) + 1)} ∩
        {q | (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1)) =
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))})
  -- A compact set intersected with closed conditions is compact.
  have hCc : ∀ n l, IsCompact (C n l) := by
    intro n l
    refine ((hK n).prod (isCompact_closedBall _ _)).inter_right ?_
    refine ((isClosed_le continuous_const ?_).inter (isClosed_le ?_ continuous_const)).inter
      (isClosed_eq hLc hLc')
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
  -- `W = ⋃_{n,l} π(C_{n,l})`, choosing `l` by the Archimedean property.
  have key : {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) =
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))} =
      ⋃ n, ⋃ l : ℕ, Prod.snd '' C n l := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨x, hxE, hxa, hxδ, hL⟩
      rw [← hKE, mem_iUnion] at hxE
      obtain ⟨n, hn⟩ := hxE
      have hd0 : 0 < dist x p.1 := dist_pos.2 hxa
      have hmin : 0 < min (dist x p.1) (δ - dist x p.1) := lt_min hd0 (by linarith)
      obtain ⟨l₁, hl₁⟩ := exists_nat_one_div_lt hmin
      obtain ⟨l₂, hl₂⟩ := exists_nat_ge ‖p‖
      refine ⟨n, max l₁ l₂, (x, p), ?_, rfl⟩
      have hle : 1 / ((max l₁ l₂ : ℕ) + 1 : ℝ) ≤ 1 / ((l₁ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (l₁ : ℝ) ≤ ((max l₁ l₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left l₁ l₂
        linarith
      have h1 := lt_of_le_of_lt hle hl₁
      refine ⟨⟨hn, ?_⟩, ⟨?_, ?_⟩, hL⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hl₂.trans (by exact_mod_cast le_max_right l₁ l₂)
      · exact (h1.trans_le (min_le_left _ _)).le
      · have := h1.trans_le (min_le_right _ _)
        simp only [mem_ofPred_eq]
        linarith
    · rintro ⟨n, l, q, ⟨⟨hq1, -⟩, ⟨hd1, hd2⟩, hL⟩, rfl⟩
      refine ⟨q.1, ?_, ?_, ?_, hL⟩
      · rw [← hKE]; exact mem_iUnion.2 ⟨n, hq1⟩
      · intro h
        have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq, h, dist_self] at hd1
        linarith
      · have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq] at hd2
        linarith
  -- Each `π(C_{n,l})` is compact, hence Borel; so is the countable union.
  rw [key]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun l =>
    ((hCc n l).image continuous_snd).measurableSet

/-- **Borel measurability of the cone ratio** (step 2(a)–(c) of the Besicovitch–Federer
trichotomy, Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 18.9).  For
`v ∈ (ℝ^N)^k`, `k = m + 1`, let `L_v y = (⟨v₁, y⟩, …, ⟨v_k, y⟩)` and
`X_v(a, r, s) = {x : |x - a| < r, |L_v (x - a)| < s |x - a|}`.  Then
`Φ(a, v) = limsup_{s → 0⁺} sup_{0 < r < δ} μ(X_v(a, r, s)) / (rs)ᵏ` is measurable in `(a, v)`:
the cones are the sections of `G(r, s) = {((a, v), x) : |x - a| < r, |L_v (x - a)| < s |x - a|}`,
which is open, monotone in `s` and left continuous in `r`, so `limsup_sup_measurable` applies. -/
theorem Submission.rectifiability_bf_cone_ratio_measurable : ∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ), SFinite μ → Measurable (fun p : Eucl N × (Fin (m + 1) → Eucl N) => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) := by
  intro N m μ δ hμ
  -- Step 1: the cone `X_v(a, r, s)` is the section of `G(r, s)` at `z = (a, v)`.
  refine Submission.rectifiability_bf_limsup_sup_measurable (Eucl N × (Fin (m + 1) → Eucl N))
    (Eucl N) (m + 1) μ δ (fun r s => {q | dist q.2 q.1.1 < r ∧
      ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) : Eucl (m + 1))‖ <
        s * ‖q.2 - q.1.1‖}) hμ ?_ ?_ ?_
  -- Step 2: `G(r, s)` is open (strict inequalities between continuous functions), hence
  -- measurable in the second-countable product.
  · intro r s
    have hL : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N =>
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) :
          Eucl (m + 1))‖ :=
      continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
        ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).inner
          (continuous_snd.sub (continuous_fst.comp continuous_fst))))
    have hd : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N => dist q.2 q.1.1 :=
      by fun_prop
    have hn : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N =>
        s * ‖q.2 - q.1.1‖ := by fun_prop
    exact ((isOpen_lt hd continuous_const).inter (isOpen_lt hL hn)).measurableSet
  -- Step 3: `G(r, s)` is monotone in `s`, as `s |x - a| ≤ s' |x - a|` for `s ≤ s'`.
  · intro r s s' hss' q hq
    exact ⟨hq.1, hq.2.trans_le (by gcongr)⟩
  -- Step 4: `G(r, s) = ⋃_{0 < r' < r} G(r', s)`; for `|x - a| < r` take `r' = (|x - a| + r) / 2`.
  · intro r s hr
    ext q
    simp only [mem_iUnion, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 q.1.1 + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨-, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
/-- Cone-ratio dichotomy.  Write `L x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`),
`X(r, s) = {x : |x − a| < r, |L(x − a)| < s|x − a|}` and
`Φ = limsup_{s→0⁺} sup_{0<r<δ} μ(X(r, s))/(rs)ᵏ`.  If `Φ = 0`, then for each `η > 0` some
`s ∈ (0, 1)` has `μ(X(r, s)) ≤ η(rs)ᵏ` for all `r ∈ (0, δ)`.  If `Φ = ∞`, then
`X(r, s) ⊆ L⁻¹(B̄(La, rs))`, so the push-forward `L_# μ` has infinite upper `k`-density at
`La`: its density quotients at the radii `rs → 0⁺` are unbounded. -/
theorem Submission.rectifiability_bf_cone_ratio_reduction :
    (∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (v : Fin (m + 1) → Eucl N),
      (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = 0 →
        ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∧
      (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = ⊤ →
        dimensionalUpperDensity (Measure.map (fun x : Eucl N =>
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) μ).toOuterMeasure
          ((m + 1 : ℕ) : ℝ) univ
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤)) := by
  intro N m μ δ a v
  -- `X r s` is the cone, `F s` the supremum of the ratios `μ(X r s)/(rs)ᵏ` over `r ∈ (0, δ)`
  set X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧
    ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}
  set F : ℝ → ℝ≥0∞ := fun s =>
    ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1)) with hF
  constructor
  · -- `Φ = 0`: eventually `F s < η`; take such an `s ∈ (0, 1)`
    intro h0 η hη
    have hlt : limsup F (𝓝[>] 0) < ENNReal.ofReal η := by
      rw [h0]; exact ENNReal.ofReal_pos.2 hη
    obtain ⟨s, hs1, hs2⟩ :=
      ((eventually_lt_of_limsup_lt hlt).and (Ioo_mem_nhdsGT one_pos)).exists
    refine ⟨s, hs2, fun r hr => ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos (mul_pos hr.1 hs2.1) _
    have h3 : μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1)) < ENNReal.ofReal η :=
      (le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
        μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))) r hr).trans_lt hs1
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 hpos).ne') (Or.inl ENNReal.ofReal_ne_top)]
      at h3
    rw [ENNReal.ofReal_mul hη.le]
    exact h3.le
  · -- `Φ = ∞`: ratios above `b ω_k` at `r < δ`, small `s` give density quotients above `b` at `rs`
    intro htop
    set L : Eucl N → Eucl (m + 1) := fun x =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) with hL
    have hLc : Continuous L :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_const.inner continuous_id)
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      simp only [hL, ← WithLp.toLp_sub]
      congr 1
      funext i
      simp [inner_sub_right]
    set ω := Poincare.SimonGMT.Chapter01.realUnitBallVolume (((m + 1 : ℕ) : ℝ)) with hω
    have hω0 : ω ≠ 0 := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      refine (ENNReal.ofReal_pos.2 (div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
        (Real.Gamma_pos_of_pos ?_))).ne'
      positivity
    have hωt : ω ≠ ⊤ := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      exact ENNReal.ofReal_ne_top
    -- `δ > 0`, since otherwise `F = 0` and `Φ = 0`
    have hδ : 0 < δ := by
      by_contra hδ
      have hF0 : F = fun _ => 0 := by
        funext s
        rw [hF, Ioo_eq_empty (not_lt.2 (not_lt.1 hδ))]
        simp
      rw [hF0, limsup_const] at htop
      exact ENNReal.zero_ne_top htop
    unfold dimensionalUpperDensity
    refine ENNReal.eq_top_of_forall_nnreal_le fun b => ?_
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    rw [(nhdsGT_basis (0 : ℝ)).frequently_iff]
    intro ρ₀ hρ₀
    have hΛ : (b : ℝ≥0∞) * ω < limsup F (𝓝[>] 0) := by
      rw [htop]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.2 hωt)
    obtain ⟨s, hs1, hs2⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hΛ).and_eventually
      (Ioo_mem_nhdsGT (div_pos hρ₀ hδ))).exists
    obtain ⟨r, hr, hrs⟩ := lt_biSup_iff.1 hs1
    have hrs0 : 0 < r * s := mul_pos hr.1 hs2.1
    have hrsρ : r * s < ρ₀ := by
      have h1 : r * s < δ * (ρ₀ / δ) := mul_lt_mul'' hr.2 hs2.2 hr.1.le hs2.1.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at h1
    refine ⟨r * s, ⟨hrs0, hrsρ⟩, ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos hrs0 _
    -- the cone lies in the preimage of the closed ball `B̄(La, rs)`
    have hsub : X r s ⊆ L ⁻¹' closedBall (L a) (r * s) := by
      intro x hx
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, hLsub]
      have h1 : ‖x - a‖ < r := by rw [← dist_eq_norm]; exact hx.1
      calc ‖L (x - a)‖ ≤ s * ‖x - a‖ := hx.2.le
        _ ≤ s * r := by gcongr; exact hs2.1.le
        _ = r * s := mul_comm _ _
    have hmap :
        μ (X r s) ≤ (Measure.map L μ).toOuterMeasure (univ ∩ closedBall (L a) (r * s)) := by
      rw [Measure.coe_toOuterMeasure, univ_inter,
        Measure.map_apply hLc.measurable isClosed_closedBall.measurableSet]
      exact measure_mono hsub
    unfold Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
    rw [ENNReal.ofReal_rpow_of_nonneg hrs0.le (by positivity), Real.rpow_natCast,
      ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 (ENNReal.ofReal_pos.2 hpos).ne'))
        (Or.inl (ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top))]
    refine le_trans ?_ hmap
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at hrs
    rw [← mul_assoc]
    exact hrs.le
/-- Cones versus unions of coordinate fibres (step 4 of the Besicovitch–Federer trichotomy,
Mattila 18.9, used for Simon Ch. 6, 8.1).  Let `k = m + 1`, `L_u(y) = (⟨u₁, y⟩, …, ⟨u_k, y⟩)`,
`X_u(a, r, s) = {x : |x − a| < r, |L_u(x − a)| < s|x − a|}`, `u ⊕_j c = (uᵢ + cᵢ e_j)ᵢ` and
`K_j(t) = {x ≠ a : L_{u ⊕_j c}(x − a) = 0 for some |c| < t}`.  With
`Φ = limsup_{s → 0⁺} sup_{0<r<δ} μ(X_u(a, r, s))/(rs)ᵏ` and
`ϑ_j = limsup_{t → 0⁺} sup_{0<r<δ} μ(B(a, r) ∩ K_j(t))/(rt)ᵏ`, we have `ϑ_j ≤ Φ` for every `j`
and `Φ ≤ (√N)ᵏ Σ_j ϑ_j`.  Since `L_{u ⊕_j c}(y) = L_u(y) + y_j c`,
`B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` and `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(√N s)`. -/
theorem Submission.rectifiability_bf_fibre_cone_comparison :
    ∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (u : Fin (m + 1) → Eucl N), (∀ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ≤ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) ∧ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) := by
  intro N m μ δ a u
  -- `L = L_u`, `K j t = K_j(t)`, `X r s = X_u(a, r, s)`, `F = F`, `Fj j = F_j`.
  let L : Eucl N → Eucl (m + 1) := fun y => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let K : Fin N → ℝ → Set (Eucl N) := fun j t => {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t,
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧ ‖L (x - a)‖ < s * ‖x - a‖}
  let F : ℝ → ℝ≥0∞ := fun s => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
  let Fj : Fin N → ℝ → ℝ≥0∞ := fun j t => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ K j t) / ENNReal.ofReal ((r * t) ^ (m + 1))
  show (∀ j, limsup (Fj j) (𝓝[>] 0) ≤ limsup F (𝓝[>] 0)) ∧
    limsup F (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (Fj j) (𝓝[>] 0)
  -- Step 1, fibre identity: `L_{u ⊕_j c}(y) = L_u(y) + y_j c`.
  have hfib : ∀ (j : Fin N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) : Eucl (m + 1)) =
        L y + (y j) • c := by
    intro j c y
    ext i
    simp [L, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  -- Step 2, inclusion (ii): `B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` for `t > 0`.
  have hincl2 : ∀ (j : Fin N) (r t : ℝ), 0 < t → ball a r ∩ K j t ⊆ X r t := by
    rintro j r t ht x ⟨hxr, hxa, c, hc, hx0⟩
    refine ⟨hxr, ?_⟩
    rw [hfib] at hx0
    have hL : L (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left hx0
    rw [hL, norm_neg, norm_smul]
    have hy : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hxa)
    have hc' : ‖c‖ < t := by simpa using hc
    have hyj : ‖(x - a) j‖ ≤ ‖x - a‖ := PiLp.norm_apply_le _ _
    calc ‖(x - a) j‖ * ‖c‖ ≤ ‖x - a‖ * ‖c‖ := by gcongr
      _ < ‖x - a‖ * t := mul_lt_mul_of_pos_left hc' hy
      _ = t * ‖x - a‖ := mul_comm _ _
  refine ⟨fun j => ?_, ?_⟩
  -- Step 3: `F_j ≤ F` on `(0, ∞)`, hence `ϑ_j ≤ Φ`.
  · refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine iSup₂_mono fun r hr => ?_
    exact ENNReal.div_le_div_right (measure_mono (hincl2 j r t ht)) _
  · rcases Nat.eq_zero_or_pos N with hN | hN
    -- Step 4: for `N = 0` every cone is empty, so `Φ = 0`.
    · subst hN
      have hF0 : F = fun _ => 0 := by
        funext s
        have hX : ∀ r, X r s = ∅ := by
          intro r
          ext x
          have hxa : x - a = 0 := Subsingleton.elim _ _
          simp [X, hxa]
        simp [F, hX]
      rw [hF0, limsup_const]
      exact zero_le
    · set σ : ℝ := Real.sqrt (N : ℝ) with hσdef
      have hσ : 0 < σ := Real.sqrt_pos.2 (by exact_mod_cast hN)
      have hσsq : σ ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      -- Step 5, inclusion (i): `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(σ s)` for `s > 0`.
      have hincl1 : ∀ r s, 0 < s → X r s ⊆ ⋃ j, ball a r ∩ K j (σ * s) := by
        rintro r s hs x ⟨hxr, hx⟩
        set y := x - a with hydef
        have hy : 0 < ‖y‖ := by
          rcases (norm_nonneg y).lt_or_eq with h | h
          · exact h
          · exfalso
            rw [← h, mul_zero] at hx
            exact (norm_nonneg _).not_gt hx
        obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖y j‖)
          (Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩)
        have hsq : ‖y‖ ^ 2 ≤ (σ * ‖y j‖) ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2, mul_pow, hσsq]
          calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin N, ‖y j‖ ^ 2 :=
                Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hj i (Finset.mem_univ i)) 2
            _ = (N : ℝ) * ‖y j‖ ^ 2 := by simp
        have hle : ‖y‖ ≤ σ * ‖y j‖ :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
        have hyj : 0 < ‖y j‖ := by
          by_contra hcon
          have : ‖y j‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
          rw [this, mul_zero] at hle
          linarith
        have hyj0 : y j ≠ 0 := norm_pos_iff.1 hyj
        refine mem_iUnion.2 ⟨j, mem_ball.2 hxr, ?_, (-(y j)⁻¹) • L y, ?_, ?_⟩
        · intro h
          rw [hydef, h, sub_self, norm_zero] at hy
          exact lt_irrefl _ hy
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv]
          rw [inv_mul_lt_iff₀ hyj]
          calc ‖L y‖ < s * ‖y‖ := hx
            _ ≤ s * (σ * ‖y j‖) := by gcongr
            _ = ‖y j‖ * (σ * s) := by ring
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj0, neg_smul, one_smul, add_neg_cancel]
      -- Step 6, pointwise bound: `F(s) ≤ σᵏ Σ_j F_j(σ s)` for `s > 0`.
      have hpt : ∀ s, 0 < s → F s ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by
        intro s hs
        refine iSup₂_le fun r hr => ?_
        have hc0 : ENNReal.ofReal (σ ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
        have hA : ENNReal.ofReal ((r * (σ * s)) ^ (m + 1)) =
            ENNReal.ofReal (σ ^ (m + 1)) * ENNReal.ofReal ((r * s) ^ (m + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          congr 2
          ring
        calc μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
            ≤ (∑ j, μ (ball a r ∩ K j (σ * s))) / ENNReal.ofReal ((r * s) ^ (m + 1)) := by
              refine ENNReal.div_le_div_right ?_ _
              exact (measure_mono (hincl1 r s hs)).trans (measure_iUnion_fintype_le μ _)
          _ = ∑ j, ENNReal.ofReal (σ ^ (m + 1)) *
                (μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) := by
              rw [ENNReal.sum_div]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
          _ ≤ ∑ j, ENNReal.ofReal (σ ^ (m + 1)) * Fj j (σ * s) := by
              refine Finset.sum_le_sum fun j _ => ?_
              gcongr
              exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) r hr
          _ = ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by rw [Finset.mul_sum]
      -- Step 8: `limsup` is subadditive along `𝓝[>] 0` (direct `ε`-argument).
      have hadd : ∀ (v w : ℝ → ℝ≥0∞), limsup (fun s => v s + w s) (𝓝[>] (0 : ℝ)) ≤
          limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) := by
        intro v w
        refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
        have hv : limsup v (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_self_add hlt
        have hw : limsup w (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_add_self hlt
        have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by
          simp [ENNReal.div_eq_zero_iff, hε.ne']
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv.ne hε2),
          eventually_lt_of_limsup_lt (ENNReal.lt_add_right hw.ne hε2)] with x h1 h2
        calc v x + w x ≤ (limsup v (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) + (limsup w (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) :=
              add_le_add h1.le h2.le
          _ = limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) + ε := by
              rw [add_add_add_comm, ENNReal.add_halves]
      have hsum : ∀ (S : Finset (Fin N)) (h : Fin N → ℝ → ℝ≥0∞),
          limsup (fun s => ∑ j ∈ S, h j s) (𝓝[>] (0 : ℝ)) ≤ ∑ j ∈ S, limsup (h j) (𝓝[>] 0) := by
        intro S h
        induction S using Finset.induction_on with
        | empty => simp
        | insert j S hj ih =>
          simp only [Finset.sum_insert hj]
          exact (hadd (h j) (fun s => ∑ i ∈ S, h i s)).trans (add_le_add le_rfl ih)
      -- Step 9, change of variable `t = σ s`: `s ↦ σ s` maps `𝓝[>] 0` into `𝓝[>] 0`.
      have hT : Tendsto (fun s : ℝ => σ * s) (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => σ * s) (𝓝 0) (𝓝 (σ * 0)) :=
            ((continuous_const.mul continuous_id).tendsto 0)
          rw [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact mul_pos hσ hs
      have hcv : ∀ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ)) ≤ limsup (Fj j) (𝓝[>] 0) := by
        intro j
        calc limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ))
            = limsup (Fj j) (map (fun s : ℝ => σ * s) (𝓝[>] 0)) := Filter.limsup_comp (Fj j) _ _
          _ ≤ limsup (Fj j) (𝓝[>] 0) := limsup_le_limsup_of_le hT (by isBoundedDefault) (by isBoundedDefault)
      -- Steps 7 and 10: pull out the constant `σᵏ`, then apply steps 8 and 9.
      calc limsup F (𝓝[>] 0) ≤ limsup (fun s => ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s)) (𝓝[>] 0) := by
            refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
            filter_upwards [self_mem_nhdsWithin] with s hs
            exact hpt s hs
        _ = ENNReal.ofReal (σ ^ (m + 1)) * limsup (fun s => ∑ j, Fj j (σ * s)) (𝓝[>] 0) :=
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] 0) := by
            gcongr
            exact hsum Finset.univ (fun j s => Fj j (σ * s))
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (Fj j) (𝓝[>] 0) := by
            gcongr with j
            exact hcv j

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
