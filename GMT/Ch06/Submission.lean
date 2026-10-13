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

/-- Coordinates of a Borel `k`-vector field in an isometric chart `J` of the `k`-covectors:
`u(x) = (v(x)(J⁻¹eᵢ))ᵢ` is Borel, `‖u‖ ≤ 1`, `‖u‖ = 1` `μ`-a.e. and `v(x)(α) = ⟨Jα, u(x)⟩`. -/
theorem Submission.smr_ufd_unit_coord_field :
    ∀ (P k N : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k)
      (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖) →
      (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) →
      (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) →
      (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) →
      ∃ u : Eucl P → EuclideanSpace ℝ (Fin N), Measurable u ∧ (∀ x, ‖u x‖ ≤ 1) ∧
        (∀ᵐ x ∂μ, ‖u x‖ = 1) ∧
        ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x) := by
  intro P k N μ v J hJ hv hmeas hae
  -- Coordinates in the chart `J`: `u(x)ᵢ = v(x)(J⁻¹eᵢ)`.
  let u : Eucl P → EuclideanSpace ℝ (Fin N) := fun x =>
    WithLp.toLp 2 (fun i => v x (J.symm (EuclideanSpace.single i 1)))
  -- Pairing formula `v(x)(α) = ⟨Jα, u(x)⟩`, by expanding `Jα` in the standard basis.
  have hpair : ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x) := by
    intro x α
    have hexp : J α = ∑ i, (J α) i • EuclideanSpace.single i (1 : ℝ) := by
      simpa [EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (J α)).symm
    conv_lhs => rw [← J.symm_apply_apply α, hexp]
    simp [map_sum, map_smul, PiLp.inner_apply, u, mul_comm]
  -- `‖u(x)‖ ≤ 1`: test with `α = J⁻¹u(x)`, so `‖u(x)‖² = v(x)(α) ≤ |α| = ‖u(x)‖`.
  have hle : ∀ x, ‖u x‖ ≤ 1 := by
    intro x
    have h1 : ‖u x‖ ^ 2 ≤ ‖u x‖ := by
      have := hv x (J.symm (u x))
      rw [hpair, hJ, LinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq] at this
      exact (le_abs_self _).trans this
    by_contra h
    nlinarith [norm_nonneg (u x), not_le.mp h]
  refine ⟨u, ?_, hle, ?_, hpair⟩
  · exact (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp (measurable_pi_iff.mpr fun i => hmeas _)
  -- `‖u(x)‖ = 1` a.e.: by Cauchy–Schwarz, `1 = v(x)(α) = ⟨Jα, u(x)⟩ ≤ |α| ‖u(x)‖ ≤ ‖u(x)‖`.
  · filter_upwards [hae] with x ⟨α, hα, hvα⟩
    refine le_antisymm (hle x) ?_
    have h2 : (1 : ℝ) ≤ ‖J α‖ * ‖u x‖ := by
      rw [← hvα, hpair]
      exact real_inner_le_norm _ _
    rw [← hJ] at h2
    nlinarith [norm_nonneg (u x), covectorEuclideanNorm_nonneg α]
/-- Compact inner approximation inside an open `W ⊆ U`: if `μ` is finite on compact subsets of
`U`, `E` is Borel and `c < μ (W ∩ E)`, then some compact `K ⊆ W ∩ E` has `c < μ K`. -/
theorem Submission.smr_ufd_cl_inner_compact : ∀ (P : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → ∀ E : Set (Eucl P), MeasurableSet E → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < μ (W ∩ E) → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ W ∩ E ∧ c < μ K := by
  intro P U μ hfin E hE W hW hWU c hc
  -- Step 1: compact sets `K j = F j ∩ closedBall 0 j ⊆ W`, increasing, with `⋃ j, K j = W`,
  -- where `F j` are closed, increasing and exhaust `W`.
  obtain ⟨F, hFc, hFW, hFU, hFm⟩ := hW.exists_iUnion_isClosed
  set K : ℕ → Set (Eucl P) := fun j => F j ∩ closedBall 0 j
  have hKc : ∀ j, IsCompact (K j) := fun j => (isCompact_closedBall 0 (j : ℝ)).inter_left (hFc j)
  have hKW : ∀ j, K j ⊆ W := fun j => inter_subset_left.trans (hFW j)
  have hKm : Monotone K := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j, K j = W := by
    refine Subset.antisymm (iUnion_subset hKW) fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i n, hFm (le_max_left i n) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hn.trans (Nat.cast_le.2 (le_max_right i n))
  -- Step 2: continuity from below gives `j` with `c < μ (E ∩ K j)`.
  have hlim : Tendsto (fun j => μ (E ∩ K j)) atTop (𝓝 (μ (W ∩ E))) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun j => E ∩ K j)
      (fun i j hij => inter_subset_inter_right E (hKm hij))
    rwa [← inter_iUnion, hKU, inter_comm E W] at h
  obtain ⟨j, hj⟩ := ((tendsto_order.1 hlim).1 c hc).exists
  -- Step 3: `E' = E ∩ K j` is Borel, `E' ⊆ W ∩ E` and `μ E' ≤ μ (K j) < ∞`.
  set E' := E ∩ K j
  have hE'm : MeasurableSet E' := hE.inter (hKc j).isClosed.measurableSet
  have hE'W : E' ⊆ W ∩ E := fun x hx => ⟨hKW j hx.2, hx.1⟩
  have hE'fin : μ E' < ∞ :=
    (measure_mono inter_subset_right).trans_lt (hfin _ (hKc j) ((hKW j).trans hWU))
  -- Step 4: the finite measure `μ ⌞ E'` on `ℝ^P` is inner regular by compact sets.
  have : IsFiniteMeasure (μ.restrict E') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hE'fin⟩
  have hcE' : c < μ.restrict E' E' := by rwa [Measure.restrict_apply_self]
  obtain ⟨L, hLE', hLc, hL⟩ :=
    hE'm.exists_lt_isCompact_of_ne_top (μ := μ.restrict E') (measure_ne_top _ E') hcE'
  -- Step 5: `L` is compact, `L ⊆ E' ⊆ W ∩ E` and `c < μ L`.
  refine ⟨L, hLc, hLE'.trans hE'W, ?_⟩
  rwa [Measure.restrict_eq_self μ hLE'] at hL
/-- Lusin's theorem with compact sets (Simon Ch. 1, 1.17, applied coordinatewise): if `μ` is a
measure on `ℝ^P`, `u : ℝ^P → ℝ^N` is Borel and `A ⊆ ℝ^P` is Borel with `μ(A) < ∞`, then for every
`ε > 0` there is a compact `C ⊆ A` with `μ(A ∖ C) < ε` and `u|C` continuous. -/
theorem Submission.smr_ufd_cl_vector_lusin : ∀ (P N : ℕ) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable u → ∀ A : Set (Eucl P), MeasurableSet A → μ A ≠ ∞ → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ A ∧ μ (A \ C) < ε ∧ ContinuousOn u C := by
  intro P N μ u hu A hA hAfin ε hε
  -- Step 1: every Borel `S` with `μ(S) < ∞` has, for every `δ > 0`, a compact (hence closed)
  -- `F ⊆ S` with `μ(S ∖ F) < δ`: the finite measure `ν = μ ⌞ S` is regular on `ℝ^P`, and
  -- `ν = μ` on subsets of `S`.
  have hreg : ∀ S : Set (Eucl P), MeasurableSet S → μ S ≠ ∞ → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ S, IsCompact F ∧ IsClosed F ∧ μ (S \ F) < δ := by
    intro S hS hSfin δ hδ
    have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
    have : (μ.restrict S).Regular :=
      Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    obtain ⟨F, hFS, hFc, hFcl, hFlt⟩ :=
      hS.exists_isCompact_isClosed_sdiff_lt (μ := μ.restrict S) (measure_ne_top _ _) hδ
    refine ⟨F, hFS, hFc, hFcl, ?_⟩
    rwa [Measure.restrict_apply (hS.diff hFcl.measurableSet), inter_eq_left.2 sdiff_subset]
      at hFlt
  -- Step 2: an error budget `0 < η < ∞` with `(N + 1) η < ε`.
  obtain ⟨η, hη0, hηε⟩ :=
    ENNReal.exists_pos_mul_lt (a := ((N + 1 : ℕ) : ℝ≥0∞)) (ENNReal.natCast_ne_top _) hε
  have hηtop : η ≠ ∞ := by
    rintro rfl
    rw [ENNReal.top_mul (by exact_mod_cast Nat.succ_ne_zero N)] at hηε
    exact not_top_lt hηε
  -- Step 3: the coordinates `u_i = (u ·) i` are Borel.
  have hui : ∀ i : Fin N, Measurable fun x => u x i := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hu
  -- Step 4: Lusin's theorem (Simon Ch. 1, 1.17) on `A` for a Borel `f : ℝ^P → ℝ`, with the
  -- closed regularity of Step 1.  SimonGMT's `Chapter01.Lusin` is outside the frozen imports, so
  -- it is proved here through a countable basis `(b k)` of `ℝ`: closed `G k ⊆ A ∩ f⁻¹(b k)` and
  -- `H k ⊆ A ∖ f⁻¹(b k)` with defects `< δ k`, `∑ δ k < η / 2`, and `F = ⋂ k, (G k ∪ H k)`.
  have hlusin : ∀ f : Eucl P → ℝ, Measurable f →
      ∃ F ⊆ A, IsClosed F ∧ μ (A \ F) < η ∧ ContinuousOn f F := by
    intro f hf
    obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis ℝ
    have hbo : ∀ k, IsOpen (b k) := fun k => hb.isOpen (mem_range_self k)
    obtain ⟨δ, hδ0, hδη⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hη0.ne').ne' ℕ
    have hδ : ∀ k, ((δ k : ℝ≥0) : ℝ≥0∞) ≠ 0 := fun k => ENNReal.coe_ne_zero.2 (hδ0 k).ne'
    choose G hGA hGc hGcl hGlt using fun k =>
      hreg _ (hA.inter (hf (hbo k).measurableSet))
        (ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)) (δ k) (hδ k)
    choose H hHA hHc hHcl hHlt using fun k =>
      hreg _ (hA.diff (hf (hbo k).measurableSet))
        (ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)) (δ k) (hδ k)
    refine ⟨⋂ k, (G k ∪ H k), ?_, isClosed_iInter fun k => (hGcl k).union (hHcl k), ?_, ?_⟩
    · exact (iInter_subset _ 0).trans
        (union_subset ((hGA 0).trans inter_subset_left) ((hHA 0).trans sdiff_subset))
    -- `A ∖ F ⊆ ⋃ k, ((A ∩ f⁻¹(b k)) ∖ G k ∪ (A ∖ f⁻¹(b k)) ∖ H k)`.
    · calc μ (A \ ⋂ k, (G k ∪ H k))
          ≤ μ (⋃ k, ((A ∩ f ⁻¹' b k) \ G k ∪ (A \ f ⁻¹' b k) \ H k)) := by
            refine measure_mono fun x hx => ?_
            obtain ⟨k, hk⟩ : ∃ k, x ∉ G k ∪ H k := by
              by_contra! h
              exact hx.2 (mem_iInter.2 h)
            refine mem_iUnion.2 ⟨k, ?_⟩
            by_cases hxb : f x ∈ b k
            · exact Or.inl ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inr h)⟩
        _ ≤ ∑' k, μ ((A ∩ f ⁻¹' b k) \ G k ∪ (A \ f ⁻¹' b k) \ H k) := measure_iUnion_le _
        _ ≤ ∑' k, ((δ k : ℝ≥0∞) + δ k) := ENNReal.tsum_le_tsum fun k =>
            (measure_union_le _ _).trans (add_le_add (hGlt k).le (hHlt k).le)
        _ = ∑' k, (δ k : ℝ≥0∞) + ∑' k, (δ k : ℝ≥0∞) := ENNReal.tsum_add
        _ < η / 2 + η / 2 := ENNReal.add_lt_add hδη hδη
        _ = η := ENNReal.add_halves η
    -- `f⁻¹(b k) ∩ F = (H k)ᶜ ∩ F` is relatively open in `F` for every basic open set `b k`.
    · rw [hb.continuousOn_iff]
      rintro t ⟨k, rfl⟩
      refine ⟨(H k)ᶜ, (hHcl k).isOpen_compl, ?_⟩
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
      constructor
      · rintro ⟨hxb, hxF⟩
        exact ⟨fun hxH => ((hHA k) hxH).2 hxb, hxF⟩
      · rintro ⟨hxH, hxF⟩
        refine ⟨?_, hxF⟩
        rcases mem_iInter.1 hxF k with hxG | hxH'
        · exact ((hGA k) hxG).2
        · exact absurd hxH' hxH
  -- For each coordinate `i`: a closed `F i ⊆ A` with `μ(A ∖ F i) < η` and `u_i` continuous
  -- on `F i`.
  choose F hFA hFcl hFlt hFcont using fun i => hlusin _ (hui i)
  -- Step 5: a compact `K ⊆ A` with `μ(A ∖ K) < η`.
  obtain ⟨K, hKA, hKc, -, hKlt⟩ := hreg A hA hAfin η hη0.ne'
  -- Step 6: `C = K ∩ ⋂ i, F i` is compact and `C ⊆ K ⊆ A`.
  refine ⟨K ∩ ⋂ i, F i, hKc.inter_right (isClosed_iInter hFcl), inter_subset_left.trans hKA,
    ?_, ?_⟩
  -- Step 8: `A ∖ C ⊆ (A ∖ K) ∪ ⋃ i, (A ∖ F i)`, so `μ(A ∖ C) < η + N η = (N + 1) η < ε`.
  · have hsum : ∑ i, μ (A \ F i) ≤ ∑ _i : Fin N, η :=
      Finset.sum_le_sum fun i _ => (hFlt i).le
    have hsum_ne_top : ∑ i, μ (A \ F i) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun _ _ => hηtop) hsum
    calc μ (A \ (K ∩ ⋂ i, F i))
        ≤ μ ((A \ K) ∪ ⋃ i, (A \ F i)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ K
          · obtain ⟨i, hi⟩ : ∃ i, x ∉ F i := by
              by_contra! h
              exact hx.2 ⟨hxK, mem_iInter.2 h⟩
            exact Or.inr (mem_iUnion.2 ⟨i, hx.1, hi⟩)
          · exact Or.inl ⟨hx.1, hxK⟩
      _ ≤ μ (A \ K) + ∑ i, μ (A \ F i) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
      _ < η + ∑ _i : Fin N, η := ENNReal.add_lt_add_of_lt_of_le hsum_ne_top hKlt hsum
      _ = η * ((N + 1 : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ < ε := hηε
  -- Step 7: every coordinate of `u` is continuous on `C ⊆ F i`, hence so is `u`.
  · have h : ContinuousOn (fun x => WithLp.ofLp (u x)) (K ∩ ⋂ i, F i) :=
      continuousOn_pi.2 fun i => (hFcont i).mono (inter_subset_right.trans (iInter_subset _ i))
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn h

/-- Lusin's theorem with compact sets of large measure (Simon Ch. 1, 1.17, with inner regularity;
used for Ch. 6, 2.7–2.9): let `μ` be finite on compact subsets of `U`, `u : ℝ^P → ℝ^N` Borel,
`E` Borel and `W ⊆ U` open.  If `c < μ(W ∩ E)`, then some compact `C ⊆ W ∩ E` has `c < μ(C)`
and `u|C` continuous. -/
theorem Submission.smr_ufd_compact_lusin_set :
    ∀ (P N : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)),
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → Measurable u →
      ∀ E : Set (Eucl P), MeasurableSet E → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U →
      ∀ c : ℝ≥0∞, c < μ (W ∩ E) →
        ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ W ∩ E ∧ c < μ C ∧ ContinuousOn u C := by
  intro P N U μ u hfin hu E hE W hW hWU c hc
  -- Inner regularity: a compact `C₀ ⊆ W ∩ E` with `c < μ(C₀)`.
  obtain ⟨C₀, hC₀, hC₀WE, hcC₀⟩ :=
    Submission.smr_ufd_cl_inner_compact P U μ hfin E hE W hW hWU c hc
  -- `C₀` is a compact subset of `W ⊆ U`, so `μ(C₀) < ∞`.
  have hC₀fin : μ C₀ ≠ ∞ := (hfin C₀ hC₀ (hC₀WE.trans (inter_subset_left.trans hWU))).ne
  -- Lusin on `C₀` with error `δ = μ(C₀) - c > 0`: a compact `C ⊆ C₀` with `μ(C₀ ∖ C) < δ` on
  -- which `u` is continuous.
  obtain ⟨C, hC, hCC₀, hC₀C, hu_cont⟩ :=
    Submission.smr_ufd_cl_vector_lusin P N μ u hu C₀ hC₀.measurableSet hC₀fin (μ C₀ - c)
      (tsub_pos_iff_lt.2 hcC₀).ne'
  -- `μ(C₀) - μ(C) ≤ μ(C₀ ∖ C) < μ(C₀) - c`, hence `c < μ(C)`.
  exact ⟨C, hC, hCC₀.trans hC₀WE, lt_of_tsub_lt_tsub_left (le_measure_sdiff.trans_lt hC₀C),
    hu_cont⟩
/-- Tietze extension into the closed unit ball of `ℝ^N`: if `u` is continuous on a closed set
`C ⊆ ℝ^P` with `‖u‖ ≤ 1` on `C`, there is a continuous `w : ℝ^P → ℝ^N` with `‖w‖ ≤ 1` and
`w = u` on `C`.  Off `C`, `w` is a continuous selection (partition of unity) of the convex hulls
of the values of `u` on `C ∩ B(y, 3 d(y, C))`, as in Dugundji's extension theorem. -/
theorem Submission.smr_ufd_ball_tietze :
    ∀ (P N : ℕ) (C : Set (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), IsClosed C →
      ContinuousOn u C → (∀ x ∈ C, ‖u x‖ ≤ 1) →
      ∃ w : Eucl P → EuclideanSpace ℝ (Fin N), Continuous w ∧ (∀ x, ‖w x‖ ≤ 1) ∧
        ∀ x ∈ C, w x = u x := by
  intro P N C u hC hu hu1
  -- Empty `C`: take `w = 0`.
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, continuous_const, fun x => by simp, fun x hx => hx.elim⟩
  -- For `y ∉ C`, `t y` is the convex hull of `u (C ∩ B(y, 3 d(y, C)))`.
  set t : (Cᶜ : Set (Eucl P)) → Set (EuclideanSpace ℝ (Fin N)) := fun y =>
    convexHull ℝ (u '' (C ∩ ball (y : Eucl P) (3 * infDist (y : Eucl P) C)))
  have htc : ∀ y, Convex ℝ (t y) := fun y => convex_convexHull ℝ _
  have hpos : ∀ y : (Cᶜ : Set (Eucl P)), 0 < infDist (y : Eucl P) C := fun y =>
    (hC.notMem_iff_infDist_pos hne).1 y.2
  -- Locally constant selections: `u c` for a point `c ∈ C` with `|y - c| < 2 d(y, C)`.
  have hloc : ∀ y : (Cᶜ : Set (Eucl P)), ∃ v, ∀ᶠ z in 𝓝 y, v ∈ t z := by
    intro y
    obtain ⟨c, hcC, hc⟩ := (infDist_lt_iff hne).1
      (by linarith [hpos y] : infDist (y : Eucl P) C < 2 * infDist (y : Eucl P) C)
    refine ⟨u c, ?_⟩
    have h1 : ContinuousAt (fun z : (Cᶜ : Set (Eucl P)) => dist (z : Eucl P) c) y :=
      (continuous_subtype_val.dist continuous_const).continuousAt
    have h2 : ContinuousAt (fun z : (Cᶜ : Set (Eucl P)) => 3 * infDist (z : Eucl P) C) y :=
      (continuous_const.mul ((continuous_infDist_pt C).comp continuous_subtype_val)).continuousAt
    filter_upwards [h1.eventually_lt h2 (by linarith [hpos y])] with z hz
    exact subset_convexHull ℝ _ ⟨c, ⟨hcC, by rw [mem_ball, dist_comm]; exact hz⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const htc hloc
  -- Every `t y` lies in the closed unit ball.
  have htB : ∀ y, t y ⊆ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := fun y =>
    convexHull_min (by rintro _ ⟨c, hc, rfl⟩; simpa using hu1 c hc.1) (convex_closedBall 0 1)
  classical
  refine ⟨fun x => if hx : x ∈ C then u x else g ⟨x, hx⟩, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ C
    · -- At `x ∈ C`: nearby values of `u` on `C` are close to `u x`, and so are their hulls.
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδu⟩ := Metric.continuousOn_iff.1 hu x hx (ε / 2) (half_pos hε)
      filter_upwards [ball_mem_nhds x (by positivity : 0 < δ / 4)] with y hy
      have hyx : dist y x < δ / 4 := mem_ball.1 hy
      rw [dite_eq_left hx]
      by_cases hyC : y ∈ C
      · rw [dite_eq_left hyC]
        exact (hδu y hyC (by linarith)).trans (half_lt_self hε)
      · rw [dite_eq_right hyC]
        have hsub : t ⟨y, hyC⟩ ⊆ closedBall (u x) (ε / 2) := by
          refine convexHull_min ?_ (convex_closedBall _ _)
          rintro _ ⟨c, ⟨hcC, hcy⟩, rfl⟩
          have hcy' : dist c y < 3 * infDist y C := mem_ball.1 hcy
          have hinf : infDist y C ≤ dist y x := infDist_le_dist_of_mem hx
          have hcx : dist c x < δ := by
            calc dist c x ≤ dist c y + dist y x := dist_triangle _ _ _
              _ < δ := by linarith
          exact mem_closedBall.2 (hδu c hcC hcx).le
        exact lt_of_le_of_lt (mem_closedBall.1 (hsub (hg ⟨y, hyC⟩))) (half_lt_self hε)
    · -- Off `C` the glued map is `g` on the open set `Cᶜ`.
      have hcont : ContinuousOn (fun x => if hx : x ∈ C then u x else g ⟨x, hx⟩) Cᶜ := by
        rw [continuousOn_iff_continuous_domRestrict]
        convert g.continuous using 1
        funext y
        have hy : (y : Eucl P) ∉ C := y.2
        simp [hy]
      exact hcont.continuousAt (hC.isOpen_compl.mem_nhds hx)
  · intro x
    dsimp only
    by_cases hx : x ∈ C
    · rw [dite_eq_left hx]
      exact hu1 x hx
    · rw [dite_eq_right hx]
      simpa using htB _ (hg ⟨x, hx⟩)
  · intro x hx
    exact dite_eq_left hx
/-- **Small cutoff (step of Simon Ch. 6, 2.7–2.9, pp. 136–137).**  If `μ` is finite on compact
subsets of `U`, `C` is compact and `W ⊆ U` is open with `C ⊆ W`, then for every `ε > 0` there is
a continuous compactly supported `ψ : ℝ^P → [0, 1]` with `tsupport ψ ⊆ W`, `ψ = 1` on `C` and
`μ(support ψ ∖ C) < ε`.  Choose `r > 0` with the compact `cthickening r C ⊆ W`; the open
thickenings `O j = thickening (r / (j + 1)) C` decrease to `C`, so by continuity from above
`μ(O j ∖ C) < ε` for some `j`, and Urysohn's lemma for `C` and `(O j)ᶜ` gives `ψ`. -/
theorem Submission.smr_ufd_small_cutoff : ∀ (P : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → ∀ C W : Set (Eucl P), IsCompact C → IsOpen W → C ⊆ W → W ⊆ U → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ ψ : Eucl P → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x ∈ C, ψ x = 1) ∧ μ (Function.support ψ \ C) < ε := by
  intro P U μ hfin C W hC hW hCW hWU ε hε
  -- Step 1: a compact closed thickening `cthickening r C ⊆ W ⊆ U`, of finite measure.
  obtain ⟨r, hr, hrW⟩ := hC.exists_cthickening_subset_open hW hCW
  have hKfin : μ (cthickening r C) < ∞ := hfin _ hC.cthickening (hrW.trans hWU)
  -- Step 2: the open thickenings `O j = thickening (r / (j + 1)) C` contain `C`, decrease, lie in
  -- `cthickening r C`, and `⋂ j, O j ⊆ C`.
  set δ : ℕ → ℝ := fun j => r / ((j : ℝ) + 1) with hδ_def
  set O : ℕ → Set (Eucl P) := fun j => thickening (δ j) C with hO_def
  have hδ_pos : ∀ j, 0 < δ j := fun j => div_pos hr (by positivity)
  have hδ_le : ∀ j, δ j ≤ r := fun j =>
    div_le_self hr.le (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hCO : ∀ j, C ⊆ O j := fun j => self_subset_thickening (hδ_pos j) C
  have hOK : ∀ j, closure (O j) ⊆ cthickening r C := fun j =>
    (closure_thickening_subset_cthickening _ _).trans (cthickening_mono (hδ_le j) C)
  have hO_anti : Antitone O := fun i j hij =>
    thickening_mono (div_le_div_of_nonneg_left hr.le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hij)) C
  have hO_inter : (⋂ j, O j) ⊆ C := by
    intro x hx
    rw [← hC.isClosed.closure_eq, closure_eq_iInter_thickening, mem_iInter₂]
    intro t ht
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (div_pos ht hr)
    have hjt : δ j ≤ t := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [one_div, inv_lt_iff_one_lt_mul₀ h1, div_mul_eq_mul_div, one_lt_div hr] at hj
      rw [hδ_def, div_le_iff₀ h1]
      exact hj.le
    exact thickening_mono hjt C (mem_iInter.1 hx j)
  -- Step 3: continuity from above on the halos `O j ∖ C` (open minus closed, decreasing, the
  -- first of finite measure, empty intersection) gives `j` with `μ (O j ∖ C) < ε`.
  have hD_meas : ∀ j, NullMeasurableSet (O j \ C) μ := fun j =>
    (isOpen_thickening.measurableSet.diff hC.isClosed.measurableSet).nullMeasurableSet
  have hD_anti : Antitone fun j => O j \ C := fun i j hij => sdiff_subset_sdiff_left (hO_anti hij)
  have hD_fin : ∃ j, μ (O j \ C) ≠ ∞ :=
    ⟨0, ((measure_mono (sdiff_subset.trans (subset_closure.trans (hOK 0)))).trans_lt hKfin).ne⟩
  have hD_empty : (⋂ j, O j \ C) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    rw [mem_iInter] at hx
    exact (hx 0).2 (hO_inter (mem_iInter.2 fun j => (hx j).1))
  have hT := tendsto_measure_iInter_atTop hD_meas hD_anti hD_fin
  rw [hD_empty, measure_empty] at hT
  obtain ⟨j, hj⟩ := (hT.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  -- Step 4: Urysohn's lemma for the compact `C` and the closed `(O j)ᶜ`, disjoint as `C ⊆ O j`.
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hC
    isOpen_thickening.isClosed_compl (disjoint_compl_right_iff_subset.2 (hCO j))
  -- Step 5: `support f ⊆ O j`, so `tsupport f ⊆ closure (O j) ⊆ cthickening r C ⊆ W` and
  -- `μ (support f ∖ C) ≤ μ (O j ∖ C) < ε`.
  have hsupp : Function.support f ⊆ O j := fun x hx => by
    by_contra h
    exact hx (hf0 h)
  refine ⟨f, f.continuous, hfc, (closure_mono hsupp).trans ((hOK j).trans hrW),
    fun x => hf01 x, fun x hx => hf1 hx, ?_⟩
  exact (measure_mono (sdiff_subset_sdiff_left hsupp)).trans_lt hj
/-- Simon Ch. 6, 2.7–2.9 (the final step of the unit-form density argument): if `|g| ≤ 1`, `g = 1`
on `C ⊆ A`, `g = 0` off `S` with `μ(S) < ∞` and `c + μ(S ∖ C) < μ(C)`, then `c < ∫_A g dμ`.  As
`g = 1` on `C` and `g = 0` off `S`, `C ⊆ S`, so all measures involved are finite, and `|g| ≤ 1_S`
makes `g` integrable.  Then `∫_A g = μ(C) + ∫_{A ∖ C} g` and
`|∫_{A ∖ C} g| = |∫_{(A ∖ C) ∩ S} g| ≤ μ(S ∖ C)`, so `∫_A g ≥ μ(C) − μ(S ∖ C) > c`. -/
theorem Submission.smr_ufd_integral_lower_bound :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (g : Eucl P → ℝ) (A C S : Set (Eucl P)) (c : ℝ≥0∞), MeasurableSet A → MeasurableSet C → MeasurableSet S → C ⊆ A → μ S < ∞ → Measurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ C, g x = 1) → (∀ x, x ∉ S → g x = 0) → c + μ (S \ C) < μ C → c < ENNReal.ofReal (∫ x in A, g x ∂μ) := by
  intro P μ g A C S c hA hC hS hCA hSfin hg hg1 hgC hgS hc
  -- Step 1 (finiteness): `C ⊆ S`, so `μ C ≤ μ S < ∞`, and `c`, `μ (S \ C)` are finite.
  have hCS : C ⊆ S := fun x hx => by
    by_contra hxS
    have h := hgC x hx
    rw [hgS x hxS] at h
    exact zero_ne_one h
  have hCfin : μ C ≠ ∞ := ((measure_mono hCS).trans_lt hSfin).ne
  have hsum : c + μ (S \ C) ≠ ∞ := ne_top_of_lt hc
  have hcfin : c ≠ ∞ := (ENNReal.add_ne_top.1 hsum).1
  have hSCfin : μ (S \ C) ≠ ∞ := (ENNReal.add_ne_top.1 hsum).2
  have hreal : c.toReal + μ.real (S \ C) < μ.real C := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add hcfin hSCfin]
    exact (ENNReal.toReal_lt_toReal hsum hCfin).2 hc
  -- Step 2 (integrability): `|g| ≤ 1_S` and `μ S < ∞`.
  have hgint : Integrable g μ := by
    refine ((integrable_indicator_iff hS).2 (integrableOn_const (C := (1 : ℝ)) hSfin.ne)).mono'
      hg.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · simpa [hx, Real.norm_eq_abs] using hg1 x
    · simp [hx, hgS x hx]
  -- Step 3 (splitting): `∫_A g = ∫_C g + ∫_{A \ C} g = μ(C) + ∫_{A \ C} g`.
  have hsplit : ∫ x in A, g x ∂μ = μ.real C + ∫ x in A \ C, g x ∂μ := by
    have hCint : ∫ x in C, g x ∂μ = ∫ _ in C, (1 : ℝ) ∂μ := setIntegral_congr_fun hC hgC
    rw [← integral_inter_add_sdiff (s := A) hC hgint.integrableOn, inter_eq_right.2 hCA, hCint,
      setIntegral_const, smul_eq_mul, mul_one]
  -- Step 4 (remainder): `|∫_{A \ C} g| ≤ μ((A \ C) ∩ S) ≤ μ(S \ C)`.
  have hsub : (A \ C) ∩ S ⊆ S \ C := fun x hx => ⟨hx.2, hx.1.2⟩
  have hrem : |∫ x in A \ C, g x ∂μ| ≤ μ.real (S \ C) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := (A \ C) ∩ S) (hA.diff hC)
      inter_subset_left fun x hx => hgS x fun hxS => hx.2 ⟨hx.1, hxS⟩]
    have h1 : ‖∫ x in (A \ C) ∩ S, g x ∂μ‖ ≤ 1 * μ.real ((A \ C) ∩ S) :=
      norm_setIntegral_le_of_norm_le_const
        ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.2 hSCfin))
        fun x _ => (Real.norm_eq_abs (g x)).trans_le (hg1 x)
    rw [one_mul, Real.norm_eq_abs] at h1
    exact h1.trans (measureReal_mono hsub hSCfin)
  -- Step 5 (conclusion): `∫_A g ≥ μ(C) − μ(S \ C) > c`.
  rw [ENNReal.lt_ofReal_iff_toReal_lt hcfin, hsplit]
  have := neg_abs_le (∫ x in A \ C, g x ∂μ)
  linarith
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
/-- A `k`-covector on `ℝ^P` whose coordinates `α(e_{I(0)}, …, e_{I(k-1)})` vanish for every
increasing multi-index `I` is zero. -/
theorem Submission.smr_ci_covector_eq_zero_of_coord :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k),
      (∀ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I = 0) → α = 0 := by
  intro P k α hα
  classical
  -- By extensionality on the standard basis it suffices to treat injective index tuples `v`.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.toAlternatingMap_zero,
    AlternatingMap.zero_apply]
  -- Sorting `v` gives an increasing multi-index `I` with `e_I = e_v ∘ σ`, `σ := Tuple.sort v`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  have h := hα (OrderEmbedding.ofStrictMono _ hsm)
  have heq : (fun j => EuclideanSpace.single (OrderEmbedding.ofStrictMono _ hsm j) (1 : ℝ)) =
      (fun i => EuclideanSpace.single (v i) (1 : ℝ)) ∘ Tuple.sort v := rfl
  -- `α(e_I) = sign σ • α(e_v)`, and the sign is a unit.
  rw [euclideanCovectorCoordinate, heq, ← ContinuousAlternatingMap.coe_toAlternatingMap α,
    AlternatingMap.map_perm] at h
  exact (smul_eq_zero_iff_eq _).mp h
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

/-- Simon (6.1.2)–(6.1.5): listing the coefficients `α(e_{I(0)}, …, e_{I(k-1)})` over the
increasing multi-indices `I` is a linear isomorphism `J` of the `k`-covectors on `ℝ^P` onto `ℝ^N`
with `|α| = ‖J α‖` for the Euclidean coefficient norm `|α| = covectorEuclideanNorm α`. -/
theorem Submission.smr_covector_coord_isometry :
    ∀ (P k : ℕ), ∃ (N : ℕ) (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖ := by
  intro P k
  -- Enumerate the increasing multi-indices `I : Fin k ↪o Fin P` by `Fin N`.
  let σ : Fin (Fintype.card (SimonMultiIndex k P)) ≃ SimonMultiIndex k P :=
    (Fintype.equivFin (SimonMultiIndex k P)).symm
  -- The coordinate map `J α = (α(e_{σ n}))_n`, linear because evaluation is.
  obtain ⟨J, hJ⟩ : ∃ J : Covector (Eucl P) k →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (SimonMultiIndex k P))),
      ∀ α n, J α n = euclideanCovectorCoordinate α (σ n) :=
    ⟨{ toFun := fun α => WithLp.toLp 2 fun n => euclideanCovectorCoordinate α (σ n)
       map_add' := fun α β => by
         ext n
         simp [euclideanCovectorCoordinate]
       map_smul' := fun c α => by
         ext n
         simp [euclideanCovectorCoordinate] }, fun _ _ => rfl⟩
  have hbij : Function.Bijective J := by
    refine ⟨(injective_iff_map_eq_zero J).2 fun α hα => ?_, fun y => ?_⟩
    · -- injective: a covector whose coordinates all vanish is zero
      refine Submission.smr_ci_covector_eq_zero_of_coord P k α fun I => ?_
      rw [← σ.apply_symm_apply I, ← hJ, hα, PiLp.zero_apply]
    · -- surjective: `∑_I y_{σ⁻¹ I} dx^I` has coordinates `y`
      refine ⟨∑ I : SimonMultiIndex k P,
        y (σ.symm I) • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)), ?_⟩
      ext n
      rw [hJ, Submission.smr_ci_coord_sum_smul_wedge, σ.symm_apply_apply]
  refine ⟨_, LinearEquiv.ofBijective J hbij, fun α => ?_⟩
  -- Both norms are square roots of the same sum of squares, reindexed along `σ`.
  rw [Submission.smr_ci_norm_eq_sqrt_sum_coord_sq, LinearEquiv.ofBijective_apply,
    EuclideanSpace.norm_eq, ← σ.sum_comp]
  simp only [hJ, Real.norm_eq_abs, sq_abs]
/-- **Mollification step of Simon Ch. 6, 2.7–2.9 (pp. 136–137).**  A continuous compactly
supported `k`-form `φ` with `tsupport φ ⊆ V`, `V` open, is a uniform limit, in the Euclidean
coefficient norm, of test forms supported in `V`.  As `|α| ≤ √M ‖α‖` (`M = #(Fin k → Fin P)`,
`‖α‖` the operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ φ)`:
`ψ ⋆ φ` is the convolution of `φ` with a normalized smooth bump `ψ` supported in a ball whose
radius is a uniform-continuity modulus of `φ`, and `χ` is a smooth cutoff with values in `[0, 1]`,
equal to `1` exactly on `tsupport φ`, whose support `V'` has compact closure in `V`. -/
theorem Submission.smr_exists_testForm_uniform_approx : ∀ (P k : ℕ) (U V : Set (Eucl P)) (φ : Eucl P → Covector (Eucl P) k), IsOpen V → V ⊆ U → Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧ ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ ε := by
  intro P k U V φ hV hVU hφ hφc hφV ε hε
  -- Step 1: `|α| ≤ C ‖α‖` with `C = √M`, since every coefficient satisfies
  -- `|α(e_I)| ≤ ‖α‖ ∏ ‖e_{I j}‖ = ‖α‖`.
  set C : ℝ := Real.sqrt (Fintype.card (Fin k → Fin P)) with hC_def
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hcmp : ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hC_def, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin k → Fin P,
          (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
        ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg α)] using h)
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  have hC1 : 0 < C + 1 := by linarith
  set ε' : ℝ := ε / (C + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε hC1
  -- Step 2: an open `V'` with `tsupport φ ⊆ V'` and `closure V' ⊆ V` compact.
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ :=
    exists_open_between_and_isCompact_closure hφc.isCompact hV hφV
  -- Step 3: a smooth cutoff `χ : ℝ^P → [0, 1]` with `support χ = V'` and `χ = 1` exactly on
  -- `tsupport φ`.
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV'o (isClosed_tsupport φ) hKV'
  -- Step 4: mollification.  `φ` is uniformly continuous with modulus `δ` at accuracy `ε'`; `ψ` is
  -- a smooth bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `g = ψ ⋆ φ` is smooth and
  -- `dist (g x) (φ x) ≤ ε'`.
  obtain ⟨δ, hδ, hφδ⟩ :=
    Metric.uniformContinuous_iff.mp (hφc.uniformContinuous_of_continuous hφ) ε' hε'
  obtain ⟨b, hbs, hbc, hbd, hbr, hb0⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
  have hbnn : ∀ y, 0 ≤ b y := fun y => (hbr (mem_range_self y)).1
  have hbint : 0 < ∫ y, b y :=
    hbd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc (fun y => hbnn y)
      (hb0.symm ▸ one_ne_zero : b 0 ≠ 0)
  set ψ : Eucl P → ℝ := fun y => (∫ z, b z)⁻¹ * b y with hψ_def
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hbd
  have hψc : HasCompactSupport ψ := hbc.mul_left
  have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hbint.le) (hbnn y)
  have hψs : Function.support ψ ⊆ ball 0 δ :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport b).trans hbs)
  have hψ1 : ∫ y, ψ y = 1 := by
    rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hbint.ne']
  obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → Covector (Eucl P) k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (φ x) ≤ ε' :=
    ⟨convolution ψ φ (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      hψc.contDiff_convolution_left _ hψd hφ.locallyIntegrable,
      fun x => dist_convolution_le hε'.le hψs hψnn hψ1 hφ.aestronglyMeasurable
        fun y hy => (hφδ (mem_ball.mp hy)).le⟩
  -- Step 5: `η = χ • g` is a test form with `tsupport η ⊆ closure V' ⊆ V ⊆ U`.
  have hη_supp : tsupport (fun x => χ x • g x) ⊆ closure V' := by
    refine (tsupport_smul_subset_left χ g).trans ?_
    rw [tsupport, hχs]
  have hη_cpt : HasCompactSupport (fun x => χ x • g x) :=
    hV'c.of_isClosed_subset (isClosed_tsupport _) hη_supp
  refine ⟨⟨fun x => χ x • g x, ⟨⟨hχ.smul hg, hη_cpt⟩, hη_supp.trans (hV'V.trans hVU)⟩⟩,
    hη_supp.trans hV'V, fun x => ?_⟩
  -- Step 6: `‖φ x - η x‖ ≤ ε'` (on `tsupport φ`, `η = g`; off it, `φ = 0` and `0 ≤ χ ≤ 1`),
  -- hence `|φ x - η x| ≤ C ε' ≤ ε`.
  have hle : ‖φ x - χ x • g x‖ ≤ ε' := by
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε' := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  calc covectorEuclideanNorm (φ x - χ x • g x) ≤ C * ‖φ x - χ x • g x‖ := hcmp _
    _ ≤ C * ε' := mul_le_mul_of_nonneg_left hle hC
    _ ≤ ε := by
      rw [hε'_def, mul_div_assoc', div_le_iff₀ hC1]
      nlinarith

/-- **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6(v) of `slicing_mass_representation`.  If
`S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, where `|⟨α, v(x)⟩| ≤ |α|` and `μ` is finite on
compact subsets of `U`, then `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)` for every continuous compactly supported
`k`-form `φ` with `spt φ ⊆ W ⊆ U`, `W` open, and `|φ| ≤ 1`.

Take an open `V ⊇ spt φ` whose closure is a compact subset of `W`.  The smooth approximants
`η_j ∈ 𝒟ᵏ(U)` of `smr_exists_testForm_uniform_approx` (`spt η_j ⊆ V`, `|φ - η_j| ≤ δ_j → 0`),
rescaled to `ζ_j = (1 + δ_j)⁻¹ η_j`, are admissible for `M_W(S)` and satisfy
`|ζ_j - φ| ≤ 2 δ_j`; the triangle inequality and homogeneity of `|·|` come from
`smr_covector_coord_isometry`.  Dominated convergence on `μ ⌞ A` with the bound `1_{closure V}`
gives `S(ζ_j) → ∫_A ⟨φ, v⟩ dμ`, and `ofReal (S(ζ_j)) ≤ M_W(S)` passes to the limit. -/
theorem Submission.smr_ofReal_integral_le_massOn : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U k), (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ W → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) ≤ S.massOn W := by
  intro P k U μ v hint hfin hv A S hS W hW hWU φ hφc hφs hφW hφ1
  -- `|α| = ‖J α‖` for a linear `J`, so `|·|` is subadditive and absolutely homogeneous.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have hadd : ∀ α β : Covector (Eucl P) k,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hJ, hJ, hJ, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hJ, hJ, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 1: an open `V ⊇ tsupport φ` whose closure is a compact subset of `W ⊆ U`.
  obtain ⟨V, hVo, hφV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hφs hW hφW
  have hKU : closure V ⊆ U := hVW.trans hWU
  have hμK : μ (closure V) < ∞ := hfin _ hVc hKU
  have hVU : V ⊆ U := subset_closure.trans hKU
  -- Step 2: test forms `η j` supported in `V` with `|φ - η j| ≤ δ j → 0`, and
  -- `ζ j = (1 + δ j)⁻¹ • η j`.
  obtain ⟨δ, hδpos, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun j => 1 / ((j : ℝ) + 1), fun j => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  have hη : ∀ j : ℕ, ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧
      ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ δ j := fun j =>
    Submission.smr_exists_testForm_uniform_approx P k U V φ hVo hVU hφc hφs hφV (δ j) (hδpos j)
  choose η hηV hηφ using hη
  obtain ⟨ζ, hζx⟩ : ∃ ζ : ℕ → TestFormOn U k, ∀ j x,
      (ζ j : DifferentialForm (Eucl P) k) x = (1 + δ j)⁻¹ • (η j : DifferentialForm (Eucl P) k) x :=
    ⟨fun j => (1 + δ j)⁻¹ • η j, fun j x => rfl⟩
  have hpos : ∀ j, 0 < 1 + δ j := fun j => by linarith [hδpos j]
  have hηle : ∀ j x, covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x) ≤ 1 + δ j := by
    intro j x
    calc covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
        = covectorEuclideanNorm (φ x + -(φ x - (η j : DifferentialForm (Eucl P) k) x)) := by
          congr 1
          abel
      _ ≤ covectorEuclideanNorm (φ x) +
            covectorEuclideanNorm (-(φ x - (η j : DifferentialForm (Eucl P) k) x)) := hadd _ _
      _ ≤ 1 + δ j := by
          rw [covectorEuclideanNorm_neg]
          exact add_le_add (hφ1 x) (hηφ j x)
  -- Step 3: every `ζ j` is admissible for `M_W(S)`, so `ofReal (S (ζ j)) ≤ M_W(S)`.
  have hadm : ∀ j, ζ j ∈ massAdmissibleOn U k W := by
    intro j
    refine ⟨?_, fun x => ?_⟩
    · have hfun : (ζ j : DifferentialForm (Eucl P) k) =
          fun x => (1 + δ j)⁻¹ • (η j : DifferentialForm (Eucl P) k) x := funext (hζx j)
      rw [hfun]
      exact (tsupport_smul_subset_right (fun _ => (1 + δ j)⁻¹) _).trans
        ((hηV j).trans (subset_closure.trans hVW))
    · rw [hζx, hsmul, abs_of_pos (inv_pos.mpr (hpos j))]
      calc (1 + δ j)⁻¹ * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
          ≤ (1 + δ j)⁻¹ * (1 + δ j) :=
            mul_le_mul_of_nonneg_left (hηle j x) (inv_nonneg.mpr (hpos j).le)
        _ = 1 := inv_mul_cancel₀ (hpos j).ne'
  -- Step 4: `|ζ j - φ| ≤ 2 δ j` everywhere, and `ζ j` vanishes off `V`.
  have hclose : ∀ j x,
      covectorEuclideanNorm ((ζ j : DifferentialForm (Eucl P) k) x - φ x) ≤ 2 * δ j := by
    intro j x
    have e : (ζ j : DifferentialForm (Eucl P) k) x - φ x =
        ((1 + δ j)⁻¹ - 1) • (η j : DifferentialForm (Eucl P) k) x +
          -(φ x - (η j : DifferentialForm (Eucl P) k) x) := by
      rw [hζx]
      module
    have habs : |(1 + δ j)⁻¹ - 1| = δ j / (1 + δ j) := by
      have h : (1 + δ j)⁻¹ - 1 = -(δ j / (1 + δ j)) := by
        linear_combination mul_inv_cancel₀ (hpos j).ne'
      rw [h, abs_neg, abs_of_pos (div_pos (hδpos j) (hpos j))]
    have h2 : δ j / (1 + δ j) * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
        ≤ δ j :=
      calc δ j / (1 + δ j) * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
          ≤ δ j / (1 + δ j) * (1 + δ j) :=
            mul_le_mul_of_nonneg_left (hηle j x) (div_pos (hδpos j) (hpos j)).le
        _ = δ j := div_mul_cancel₀ _ (hpos j).ne'
    rw [e]
    refine (hadd _ _).trans ?_
    rw [covectorEuclideanNorm_neg, hsmul, habs]
    linarith [hηφ j x]
  have hζ0 : ∀ j x, x ∉ V → (ζ j : DifferentialForm (Eucl P) k) x = 0 := fun j x hx => by
    rw [hζx, image_eq_zero_of_notMem_tsupport fun h => hx (hηV j h), smul_zero]
  -- Steps 5–6: dominated convergence on `μ ⌞ A`, with the integrable bound `1_{closure V}`
  -- (`μ (closure V) < ∞`), gives `S (ζ j) → ∫_A ⟨φ, v⟩ dμ`.
  have hlim : Tendsto (fun j => S (ζ j)) atTop (𝓝 (∫ x in A, v x (φ x) ∂μ)) := by
    simp only [hS]
    refine tendsto_integral_of_dominated_convergence
      (F := fun j x => v x ((ζ j : DifferentialForm (Eucl P) k) x)) (f := fun x => v x (φ x))
      ((closure V).indicator fun _ => (1 : ℝ))
      (fun j => (hint (ζ j)).aestronglyMeasurable.restrict)
      ((integrable_indicator_iff isClosed_closure.measurableSet).mpr
        (integrableOn_const ((Measure.restrict_apply_le A (closure V)).trans_lt hμK).ne))
      (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ V
      · rw [indicator_of_mem (subset_closure hx), Real.norm_eq_abs]
        exact (hv x _).trans ((hadm j).2 x)
      · rw [hζ0 j x hx, map_zero, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) x
    · have h2δ : Tendsto (fun j => 2 * δ j) atTop (𝓝 0) := by
        simpa using hδlim.const_mul 2
      have h0 : Tendsto (fun j => v x ((ζ j : DifferentialForm (Eucl P) k) x) - v x (φ x))
          atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun j => ?_) h2δ
        rw [← map_sub, Real.norm_eq_abs]
        exact (hv x _).trans (hclose j x)
      simpa using h0.add_const (v x (φ x))
  -- Step 7: pass to the limit in `ofReal (S (ζ j)) ≤ M_W(S)`.
  exact le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun j => S.le_massOn (hadm j)

/-- Simon Ch. 6, 2.8–2.9 (pp. 136–137), the step `μ(W ∩ A) ≤ M_W(T ⌞ A)` of the mass formula
for a restriction: continuous unit forms supported in an open `W ⊆ U` detect `μ(W ∩ A)`.  Write
`v(x)(α) = ⟨Jα, u(x)⟩` for an isometry `J` of `(Λᵏ, |·|)` onto `ℝ^N`, so `‖u‖ ≤ 1` and `‖u‖ = 1`
`μ`-a.e.  Take a compact Lusin set `C ⊆ W ∩ A ∩ {‖u‖ = 1}` of `u` with `c < μ(C)`, a continuous
extension `w` of `u|C` with `‖w‖ ≤ 1` (Tietze) and a cutoff `ψ ∈ [0, 1]`, `ψ = 1` on `C`, with
`tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c` (Urysohn).  Then `φ = J⁻¹(ψ w)` has `|φ| ≤ 1`,
and `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C` and `0` off `support ψ`, so `∫_A ⟨φ, v⟩ dμ > c`. -/
theorem Submission.smr_exists_unit_form_gt : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) → (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < μ (W ∩ A) → ∃ φ : Eucl P → Covector (Eucl P) k, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ W ∧ (∀ x, covectorEuclideanNorm (φ x) ≤ 1) ∧ c < ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) := by
  intro P k U μ v hμK hv hvm hunit A hA W hW hWU c hc
  -- Coordinates `u` of `v` in an isometric chart `J`: `v(x)(α) = ⟨Jα, u(x)⟩`, `‖u‖ = 1` a.e.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  obtain ⟨u, hum, hu1, hu_ae, hvu⟩ :=
    Submission.smr_ufd_unit_coord_field P k N μ v J hJ hv hvm hunit
  -- `{‖u‖ = 1}` is conull, so it does not change `μ(W ∩ A)`; take a compact Lusin set `C` of `u`
  -- inside `W ∩ A ∩ {‖u‖ = 1}` with `c < μ(C)`.
  have hWAG : μ (W ∩ (A ∩ {x | ‖u x‖ = 1})) = μ (W ∩ A) := by
    rw [← Set.inter_assoc]
    exact measure_inter_conull (mem_ae_iff.1 hu_ae)
  obtain ⟨C, hCc, hCsub, hcC, huC⟩ := Submission.smr_ufd_compact_lusin_set P N U μ u hμK hum
    (A ∩ {x | ‖u x‖ = 1}) (hA.inter (measurableSet_eq_fun hum.norm measurable_const)) W hW hWU c
    (by rw [hWAG]; exact hc)
  have hCW : C ⊆ W := hCsub.trans Set.inter_subset_left
  -- Tietze: a continuous `w` with `‖w‖ ≤ 1` and `w = u` on `C`.
  obtain ⟨w, hwc, hw1, hwu⟩ :=
    Submission.smr_ufd_ball_tietze P N C u hCc.isClosed huC fun x _ => hu1 x
  -- Urysohn: `ψ ∈ [0, 1]`, `ψ = 1` on `C`, `tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c`.
  obtain ⟨ψ, hψc, hψcs, hψW, hψ01, hψC, hψS⟩ := Submission.smr_ufd_small_cutoff P U μ hμK C W hCc
    hW hCW hWU (μ C - c) (tsub_pos_of_lt hcC).ne'
  have hψw : ∀ x, ‖ψ x • w x‖ ≤ 1 := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (hψ01 x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hψ01 x).2).trans (hw1 x)
  -- The form `φ = J⁻¹(ψ w)`; `J⁻¹` is continuous since `ℝ^N` is finite-dimensional.
  refine ⟨fun x => J.symm (ψ x • w x),
    (LinearMap.continuous_of_finiteDimensional J.symm.toLinearMap).comp (hψc.smul hwc),
    (hψcs.smul_right (f' := w)).comp_left (map_zero J.symm),
    (tsupport_comp_subset (map_zero J.symm) _).trans ((tsupport_smul_subset_left ψ w).trans hψW),
    fun x => ?_, ?_⟩
  · -- `|φ(x)| = ‖ψ(x) w(x)‖ ≤ 1`.
    change covectorEuclideanNorm (J.symm (ψ x • w x)) ≤ 1
    rw [hJ, LinearEquiv.apply_symm_apply]
    exact hψw x
  · -- `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C ⊆ {‖u‖ = 1}` and `0` off `support ψ`.
    have hg : ∀ x, v x (J.symm (ψ x • w x)) = inner ℝ (ψ x • w x) (u x) := fun x => by
      rw [hvu, LinearEquiv.apply_symm_apply]
    simp only [hg]
    refine Submission.smr_ufd_integral_lower_bound P μ (fun x => inner ℝ (ψ x • w x) (u x)) A C
      (Function.support ψ) c hA hCc.isClosed.measurableSet hψc.isOpen_support.measurableSet
      (fun x hx => (hCsub hx).2.1)
      ((measure_mono (subset_tsupport ψ)).trans_lt (hμK (tsupport ψ) hψcs (hψW.trans hWU)))
      ((continuous_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin N))).measurable.comp
        ((hψc.smul hwc).measurable.prodMk hum))
      (fun x => (abs_real_inner_le_norm _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hψw x)).trans (hu1 x)))
      (fun x hx => ?_) (fun x hx => ?_) (lt_tsub_iff_left.1 hψS)
    · have hx1 : ‖u x‖ = 1 := (hCsub hx).2.2
      simp only [hψC x hx, one_smul, hwu x hx, real_inner_self_eq_norm_sq, hx1, one_pow]
    · simp only [Function.notMem_support.1 hx, zero_smul, inner_zero_left]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
