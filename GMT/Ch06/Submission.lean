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

/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), in the quantitative form
used in the proof of Ch. 6, 8.2.  For `r > 0`, the blow-up `η_{x,r}(z) = r⁻¹(z - x)` pushes
`(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so the blow-up integral of `(M, θ)` against `f` is
`(rⁿ)⁻¹ ∫ f(η_{x,r} z) 1_M θ(z) dHⁿ(z)` (`M` is `Hⁿ`-null-measurable).  If `f = 0` off
`B_R(0)` and `|f| ≤ C`, then for `R r ≤ ρ` these integrals exist and those of `(M, θ)` and
`(M', θ')` differ by at most `C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'| dHⁿ → 0`; as
`θ x = θ' x`, the two tangent-space conditions are equivalent. -/
theorem Submission.iwl_weighted_tangent_locality :
    ∀ (P n : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P),
      NullMeasurableSet M (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M' (μHE[n] : Measure (Eucl P)) → θ x = θ' x →
      (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧
        IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) →
      (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
          ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) →
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q ↔
        HasWeightedApproximateTangentSpaceAt n M' θ' x Q := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P n M M' θ θ' x hM hM' hθx ⟨ρ, hρ, hθρ, hθ'ρ⟩ hlim Q
  -- Change of variables under `η_r = blowUpMap x r`: `∫_{η_r(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η_r dHⁿ`.
  have hcov : ∀ r : ℝ, 0 < r → ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, g y ∂(μHE[n] : Measure (Eucl P)) =
        (r ^ n)⁻¹ * ∫ z in S, g (blowUpMap x r z) ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr S g
    let e : Eucl P ≃ₜ Eucl P :=
      (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
    have he : (e : Eucl P → Eucl P) = blowUpMap x r := by
      funext z
      simp [e, blowUpMap, sub_eq_add_neg]
    have hemb : MeasurableEmbedding (blowUpMap x r) := he ▸ e.measurableEmbedding
    -- `η_r` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η_r⁻¹(B) = x + r • B`.
    have hmp : MeasurePreserving (blowUpMap x r)
        (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) μHE[n] := by
      refine ⟨hemb.measurable, ?_⟩
      ext B hB
      rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
      have hpre : blowUpMap x r ⁻¹' B = (fun z => x + z) '' ((fun z => r • z) '' B) := by
        ext z
        simp only [mem_preimage, mem_image, blowUpMap]
        constructor
        · intro hz
          exact ⟨r • r⁻¹ • (z - x), ⟨r⁻¹ • (z - x), hz, rfl⟩, by
            rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
        · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
          rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
      rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
        Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
        smul_eq_mul, ← mul_assoc]
      have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
          coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
          ENNReal.ofReal_one]
      rw [hc, one_mul]
    rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- The blow-up integrals of `(M, θ)` and `(M', θ')` against `f` differ by `o(1)` as `r ↓ 0`.
  have hkey : ∀ f : CompactlySupportedContinuousMap (Eucl P) ℝ, Tendsto (fun r : ℝ =>
      (∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P))) -
        ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[n] : Measure (Eucl P)))
      (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- `f = 0` off `B_R(0)` and `|f| ≤ C`.
    obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- `f ∘ η_r` vanishes off `B̄_{R r}(x)`.
    have hvan : ∀ r : ℝ, 0 < r → ∀ z : Eucl P, z ∉ closedBall x (R * r) →
        f (blowUpMap x r z) = 0 := by
      intro r hr z hz
      apply hfR
      rw [mem_closedBall, not_le, dist_eq_norm] at hz
      rw [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div,
        le_div_iff₀ hr]
      exact hz.le
    -- For `R r ≤ ρ`, `(f ∘ η_r) · 1_S ϑ` is integrable when `ϑ` is integrable on `S ∩ B̄_ρ(x)`.
    have hint : ∀ r : ℝ, 0 < r → R * r ≤ ρ → ∀ (S : Set (Eucl P)) (ϑ : Eucl P → ℝ),
        NullMeasurableSet S (μHE[n] : Measure (Eucl P)) →
        IntegrableOn ϑ (S ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
        Integrable (fun z => f (blowUpMap x r z) * S.indicator ϑ z)
          (μHE[n] : Measure (Eucl P)) := by
      intro r hr hRr S ϑ hS hϑ
      have hcont : Continuous fun z => f (blowUpMap x r z) :=
        f.continuous.comp ((continuous_const_smul _).comp (continuous_id.sub continuous_const))
      have h1 : IntegrableOn (fun z => f (blowUpMap x r z) * ϑ z) (S ∩ closedBall x ρ)
          (μHE[n] : Measure (Eucl P)) :=
        Integrable.bdd_mul hϑ hcont.aestronglyMeasurable (ae_of_all _ fun z => hC _)
      have h2 : IntegrableOn (fun z => f (blowUpMap x r z) * ϑ z) S
          (μHE[n] : Measure (Eucl P)) := by
        refine h1.of_ae_sdiff_eq_zero hS (ae_of_all _ fun z hz => ?_)
        have hz' : z ∉ closedBall x (R * r) := fun h =>
          hz.2 ⟨hz.1, closedBall_subset_closedBall hRr h⟩
        rw [hvan r hr z hz', zero_mul]
      refine (h2.integrable_indicator₀ hS).congr (ae_of_all _ fun z => ?_)
      exact Set.indicator_mul_right S (fun z => f (blowUpMap x r z)) ϑ
    -- `∫_{η_r(S)} f(y) ϑ(x + r y) dHⁿ(y) = (rⁿ)⁻¹ ∫ f(η_r z) 1_S ϑ(z) dHⁿ(z)`.
    have hI : ∀ r : ℝ, 0 < r → ∀ (S : Set (Eucl P)) (ϑ : Eucl P → ℝ),
        NullMeasurableSet S (μHE[n] : Measure (Eucl P)) →
        ∫ y in blowUpMap x r '' S, f y * ϑ (x + r • y) ∂(μHE[n] : Measure (Eucl P)) =
          (r ^ n)⁻¹ * ∫ z, f (blowUpMap x r z) * S.indicator ϑ z
            ∂(μHE[n] : Measure (Eucl P)) := by
      intro r hr S ϑ hS
      rw [hcov r hr S]
      simp only [hinv r hr.ne']
      rw [← integral_indicator₀ hS]
      congr 2
      funext z
      exact Set.indicator_mul_right S (fun z => f (blowUpMap x r z)) ϑ
    -- The estimate `|I_{M,θ}(r) - I_{M',θ'}(r)| ≤ C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'|`.
    have hbound : ∀ r : ℝ, 0 < r → R * r ≤ ρ →
        ‖(∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P))) -
          ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ n)⁻¹) *
          ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
            ∂(μHE[n] : Measure (Eucl P))) := by
      intro r hr hRr
      rw [hI r hr M θ hM, hI r hr M' θ' hM', ← mul_sub,
        ← integral_sub (hint r hr hRr M θ hM hθρ) (hint r hr hRr M' θ' hM' hθ'ρ), enorm_mul,
        Real.enorm_of_nonneg (by positivity), mul_left_comm]
      gcongr
      calc ‖∫ z, f (blowUpMap x r z) * M.indicator θ z - f (blowUpMap x r z) * M'.indicator θ' z
              ∂(μHE[n] : Measure (Eucl P))‖ₑ
          ≤ ∫⁻ z, ‖f (blowUpMap x r z) * M.indicator θ z -
              f (blowUpMap x r z) * M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ z, (closedBall x (R * r)).indicator
              (fun z => ENNReal.ofReal C * ‖M.indicator θ z - M'.indicator θ' z‖ₑ) z
              ∂(μHE[n] : Measure (Eucl P)) := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ closedBall x (R * r)
            · rw [Set.indicator_of_mem hz, ← mul_sub, enorm_mul, ← ofReal_norm]
              gcongr
              exact hC _
            · rw [hvan r hr z hz, zero_mul, zero_mul, sub_zero, enorm_zero]
              exact zero_le
        _ = ENNReal.ofReal C * ∫⁻ z in closedBall x (R * r),
              ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
            rw [lintegral_indicator measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [tendsto_zero_iff_enorm_tendsto_zero]
    have hupper : Tendsto (fun r : ℝ => ENNReal.ofReal C * (ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
          ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hlim R hR) (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    refine hbound r hr.1 ?_
    have := hr.2
    rw [lt_div_iff₀ hR] at this
    linarith
  constructor
  · rintro ⟨hQ, hf⟩
    refine ⟨hQ, fun f => ?_⟩
    rw [← hθx]
    simpa using (hf f).sub (hkey f)
  · rintro ⟨hQ, hf⟩
    refine ⟨hQ, fun f => ?_⟩
    rw [hθx]
    simpa using (hf f).add (hkey f)

/-- **Coordinate expansion of covectors, Simon Ch. 6, (1.1)–(1.2) (pp. 131–132).**  Every
`k`-covector `α` on `ℝ^P` is `∑_{β ∈ I(k,P)} α(e_{β(0)}, …, e_{β(k-1)}) dx^β`.  By (1.1),
`dx^β(e_γ) = δ_{βγ}` for increasing `β, γ` (the determinant of the identity matrix if `β = γ`,
of a matrix with a zero column otherwise), so both sides agree on increasing basis tuples;
sorting and the sign rule for alternating maps extend this to all injective basis tuples, and an
alternating map is determined by its values on those. -/
theorem Submission.slicing_ru_covector_expansion : ∀ (P k : ℕ) (α : Covector (Eucl P) k), α = ∑ β : SimonMultiIndex k P, euclideanCovectorCoordinate α β • wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) := by
  intro P k α
  classical
  set e : (Fin k → Fin P) → Fin k → Eucl P := fun v j => EuclideanSpace.single (v j) 1
  set R : Covector (Eucl P) k := ∑ β : SimonMultiIndex k P,
    euclideanCovectorCoordinate α β • wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) with hR
  -- Steps 1–2: Kronecker property `dx^β(e_γ) = δ_{βγ}` on increasing multi-indices.
  have hK : ∀ β γ : SimonMultiIndex k P,
      wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · subst hβγ
      convert Matrix.det_one (n := Fin k) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · -- Some `γ j₀` lies outside `range β`: otherwise the ranges coincide (equal cardinality),
      -- and increasing maps with equal ranges are equal.
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ i, γ j₀ ≠ β i := by
        by_contra! h
        apply hβγ
        symm
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range γ ⊆ Set.range β := by
          rintro _ ⟨j, rfl⟩
          obtain ⟨i, hi⟩ := h j
          exact ⟨i, hi.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range β)
        rw [Set.ncard_range_of_injective β.injective, Set.ncard_range_of_injective γ.injective]
      exact Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => by
        simp [e, PiLp.single_apply, (hj₀ i).symm]
  -- Step 3: agreement on increasing basis tuples.
  have h1 : ∀ γ : SimonMultiIndex k P, R (e γ) = α (e γ) := by
    intro γ
    rw [hR, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  -- Step 4: agreement on injective basis tuples, by sorting and the sign rule.
  have h2 : ∀ v : Fin k → Fin P, Function.Injective v → R (e v) = α (e v) := by
    intro v hv
    have hsm : StrictMono (v ∘ Tuple.sort v) :=
      (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
    have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
    have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
    rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
      ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
      AlternatingMap.map_perm] at hγ
    exact smul_left_cancel _ hγ
  -- Step 5: an alternating map is determined by its values on injective basis tuples.
  symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  exact h2 v hv

/-- **Simple `n`-vectors (step (P1) of Simon Ch. 6, Lemma 3.9).**  The operator norm of
`v₁ ∧ ⋯ ∧ vₙ = simpleNVector v` is the square root of the Gram determinant `det (⟪vᵢ, vⱼ⟫)`, and a
change of frame `τ ↦ Bτ` multiplies `simpleNVector τ` by `det B`.  The second identity is the
uniqueness of alternating forms on `ℝⁿ` (`AlternatingMap.eq_smul_basis_det`).  A dependent `v`
makes both sides of the first vanish.  An independent `v` is `Bτ` for an orthonormal basis `τ` of
`span v`, so `G(v) = B Bᵀ`; `|α τ| ≤ ‖α‖` and the covector `u ↦ det (⟪τᵢ, uⱼ⟫)` (norm `≤ 1` by
Hadamard's and Bessel's inequalities, value `1` at `τ`) give `‖simpleNVector v‖ = |det B|`. -/
theorem Submission.lpf_simple_nvector_algebra : (∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
  -- Change of frame: `α(Bτ) = det B · α(τ)` for every `n`-covector `α`, since
  -- `B ↦ α(Bτ)` is alternating in the rows of `B` (`AlternatingMap.eq_smul_basis_det`).
  have hframe : ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
      simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
    intro P n B τ
    ext α
    simp only [simpleNVector_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    set f : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ :=
      α.toAlternatingMap.compLinearMap (Fintype.linearCombination ℝ τ) with hf
    have h1 : f (fun i j => B i j) = α (fun i => ∑ j, B i j • τ j) := by
      simp [hf, Fintype.linearCombination_apply]
    have h2 : f (Pi.basisFun ℝ (Fin n)) = α τ := by
      simp [hf, Fintype.linearCombination_apply_single]
    rw [← h1, AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) f,
      AlternatingMap.smul_apply, h2, Pi.basisFun_det, smul_eq_mul, mul_comm]
    rfl
  refine ⟨fun P n v => ?_, hframe⟩
  by_cases hv : LinearIndependent ℝ v
  · -- Independent family: `v = Bτ` for an orthonormal basis `τ` of `W = span v`,
    -- `B i j = ⟪v i, τ j⟫`, so `G(v) = B Bᵀ` and `simpleNVector v = det B • simpleNVector τ`.
    set W := Submodule.span ℝ (Set.range v) with hW_def
    have hW : Module.finrank ℝ W = n := by rw [finrank_span_eq_card hv, Fintype.card_fin]
    set b : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
    set τ : Fin n → Eucl P := fun j => (b j : Eucl P) with hτ_def
    have hτ : Orthonormal ℝ τ := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hvW : ∀ i, v i ∈ W := fun i => Submodule.subset_span (Set.mem_range_self i)
    set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => inner ℝ (v i) (τ j) with hB_def
    have hvB : (fun i => ∑ j, B i j • τ j) = v := by
      funext i
      have h := congrArg Subtype.val (b.sum_repr' ⟨v i, hvW i⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
      simpa [hB_def, hτ_def, real_inner_comm] using h
    have hgram : (Matrix.of fun i j => inner ℝ (v i) (v j)) = B * B.transpose := by
      ext i k
      have h := b.sum_inner_mul_inner ⟨v i, hvW i⟩ ⟨v k, hvW k⟩
      simp only [Submodule.coe_inner] at h
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hB_def]
      rw [← h]
      simp [hτ_def, real_inner_comm]
    have hsv : ∀ α : Covector (Eucl P) n, simpleNVector v α = B.det * α τ := by
      intro α
      rw [← hvB, hframe]
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, simpleNVector_apply]
    -- Upper bound: `|α τ| ≤ ‖α‖ ∏ ‖τ i‖ = ‖α‖`.
    have hup : ∀ α : Covector (Eucl P) n, |α τ| ≤ ‖α‖ := by
      intro α
      have h := α.le_opNorm τ
      simp only [hτ.1, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    -- Lower bound: the calibrating covector `α₀(u) = det (⟪τ i, u j⟫)` has `α₀ τ = 1` and
    -- `‖α₀‖ ≤ 1` by Hadamard's inequality for the columns `c j = (⟪τ i, u j⟫)ᵢ` together with
    -- Bessel's inequality `‖c j‖ ≤ ‖u j‖`.
    set α₀ : Covector (Eucl P) n := wedgeCovectors n fun i => innerSL ℝ (τ i) with hα₀_def
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀_def, wedgeCovectors_apply_det]
      have h : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) = 1 := by
        ext i j
        simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
      rw [h, Matrix.det_one]
    have hα₀ : ‖α₀‖ ≤ 1 := by
      refine ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one fun u => ?_
      rw [one_mul, hα₀_def, wedgeCovectors_apply_det, Real.norm_eq_abs]
      set c : Fin n → EuclideanSpace ℝ (Fin n) :=
        fun j => WithLp.toLp 2 fun i => inner ℝ (τ i) (u j) with hc
      set e := EuclideanSpace.basisFun (Fin n) ℝ
      have hdet : (Matrix.of fun i j => innerSL ℝ (τ i) (u j)).det = e.toBasis.det c := by
        rw [Module.Basis.det_apply]
        congr 1
      have hHad : |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := by
        have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
          ⟨finrank_euclideanSpace_fin⟩
        rw [← e.toBasis.orientation.volumeForm_robust' e c]
        exact e.toBasis.orientation.abs_volumeForm_apply_le c
      have hBessel : ∀ j, ‖c j‖ ≤ ‖u j‖ := by
        intro j
        rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (u j))]
        apply Real.sqrt_le_sqrt
        simpa [hc] using hτ.sum_inner_products_le (u j) (s := Finset.univ)
      rw [hdet]
      calc |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := hHad
        _ ≤ ∏ j, ‖u j‖ := by gcongr with j; exact hBessel j
    -- Hence `‖simpleNVector v‖ = |det B|`.
    have hnorm : ‖simpleNVector v‖ = |B.det| := by
      apply le_antisymm
      · refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun α => ?_
        rw [hsv, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hup α) (abs_nonneg _)
      · calc |B.det| = ‖simpleNVector v α₀‖ := by rw [hsv, hα₀τ, mul_one, Real.norm_eq_abs]
          _ ≤ ‖simpleNVector v‖ * ‖α₀‖ := (simpleNVector v).le_opNorm α₀
          _ ≤ ‖simpleNVector v‖ * 1 :=
            mul_le_mul_of_nonneg_left hα₀ (ContinuousLinearMap.opNorm_nonneg _)
          _ = ‖simpleNVector v‖ := mul_one _
    rw [hnorm, hgram, Matrix.det_mul, Matrix.det_transpose, sq_abs, sq]
  · -- Dependent family: every alternating map vanishes on `v`, and `G(v) g = 0` for a
    -- nontrivial relation `∑ g j • v j = 0`, so both sides vanish.
    have h0 : ‖simpleNVector v‖ = 0 := by
      refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun α => ?_)
        (ContinuousLinearMap.opNorm_nonneg _)
      have hα : α v = 0 := α.toAlternatingMap.map_linearDependent v hv
      rw [simpleNVector_apply, hα, norm_zero, zero_mul]
    obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hv
    have hdet : (Matrix.of fun i j => inner ℝ (v i) (v j)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨g, fun h => hi₀ (congrFun h i₀), ?_⟩
      funext i
      have h := congrArg (inner ℝ (v i)) hg
      simp only [inner_sum, inner_smul_right, inner_zero_right] at h
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
    rw [h0, hdet, sq, mul_zero]

/-- **Patching lemma** (P4) of the proof of Simon Ch. 6, 8.2 (Remark 8.3(1)): a current that
agrees near every point of `U` with an integer multiplicity current is integer multiplicity.
By Lindelöf, countably many `V (e i)` cover `U`, with `X = Y (e i) = τ(Mᵢ, θᵢ, ξᵢ)` on forms
supported in `V (e i)`.  On overlaps the vector densities `1_{Mᵢ} θᵢ ξᵢ` agree `Hᵏ`-a.e. (test
with `g dx^β`, `g ∈ C_c^∞`, and expand covectors by `Submission.slicing_ru_covector_expansion`),
hence so do the multiplicities `1_{Mᵢ} θᵢ`, since `‖ξᵢ‖ = 1` a.e.
(`Submission.lpf_simple_nvector_algebra`).  The triple `(M, θ, ξ)` glued along
`D i = V (e i) \ ⋃_{j < i} V (e j)` therefore agrees a.e. with `(Mᵢ, θᵢ, ξᵢ)` on `V (e i)`;
`Submission.iwl_weighted_tangent_locality` transfers the orientation condition from `(Mᵢ, θᵢ)`
to `(M, θ)`, and `X = τ(M, θ, ξ)` by a smooth partition of unity. -/
theorem Submission.iwl_im_patching : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k, (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y ∧ ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = Y ω) → IsIntegerMultiplicity X := by
  intro P k U hU X hloc
  -- Empty domain: `X = 0 = τ(∅, 1, 0)`.
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · refine ⟨∅, fun _ => 1, fun _ => 0, ⟨Subset.rfl, nullMeasurableSet_empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
      fun x hx => absurd hx (notMem_empty x), fun K _ _ => by simp,
      aestronglyMeasurable_const,
      ae_restrict_of_forall_mem MeasurableSet.empty fun x hx => absurd hx (notMem_empty x)⟩,
      fun x hx => absurd hx (notMem_empty x), fun ω => ?_⟩
    have hω : ω = 0 := by
      apply Subtype.ext
      funext x
      exact image_eq_zero_of_notMem_tsupport fun hx => notMem_empty x (ω.2.2 hx)
    rw [hω, tauAction, Measure.restrict_empty, integral_zero_measure]
    exact map_zero X.toCurrent
  -- Fact (a): `‖ξ‖ = 1` `Hᵏ`-a.e. on `M`.  A.e. `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ` orthonormal, and
  -- `‖τ₁ ∧ ⋯ ∧ τₖ‖² = det (⟪τᵢ, τⱼ⟫) = 1`.
  have norm_eq_one : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ} {ξ : Eucl P → NVector (Eucl P) k},
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ M → ‖ξ x‖ = 1 := by
    intro M θ ξ h
    rw [← ae_restrict_iff'₀ h.nullMeasurableSet]
    filter_upwards [h.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hgram : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
    have hsq := Submission.lpf_simple_nvector_algebra.1 P k τ
    rw [hgram, Matrix.det_one] at hsq
    have h1 : ‖simpleNVector τ‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg (simpleNVector τ)) two_ne_zero).mp hsq
    rcases hξ with hξ | hξ
    · rw [hξ, h1]
    · rw [hξ, ContinuousLinearMap.opNorm_neg, h1]
  -- Fact (d): `‖1_M θ ξ‖ = 1_M θ` a.e., as `θ > 0` on `M`.
  have norm_indicator : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ} {ξ : Eucl P → NVector (Eucl P) k},
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)),
        ‖M.indicator (fun y => θ y • ξ y) x‖ = M.indicator θ x := by
    intro M θ ξ h
    filter_upwards [norm_eq_one h] with x hx
    by_cases hxM : x ∈ M
    · rw [indicator_of_mem hxM, indicator_of_mem hxM,
        @norm_smul ℝ (NVector (Eucl P) k) _ _ _ NormedSpace.toNormSMulClass, hx hxM, mul_one,
        Real.norm_of_nonneg (h.pos x hxM).le]
    · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, ContinuousLinearMap.opNorm_zero]
  -- `τ(M, θ, ξ)(ω) = ∫ ⟨ω, 1_M θ ξ⟩ dHᵏ` (Simon Ch. 6, 3.1 (‡)) for `Hᵏ`-null-measurable `M`.
  have tau_eq_integral : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ}
      {ξ : Eucl P → NVector (Eucl P) k}, NullMeasurableSet M (μHE[k] : Measure (Eucl P)) →
      ∀ ω : DifferentialForm (Eucl P) k, tauAction k M θ ξ ω =
        ∫ x, M.indicator (fun y => θ y • ξ y) x (ω x) ∂(μHE[k] : Measure (Eucl P)) := by
    intro M θ ξ hM ω
    rw [tauAction, ← integral_indicator₀ hM]
    congr 1
    funext x
    by_cases hx : x ∈ M <;> simp [hx]
  -- Fact (b): for a continuous form `η`, `⟨η, 1_M θ ξ⟩` is `Hᵏ`-integrable on each compact
  -- `K ⊆ U`, since `|⟨η, θ ξ⟩| ≤ |θ| sup_K ‖η‖` a.e. on `M ∩ K`.
  have integrableOn_pairing : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ}
      {ξ : Eucl P → NVector (Eucl P) k}, IsRectifiableTriple U k M θ ξ →
      ∀ {K : Set (Eucl P)}, IsCompact K → K ⊆ U → ∀ {η : DifferentialForm (Eucl P) k},
      Continuous η → IntegrableOn (fun x => M.indicator (fun y => θ y • ξ y) x (η x)) K
        (μHE[k] : Measure (Eucl P)) := by
    intro M θ ξ h K hK hKU η hη
    have heq : (fun x => M.indicator (fun y => θ y • ξ y) x (η x)) =
        M.indicator (fun y => θ y * ξ y (η y)) := by
      funext x
      by_cases hx : x ∈ M <;> simp [hx]
    rw [heq, integrableOn_indicator_iff h.nullMeasurableSet]
    have hθ := h.integrableOn K hK hKU
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hη.continuousOn
    have hev : Continuous fun p : NVector (Eucl P) k × Covector (Eucl P) k => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    have hmeas : AEStronglyMeasurable (fun y => ξ y (η y))
        ((μHE[k] : Measure (Eucl P)).restrict (M ∩ K)) :=
      hev.comp_aestronglyMeasurable
        ((h.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono inter_subset_left le_rfl)).prodMk hη.aestronglyMeasurable)
    refine Integrable.mono' (hθ.norm.mul_const C) (hθ.aestronglyMeasurable.mul hmeas) ?_
    rw [ae_restrict_iff'₀ (h.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet)]
    filter_upwards [norm_eq_one h] with y hy hyMK
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖ξ y (η y)‖ ≤ ‖ξ y‖ * ‖η y‖ := (ξ y).le_opNorm (η y)
      _ = ‖η y‖ := by rw [hy hyMK.1, one_mul]
      _ ≤ C := hC y hyMK.2
  -- Fact (b) for continuous `η` with compact support in `U`: `⟨η, 1_M θ ξ⟩` vanishes off
  -- `tsupport η`, so it is `Hᵏ`-integrable.
  have integrable_pairing : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ}
      {ξ : Eucl P → NVector (Eucl P) k}, IsRectifiableTriple U k M θ ξ →
      ∀ {η : DifferentialForm (Eucl P) k}, Continuous η → HasCompactSupport η →
      tsupport η ⊆ U → Integrable (fun x => M.indicator (fun y => θ y • ξ y) x (η x))
        (μHE[k] : Measure (Eucl P)) := by
    intro M θ ξ h η hη hηc hηU
    have hsupp : (Function.support fun x => M.indicator (fun y => θ y • ξ y) x (η x)) ⊆
        tsupport η := by
      intro x hx
      by_contra hxη
      apply hx
      dsimp only
      rw [image_eq_zero_of_notMem_tsupport hxη, map_zero]
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    exact integrableOn_pairing h hηc hηU hη
  -- Fact (c), uniqueness of the vector measure `θ ξ Hᵏ ⌞ M`: if `τ(M, θ, ξ)` and `τ(M', θ', ξ')`
  -- agree on test forms supported in an open `O ⊆ U`, then `1_M θ ξ = 1_{M'} θ' ξ'` a.e. on `O`.
  -- For a constant covector `α`, testing with `ω = g α` (`g ∈ C_c^∞(O)`) shows that the locally
  -- integrable `⟨α, 1_M θ ξ - 1_{M'} θ' ξ'⟩` vanishes as a distribution on `O`, hence a.e. on
  -- `O`; the coordinate covectors `dx^β` determine an `n`-vector.
  have ae_eq : ∀ {O : Set (Eucl P)}, IsOpen O → O ⊆ U → ∀ {M M' : Set (Eucl P)}
      {θ θ' : Eucl P → ℝ} {ξ ξ' : Eucl P → NVector (Eucl P) k},
      IsRectifiableTriple U k M θ ξ → IsRectifiableTriple U k M' θ' ξ' →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M θ ξ ω = tauAction k M' θ' ξ' ω) →
      ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
        M.indicator (fun y => θ y • ξ y) x = M'.indicator (fun y => θ' y • ξ' y) x := by
    intro O hO hOU M M' θ θ' ξ ξ' h h' heq
    have hcoord : ∀ α : Covector (Eucl P) k, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
        M.indicator (fun y => θ y • ξ y) x α = M'.indicator (fun y => θ' y • ξ' y) x α := by
      intro α
      have hli : LocallyIntegrableOn (fun x => M.indicator (fun y => θ y • ξ y) x α -
          M'.indicator (fun y => θ' y • ξ' y) x α) O (μHE[k] : Measure (Eucl P)) := by
        rw [locallyIntegrableOn_iff hO.isLocallyClosed]
        intro K hKO hK
        exact (integrableOn_pairing h hK (hKO.trans hOU) (η := fun _ => α)
          continuous_const).sub
          (integrableOn_pairing h' hK (hKO.trans hOU) (η := fun _ => α) continuous_const)
      have key := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
      · filter_upwards [key] with x hx hxO
        exact sub_eq_zero.mp (hx hxO)
      intro g hg hgc hgO
      have hηc : Continuous fun x => g x • α := hg.continuous.smul continuous_const
      have hηcs : HasCompactSupport fun x => g x • α := hgc.smul_right (f' := fun _ => α)
      have hηO : tsupport (fun x => g x • α) ⊆ O := (tsupport_smul_subset_left _ _).trans hgO
      have h1 := integrable_pairing h hηc hηcs (hηO.trans hOU)
      have h2 := integrable_pairing h' hηc hηcs (hηO.trans hOU)
      have heqα := heq ⟨fun x => g x • α, ⟨hg.smul contDiff_const, hηcs⟩, hηO.trans hOU⟩ hηO
      rw [tau_eq_integral h.nullMeasurableSet, tau_eq_integral h'.nullMeasurableSet] at heqα
      calc ∫ x, g x • (M.indicator (fun y => θ y • ξ y) x α -
            M'.indicator (fun y => θ' y • ξ' y) x α) ∂(μHE[k] : Measure (Eucl P))
          = ∫ x, (M.indicator (fun y => θ y • ξ y) x (g x • α) -
              M'.indicator (fun y => θ' y • ξ' y) x (g x • α)) ∂(μHE[k] : Measure (Eucl P)) := by
            congr 1
            funext x
            simp only [map_smul, smul_eq_mul, mul_sub]
        _ = ∫ x, M.indicator (fun y => θ y • ξ y) x (g x • α) ∂(μHE[k] : Measure (Eucl P)) -
              ∫ x, M'.indicator (fun y => θ' y • ξ' y) x (g x • α)
                ∂(μHE[k] : Measure (Eucl P)) := integral_sub h1 h2
        _ = 0 := sub_eq_zero.mpr heqα
    have hall := ae_all_iff.mpr fun β : SimonMultiIndex k P =>
      hcoord (wedgeCovectors k fun j => EuclideanSpace.proj (β j))
    filter_upwards [hall] with x hx hxO
    refine ContinuousLinearMap.ext fun α => ?_
    rw [Submission.slicing_ru_covector_expansion P k α, map_sum, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_smul, map_smul, hx β hxO]
  -- Step 1 (Lindelöf): countably many `V (e i)` cover `U`.
  have hloc' : ∀ x : U, ∃ V : Set (Eucl P), IsOpen V ∧ (x : Eucl P) ∈ V ∧ V ⊆ U ∧
      ∃ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y ∧
        ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = Y ω :=
    fun x => hloc x x.2
  choose V hVo hxV hVU Y hY hXY using hloc'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcovT : ∀ y ∈ U, ∃ x ∈ T, y ∈ V x := by
    intro y hy
    have hy' : y ∈ ⋃ x ∈ T, V x := by
      rw [hTU]
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
    simpa only [mem_iUnion, exists_prop] using hy'
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨x₀, hx₀T, -⟩ := hcovT y₀ hy₀
  obtain ⟨e, rfl⟩ := hTc.exists_eq_range ⟨x₀, hx₀T⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Set (Eucl P), ∀ i, W i = V (e i) := ⟨_, fun _ => rfl⟩
  have hWo : ∀ i, IsOpen (W i) := fun i => by rw [hW]; exact hVo (e i)
  have hWU : ∀ i, W i ⊆ U := fun i => by rw [hW]; exact hVU (e i)
  have hcov : ∀ x ∈ U, ∃ i, x ∈ W i := by
    intro x hx
    obtain ⟨_, ⟨i, rfl⟩, hxi⟩ := hcovT x hx
    exact ⟨i, by rw [hW]; exact hxi⟩
  -- The local integer multiplicity triples `Y (e i) = τ(Mᵢ, θᵢ, ξᵢ)`.
  have hY' : ∀ i, ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ ∧ (∀ x ∈ M, ∃ n : ℕ, θ x = n) ∧
        ∀ ω : TestFormOn U k, Y (e i) ω = tauAction k M θ ξ ω := fun i => hY (e i)
  choose Ms θs ξs hTr hNat hRep using hY'
  have hXW : ∀ i (ω : TestFormOn U k), tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W i →
      X ω = tauAction k (Ms i) (θs i) (ξs i) ω := fun i ω hω =>
    (hXY (e i) ω (by rw [← hW]; exact hω)).trans (hRep i ω)
  -- Step 2: the local triples agree a.e. on overlaps (facts (c), (d)).
  have hcompat : ∀ i j, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ W i ∩ W j →
      (Ms i).indicator (fun y => θs i y • ξs i y) x =
        (Ms j).indicator (fun y => θs j y • ξs j y) x ∧
      (Ms i).indicator (θs i) x = (Ms j).indicator (θs j) x := by
    intro i j
    have hF := ae_eq ((hWo i).inter (hWo j)) (inter_subset_left.trans (hWU i)) (hTr i) (hTr j)
      fun ω hω => (hXW i ω (hω.trans inter_subset_left)).symm.trans
        (hXW j ω (hω.trans inter_subset_right))
    filter_upwards [hF, norm_indicator (hTr i), norm_indicator (hTr j)] with x h1 h2 h3 hx
    refine ⟨h1 hx, ?_⟩
    rw [← h2, ← h3, h1 hx]
  -- Step 3: glue along `D i = {x ∈ U | i is the least index with x ∈ W i}`.
  obtain ⟨idx, hidx⟩ : ∃ idx : Eucl P → ℕ, ∀ x, idx x = sInf {i | x ∈ W i} :=
    ⟨_, fun _ => rfl⟩
  have hidx_mem : ∀ x ∈ U, x ∈ W (idx x) := fun x hx => by
    rw [hidx]
    exact Nat.sInf_mem (hcov x hx)
  have hidx_le : ∀ x i, x ∈ W i → idx x ≤ i := fun x i hx => by
    rw [hidx]
    exact Nat.sInf_le hx
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Set (Eucl P), ∀ i, D i = {x | x ∈ U ∧ idx x = i} :=
    ⟨_, fun _ => rfl⟩
  have hmemD : ∀ x ∈ U, x ∈ D (idx x) := fun x hx => by
    rw [hD]
    exact ⟨hx, rfl⟩
  have hDU : ∀ i, D i ⊆ U := fun i x hx => by
    rw [hD] at hx
    exact hx.1
  have hidxD : ∀ i x, x ∈ D i → idx x = i := fun i x hx => by
    rw [hD] at hx
    exact hx.2
  have hDW : ∀ i, D i ⊆ W i := fun i x hx => by
    rw [← hidxD i x hx]
    exact hidx_mem x (hDU i hx)
  have hDmeas : ∀ i, MeasurableSet (D i) := by
    intro i
    have hDeq : D i = W i \ ⋃ j ∈ Finset.range i, W j := by
      ext x
      simp only [Set.mem_sdiff, mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and]
      constructor
      · intro hx
        refine ⟨hDW i hx, fun j hj hxj => ?_⟩
        have := hidx_le x j hxj
        rw [hidxD i x hx] at this
        omega
      · rintro ⟨hxi, hnot⟩
        rw [hD]
        refine ⟨hWU i hxi, le_antisymm (hidx_le x i hxi) ?_⟩
        by_contra hlt
        exact hnot _ (not_le.mp hlt) (hidx_mem x (hWU i hxi))
    rw [hDeq]
    exact (hWo i).measurableSet.diff
      (Finset.measurableSet_biUnion _ fun j _ => (hWo j).measurableSet)
  obtain ⟨M, hM⟩ : ∃ M : Set (Eucl P), M = ⋃ i, D i ∩ Ms i := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : Eucl P → ℝ, ∀ x, θ x = θs (idx x) x := ⟨_, fun _ => rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Eucl P → NVector (Eucl P) k, ∀ x, ξ x = ξs (idx x) x :=
    ⟨_, fun _ => rfl⟩
  have hMD : ∀ i x, x ∈ D i → (x ∈ M ↔ x ∈ Ms i) := by
    intro i x hx
    rw [hM, mem_iUnion]
    constructor
    · rintro ⟨j, hxj, hxM⟩
      rwa [← hidxD j x hxj, hidxD i x hx] at hxM
    · exact fun hxM => ⟨i, hx, hxM⟩
  have hθD : ∀ i x, x ∈ D i → θ x = θs i x := fun i x hx => by rw [hθ, hidxD i x hx]
  have hξD : ∀ i x, x ∈ D i → ξ x = ξs i x := fun i x hx => by rw [hξ, hidxD i x hx]
  have hFD : ∀ i x, x ∈ D i →
      M.indicator (fun y => θ y • ξ y) x = (Ms i).indicator (fun y => θs i y • ξs i y) x ∧
      M.indicator θ x = (Ms i).indicator (θs i) x := by
    intro i x hx
    by_cases hxM : x ∈ Ms i
    · have hxM' : x ∈ M := (hMD i x hx).mpr hxM
      simp only [indicator_of_mem hxM, indicator_of_mem hxM', hθD i x hx, hξD i x hx, and_self]
    · have hxM' : x ∉ M := fun h => hxM ((hMD i x hx).mp h)
      simp only [indicator_of_notMem hxM, indicator_of_notMem hxM', and_self]
  -- Step 4: on `W i` the glued triple agrees a.e. with the `i`-th one.
  have hagree : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ W i →
      M.indicator (fun y => θ y • ξ y) x = (Ms i).indicator (fun y => θs i y • ξs i y) x ∧
      M.indicator θ x = (Ms i).indicator (θs i) x := by
    intro i
    filter_upwards [ae_all_iff.mpr fun j => hcompat j i] with x hx hxi
    have hxU := hWU i hxi
    obtain ⟨h1, h2⟩ := hFD _ x (hmemD x hxU)
    obtain ⟨h3, h4⟩ := hx (idx x) ⟨hidx_mem x hxU, hxi⟩
    exact ⟨h1.trans h3, h2.trans h4⟩
  -- Step 6: `(M, θ, ξ)` is a rectifiable triple.
  have hMnull : NullMeasurableSet M (μHE[k] : Measure (Eucl P)) := by
    rw [hM]
    exact NullMeasurableSet.iUnion fun i =>
      (hDmeas i).nullMeasurableSet.inter (hTr i).nullMeasurableSet
  have hMU : M ⊆ U := by
    rw [hM]
    exact iUnion_subset fun i => inter_subset_left.trans (hDU i)
  have hGloc : LocallyIntegrableOn (M.indicator θ) U (μHE[k] : Measure (Eucl P)) := by
    intro x hxU
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp (hWo (idx x)) x (hidx_mem x hxU)
    have hsub : closedBall x (ε / 2) ⊆ W (idx x) :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεW
    refine ⟨closedBall x (ε / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hε)), ?_⟩
    have hint : IntegrableOn ((Ms (idx x)).indicator (θs (idx x))) (closedBall x (ε / 2))
        (μHE[k] : Measure (Eucl P)) := by
      rw [integrableOn_indicator_iff (hTr _).nullMeasurableSet]
      exact (hTr _).integrableOn _ (isCompact_closedBall x _) (hsub.trans (hWU _))
    refine hint.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (hagree (idx x)),
      ae_restrict_mem measurableSet_closedBall] with y hy hyB
    exact (hy (hsub hyB)).2.symm
  have hθint : ∀ K, IsCompact K → K ⊆ U →
      IntegrableOn θ (M ∩ K) (μHE[k] : Measure (Eucl P)) := by
    intro K hK hKU
    rw [← integrableOn_indicator_iff hMnull]
    exact hGloc.integrableOn_compact_subset hKU hK
  have hTriple : IsRectifiableTriple U k M θ ξ := by
    refine ⟨hMU, hMnull, ?_, ?_, hθint, ?_, ?_⟩
    · refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion Ms fun i =>
        (hTr i).countablyRectifiable).mono ?_
      rw [hM]
      exact iUnion_mono fun i => inter_subset_right
    · intro x hx
      rw [hM, mem_iUnion] at hx
      obtain ⟨i, hxD, hxM⟩ := hx
      rw [hθD i x hxD]
      exact (hTr i).pos x hxM
    · have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) k) :=
        ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
      rw [hM, aestronglyMeasurable_iUnion_iff]
      intro i
      refine ((hTr i).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)).congr ?_
      filter_upwards [ae_restrict_mem₀
        ((hDmeas i).nullMeasurableSet.inter (hTr i).nullMeasurableSet)] with x hx
      exact (hξD i x hx.1).symm
    · have key : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)).restrict (D i ∩ Ms i),
          ∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
            HasWeightedApproximateTangentSpaceAt k M θ x (Submodule.span ℝ (range τ)) ∧
            (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
        intro i
        filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right (hTr i).orients,
          ae_restrict_mem₀ ((hDmeas i).nullMeasurableSet.inter (hTr i).nullMeasurableSet)]
          with x hx hxDM
        obtain ⟨τ, hτ, hT, hξx⟩ := hx
        obtain ⟨hxD, -⟩ := hxDM
        refine ⟨τ, hτ, ?_, by rwa [hξD i x hxD]⟩
        -- Transfer the tangent plane from `(Mᵢ, θᵢ)` to `(M, θ)` by tangent locality.
        obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp (hWo i) x (hDW i hxD)
        have hρ : 0 < ε / 2 := half_pos hε
        have hsub : closedBall x (ε / 2) ⊆ W i :=
          (closedBall_subset_ball (half_lt_self hε)).trans hεW
        refine (Submission.iwl_weighted_tangent_locality P k (Ms i) M (θs i) θ x
          (hTr i).nullMeasurableSet hMnull (hθD i x hxD).symm
          ⟨ε / 2, hρ, (hTr i).integrableOn _ (isCompact_closedBall x _) (hsub.trans (hWU i)),
            hθint _ (isCompact_closedBall x _) (hsub.trans (hWU i))⟩ ?_ _).mp hT
        intro R hR
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
        have hRr : R * r ≤ ε / 2 := by
          have := (lt_div_iff₀ hR).mp hr.2
          linarith [mul_comm R r]
        have hae : ∀ᵐ z ∂(μHE[k] : Measure (Eucl P)).restrict (closedBall x (R * r)),
            ‖(Ms i).indicator (θs i) z - M.indicator θ z‖ₑ = 0 := by
          filter_upwards [ae_restrict_of_ae (hagree i),
            ae_restrict_mem measurableSet_closedBall] with z hz hzB
          rw [(hz (hsub (closedBall_subset_closedBall hRr hzB))).2, sub_self, enorm_zero]
        rw [lintegral_congr_ae hae, lintegral_zero, mul_zero]
      have := (ae_restrict_iUnion_iff (fun i => D i ∩ Ms i) _).mpr key
      rwa [← hM] at this
  -- Step 5: `X = τ(M, θ, ξ)` on forms supported in some `W i`, hence on all forms.
  have hXloc : ∀ i (ω : TestFormOn U k), tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W i →
      X ω = tauAction k M θ ξ ω := by
    intro i ω hω
    rw [hXW i ω hω, tau_eq_integral (hTr i).nullMeasurableSet, tau_eq_integral hMnull]
    refine integral_congr_ae ?_
    filter_upwards [hagree i] with x hx
    by_cases hxW : x ∈ W i
    · rw [(hx hxW).1]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hω h), map_zero, map_zero]
  refine ⟨M, θ, ξ, hTriple, ?_, fun ω => ?_⟩
  · intro x hx
    rw [hM, mem_iUnion] at hx
    obtain ⟨i, hxD, hxM⟩ := hx
    rw [hθD i x hxD]
    exact hNat i x hxM
  -- A smooth partition of unity `(ρᵢ)` subordinate to a finite subcover of `tsupport ω` splits
  -- `ω = ∑ ρᵢ ω`; `X` is linear and `τ(M, θ, ξ)` is additive on the integrable pieces.
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) := ω.2.1.1
  have hωc : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
  have hωU : tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U := ω.2.2
  obtain ⟨t, ht⟩ := hωc.isCompact.elim_finite_subcover W hWo
    (hωU.trans fun x hx => mem_iUnion.mpr (hcov x hx))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ (Eucl P))
    (isClosed_tsupport (ω : DifferentialForm (Eucl P) k)) (fun i : t => W i) (fun i => hWo i)
    (by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  have hρs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i =>
    contMDiff_iff_contDiff.mp (ρ i).contMDiff
  let ωi : t → TestFormOn U k := fun i =>
    ⟨fun x => ρ i x • (ω : DifferentialForm (Eucl P) k) x,
      ⟨(hρs i).smul hωs, IsCompact.of_isClosed_subset hωc (isClosed_tsupport _)
        (tsupport_smul_subset_right _ _)⟩, (tsupport_smul_subset_right _ _).trans hωU⟩
  have hsum' : ∀ x, (ω : DifferentialForm (Eucl P) k) x =
      ∑ i, ρ i x • (ω : DifferentialForm (Eucl P) k) x := by
    intro x
    by_cases hx : x ∈ tsupport (ω : DifferentialForm (Eucl P) k)
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one hx, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [hsum' x, Submodule.coe_sum, Finset.sum_apply]
  have hint : ∀ i, Integrable (fun x => M.indicator (fun y => θ y • ξ y) x
      ((ωi i : DifferentialForm (Eucl P) k) x)) (μHE[k] : Measure (Eucl P)) := fun i =>
    integrable_pairing hTriple (ωi i).2.1.1.continuous (ωi i).2.1.2 (ωi i).2.2
  calc X ω = ∑ i, X (ωi i) := by
        conv_lhs => rw [hsum]
        exact map_sum X.toCurrent _ _
    _ = ∑ i, tauAction k M θ ξ (ωi i) :=
        Finset.sum_congr rfl fun i _ =>
          hXloc i (ωi i) ((tsupport_smul_subset_left _ _).trans (hρ i))
    _ = tauAction k M θ ξ ω := by
        simp only [tau_eq_integral hMnull]
        rw [← integral_finsetSum _ fun i _ => hint i]
        congr 1
        funext x
        rw [hsum' x, map_sum]

/-- Simon Ch. 6, 8.2 in the case `n = 0` (p. 176, "the theorem is trivial in case `n = 0`"): a
weak limit `X` of integer multiplicity `X_j ∈ 𝒟₀(U)` with `sup_j M_W(X_j) < ∞` for all `W ⊂⊂ U` is
integer multiplicity.  Each `X_j = τ(M_j, θ_j, ξ_j)` is a locally finite sum
`X_j(ω) = ∑_{x ∈ M_j} c_j(x) ω(x)` with `c_j = ±θ_j ∈ ℤ ∖ {0}`, and testing with signed bumps gives
`∑_{x ∈ S} |c_j(x)| ≤ M_W(X_j)` for finite `S ⊆ M_j ∩ W`.  On `W = B_{ε/2}(x₀) ⊂⊂ U`,
`br_zd_dirac_local_limit` makes `X` a finite integer Dirac sum on forms supported in `W`, which is
integer multiplicity by `br_zd_finite_dirac_im`, and `iwl_im_patching` globalizes. -/
theorem Submission.iwl_zero_dim_integrality : ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0), (∀ j, IsIntegerMultiplicity (Xj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, (Xj j).massOn W) < ∞) → WeaklyConvergesOn Xj X → IsIntegerMultiplicity X := by
  classical
  intro P U hU Xj X hXj hmass hconv
  -- Step 1: an integer multiplicity `Y = τ(M, θ, ξ) ∈ 𝒟₀(U)` is `Y(ω) = ∑ᶠ_{x ∈ M} c(x) ω(x)(![])`
  -- with `c(x) ≠ 0` on `M` and `M ∩ K` finite for compact `K ⊆ U`.
  have hrepr : ∀ Y : GeometricCurrentOn U 0, IsIntegerMultiplicity Y →
      ∃ (N : Set (Eucl P)) (c : Eucl P → ℤ),
        (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) ∧ (∀ x ∈ N, c x ≠ 0) ∧
          ∀ ω : TestFormOn U 0,
            Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
    rintro Y ⟨M, θ, ξ, hT, hθ, hY⟩
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
    have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
        IntegrableOn g (F : Set (Eucl P)) μ := by
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
    have hpair : ∀ (w : NVector (Eucl P) 0) (α : Covector (Eucl P) 0),
        w α = α ![] * w one0 := by
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
    refine ⟨M, c, hlocfin, fun x hx => (hcM x hx).2, ?_⟩
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
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := (S : Set (Eucl P)))
      hT.nullMeasurableSet (by rw [hSM]; exact inter_subset_left)
      (Eventually.of_forall fun x hx => ?_)]
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
  -- Step 2: if `Y(ω) = ∑ᶠ_{x ∈ N} c(x) ω(x)(![])` with `N ∩ K` finite for compact `K ⊆ U`, then
  -- `∑_{x ∈ S} |c(x)| ≤ M_W(Y)` for finite `S ⊆ N ∩ W`, `W ⊆ U` open.  Test with
  -- `ω = ∑_{x ∈ S} sign(c(x)) φₓ`, where the bumps `φₓ` (`φₓ(x) = 1`) have pairwise disjoint
  -- supports `B(x, δ) ⊆ W` meeting `N` only in `x`: then `|ω| ≤ 1` and `Y(ω) = ∑_{x ∈ S} |c(x)|`.
  have hmassge : ∀ (W N : Set (Eucl P)) (Y : GeometricCurrentOn U 0) (c : Eucl P → ℤ),
      IsOpen W → W ⊆ U → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) →
      (∀ ω : TestFormOn U 0,
        Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) →
      ∀ S : Finset (Eucl P), (↑S : Set (Eucl P)) ⊆ N ∩ W →
        ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) ≤ Y.massOn W := by
    intro W N Y c hW hWU hN hY S hS
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
  -- Steps 3–7: on `W = B_{ε/2}(x₀) ⊂⊂ U`, `Λ = sup_j M_W(X_j) < ∞` bounds the coefficients of the
  -- `X_j` in `W`, so `X` agrees on forms supported in `W` with a finite integer Dirac sum, which is
  -- integer multiplicity; `iwl_im_patching` (with `k = 0`) globalizes.
  choose N c hNfin hc hN using fun j => hrepr (Xj j) (hXj j)
  refine Submission.iwl_im_patching P 0 U hU X fun x₀ hx₀ => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hWU : closure (ball x₀ (ε / 2)) ⊆ U :=
    closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hε)).trans hεU)
  have hWcpt : IsCompact (closure (ball x₀ (ε / 2))) :=
    (isCompact_closedBall x₀ (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hΛ : (⨆ j, (Xj j).massOn (ball x₀ (ε / 2))) ≠ ∞ :=
    (hmass _ ⟨isOpen_ball, hWcpt, hWU⟩).ne
  obtain ⟨D, a, hDW, hXD⟩ := Submission.br_zd_dirac_local_limit P U (ball x₀ (ε / 2)) Xj X N c
    _ hWcpt hconv hc
    (fun j => (hNfin j _ hWcpt hWU).subset (inter_subset_inter_right _ subset_closure))
    (fun j S hS => (ENNReal.ofReal_le_iff_le_toReal hΛ).1
      ((hmassge _ (N j) (Xj j) (c j) isOpen_ball (subset_closure.trans hWU) (hNfin j) (hN j) S
        hS).trans (le_iSup (fun i => (Xj i).massOn (ball x₀ (ε / 2))) j)))
    (fun j ω _ => hN j ω)
  obtain ⟨Y, hYim, hY⟩ := Submission.br_zd_finite_dirac_im P U D a
    (hDW.trans (subset_closure.trans hWU))
  exact ⟨ball x₀ (ε / 2), isOpen_ball, mem_ball_self (half_pos hε), subset_closure.trans hWU, Y,
    hYim, fun ω hω => (hXD ω hω).trans (hY ω).symm⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
