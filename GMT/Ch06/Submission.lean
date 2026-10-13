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

/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9 (p. 148): the
inverse-function-theorem estimate.  If `G : ℝⁿ → ℝ^Q` is `C¹` and `DG(w)` is injective, then
`c |z − z'| ≤ |G z − G z'|` for all `z, z'` in some ball `B_r(w)`, with `c > 0`. -/
theorem Submission.lpf_c1_local_antilipschitz :
    ∀ (n Q : ℕ) (G : Eucl n → Eucl Q) (w : Eucl n), ContDiff ℝ 1 G →
      Function.Injective (fderiv ℝ G w) →
      ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ ball w r, ∀ z' ∈ ball w r,
        c * ‖z - z'‖ ≤ ‖G z - G z'‖ := by
  intro n Q G w hG hinj
  set A : Eucl n →L[ℝ] Eucl Q := fderiv ℝ G w
  -- `A` is injective on the finite-dimensional `ℝⁿ`, hence antilipschitz: `|v| ≤ K |A v|`,
  -- i.e. `|A v| ≥ m |v|` with `m = K⁻¹ > 0`.
  obtain ⟨K, hKpos, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q)).mp hinj
  have hK0 : (0 : ℝ) < K := hKpos
  have hm : ∀ v : Eucl n, (K : ℝ)⁻¹ * ‖v‖ ≤ ‖A v‖ := by
    intro v
    rw [inv_mul_le_iff₀ hK0]
    exact ZeroHomClass.bound_of_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q) hK v
  -- `c = m / 2`.  `A` is the strict derivative of `G` at `w`, so `G` approximates `A` with
  -- constant `c` on a neighbourhood of `w`, which contains a ball `B_r(w)`.
  set c : ℝ≥0 := K⁻¹ / 2 with hc
  have hc0 : 0 < c := by
    rw [hc]
    exact div_pos (inv_pos.mpr hKpos) two_pos
  have hcK : (c : ℝ) = (K : ℝ)⁻¹ / 2 := by
    rw [hc, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_two]
  have hstrict : HasStrictFDerivAt G A w := hG.hasStrictFDerivAt one_ne_zero
  obtain ⟨s, hs, happrox⟩ := hstrict.approximates_deriv_on_nhds (c := c) (Or.inr hc0)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r, hr, c, hc0, fun z hz z' hz' => ?_⟩
  -- On `B_r(w)`, `|G z − G z' − A (z − z')| ≤ c |z − z'|`; with the triangle inequality,
  -- `m |z − z'| ≤ |A (z − z')| ≤ |G z − G z'| + c |z − z'|`, and `m − c = c`.
  have h1 : ‖G z - G z' - A (z - z')‖ ≤ c * ‖z - z'‖ := happrox z (hrs hz) z' (hrs hz')
  have h2 := hm (z - z')
  have h3 : ‖A (z - z')‖ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := by
    calc ‖A (z - z')‖ = ‖(G z - G z') - (G z - G z' - A (z - z'))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := norm_sub_le _ _
  rw [hcK] at h1 ⊢
  linarith

/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70) and Remark 1.3, for one `C¹` map `G : ℝⁿ → ℝ^P`:
countably many open sets `O k` on each of which `G` is Lipschitz and bi-Lipschitz onto its image
cover `G(ℝⁿ)` up to an `Hⁿ`-null set.  Regular points (`DG(w)` injective) lie in some `O k`;
the image of the critical set is `Hⁿ`-null: near a critical point, `G` composed with a linear map
that shrinks the directions orthogonal to a kernel vector has a small Lipschitz constant. -/
theorem Submission.slicing_im_tg_cc_contDiff_range_chart_cover : ∀ (n P : ℕ) (G : Eucl n → Eucl P), ContDiff ℝ 1 G → ∃ O : ℕ → Set (Eucl n), (∀ k, IsOpen (O k)) ∧ (∀ k, ∃ K : ℝ≥0, LipschitzOnWith K G (O k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G w - G w'‖) ∧ (μHE[n] : Measure (Eucl P)) (range G \ ⋃ k, G '' O k) = 0 := by
  intro n P G hG
  -- A countable basis `𝔅` of `ℝⁿ`; enumerate `{∅} ∪ {U ∈ 𝔅 : G Lipschitz and antilipschitz on U}`.
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Eucl n)
  set good : Set (Set (Eucl n)) := {U | U ∈ b ∧ (∃ K : ℝ≥0, LipschitzOnWith K G U) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ U, ∀ w' ∈ U, c * ‖w - w'‖ ≤ ‖G w - G w'‖} with hgood
  have hgc : (insert ∅ good).Countable := (hbc.mono fun U hU => hU.1).insert ∅
  obtain ⟨O, hO⟩ := hgc.exists_eq_range (insert_nonempty _ _)
  have hOk : ∀ k, O k = ∅ ∨ O k ∈ good := fun k => by
    have : O k ∈ insert ∅ good := hO ▸ mem_range_self k
    simpa using this
  -- Each `O k` is open, and `G` is Lipschitz and antilipschitz on it.
  refine ⟨O, fun k => ?_, fun k => ?_, fun k => ?_, ?_⟩
  · rcases hOk k with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h.1
  · rcases hOk k with h | h
    · exact ⟨0, by rw [h]; exact lipschitzOnWith_empty _ _⟩
    · exact h.2.1
  · rcases hOk k with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact h.2.2
  · -- A regular point has an antilipschitz ball and a Lipschitz neighbourhood, hence a good
    -- basis set around it.
    have hreg : ∀ w, Function.Injective (fderiv ℝ G w) → ∃ k, w ∈ O k := by
      intro w hw
      obtain ⟨r, hr, c, hc, hcr⟩ := Submission.lpf_c1_local_antilipschitz n P G w hG hw
      obtain ⟨K, t, ht, hKt⟩ := hG.locallyLipschitz w
      have hmem : ball w r ∩ t ∈ 𝓝 w := inter_mem (ball_mem_nhds w hr) ht
      obtain ⟨U, hUb, hwU, hUs⟩ := hb.mem_nhds_iff.1 hmem
      have hUg : U ∈ good := ⟨hUb, ⟨K, hKt.mono fun x hx => (hUs hx).2⟩,
        ⟨c, hc, fun z hz z' hz' => hcr z (hUs hz).1 z' (hUs hz').1⟩⟩
      obtain ⟨k, hk⟩ : U ∈ range O := hO ▸ mem_insert_of_mem _ hUg
      exact ⟨k, hk ▸ hwU⟩
    -- The critical set `C = {w : DG(w) not injective}` has `Hⁿ`-null image, and `G(C)` contains
    -- every uncovered point of `G(ℝⁿ)`.
    set C : Set (Eucl n) := {x | ¬ Function.Injective (fderiv ℝ G x)}
    have hcrit : (μHE[n] : Measure (Eucl P)) (G '' C) = 0 := by
      have hD : ∀ x, HasFDerivAt G (fderiv ℝ G x) x :=
        fun x => ((hG.differentiable one_ne_zero) x).hasFDerivAt
      -- It suffices to treat the bounded pieces `s = C ∩ B_R(0)`.
      have hR : ∀ R : ℕ, (μHE[n] : Measure (Eucl P)) (G '' (C ∩ ball 0 R)) = 0 := by
        intro R
        set s : Set (Eucl n) := C ∩ ball 0 R
        have hsfin : volume s ≠ ∞ :=
          ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        -- Main estimate: `Hⁿ(G(s)) ≤ 2ⁿ ε |s|` for every `0 < ε ≤ 1`.
        have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            (μHE[n] : Measure (Eucl P)) (G '' s) ≤ ENNReal.ofReal (2 ^ n * ε) * volume s := by
          intro ε hε hε1
          rcases s.eq_empty_or_nonempty with hse | hsne
          · rw [hse, image_empty, measure_empty]
            exact zero_le
          -- Partition `s` into measurable pieces `s ∩ t j` on which `G` is approximated by
          -- `A j = DG(y)`, `y ∈ s`, up to `δ = ε / (‖A j‖ + 1)ⁿ`.
          obtain ⟨t, A, htd, htm, hst, hA, hAy⟩ :=
            exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
              (fun x _ => (hD x).hasFDerivWithinAt)
              (fun B => ⟨ε / (‖B‖ + 1) ^ n, by positivity⟩)
              (fun B => ne_of_gt
                (NNReal.coe_pos.1 (show (0 : ℝ) < ε / (‖B‖ + 1) ^ n by positivity)))
          have hpiece : ∀ j, (μHE[n] : Measure (Eucl P)) (G '' (s ∩ t j)) ≤
              ENNReal.ofReal (2 ^ n * ε) * volume (s ∩ t j) := by
            intro j
            obtain ⟨y, hys, hyA⟩ := hAy hsne j
            -- A unit vector `u` in the kernel of `A j = DG(y)`.
            obtain ⟨u, hu1, hAu⟩ : ∃ u : Eucl n, ‖u‖ = 1 ∧ A j u = 0 := by
              have hni : ¬ Function.Injective (A j) := by rw [hyA]; exact hys.1
              obtain ⟨v, hv, hv0⟩ : ∃ v, A j v = 0 ∧ v ≠ 0 := by
                by_contra hcon
                refine hni ((injective_iff_map_eq_zero (A j)).2 fun v hv => ?_)
                by_contra hv0
                exact hcon ⟨v, hv, hv0⟩
              refine ⟨‖v‖⁻¹ • v, ?_, by rw [map_smul, hv, smul_zero]⟩
              rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
            -- `L = ‖A j‖ + 1`, `δ = ε / Lⁿ`, `a = δ / L`; `T = a • id + (1 - a) • ⟪u, ·⟫ u`
            -- shrinks `u⊥` by the factor `a` and fixes `u`.
            set L : ℝ := ‖A j‖ + 1
            have hL1 : 1 ≤ L := le_add_of_nonneg_left (norm_nonneg _)
            have hL0 : 0 < L := by linarith
            set δ : ℝ := ε / L ^ n with hδ
            have hδ0 : 0 < δ := by positivity
            set a : ℝ := δ / L with ha
            have ha0 : 0 < a := by positivity
            have ha1 : a ≤ 1 := by
              rw [ha, hδ, div_div, div_le_one (by positivity)]
              exact hε1.trans (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hL1)
            set T : Eucl n →ₗ[ℝ] Eucl n :=
              a • LinearMap.id + (1 - a) • (innerₛₗ ℝ u).smulRight u with hT
            have hTw : ∀ w, T w = a • w + (1 - a) • (inner ℝ u w • u) := fun w => by
              simp only [hT, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
                LinearMap.smulRight_apply, innerₛₗ_apply_apply]
            have hAT : ∀ w, A j (T w) = a • A j w := fun w => by
              rw [hTw, map_add, map_smul, map_smul, map_smul, hAu, smul_zero, smul_zero, add_zero]
            have hTn : ∀ w, ‖T w‖ ≤ ‖w‖ := fun w => by
              rw [hTw]
              calc ‖a • w + (1 - a) • (inner ℝ u w • u)‖
                  ≤ ‖a • w‖ + ‖(1 - a) • (inner ℝ u w • u)‖ := norm_add_le _ _
                _ = a * ‖w‖ + (1 - a) * (|inner ℝ u w| * ‖u‖) := by
                    rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg ha0.le,
                      Real.norm_of_nonneg (sub_nonneg.2 ha1), Real.norm_eq_abs]
                _ ≤ a * ‖w‖ + (1 - a) * ‖w‖ := by
                    have h1a : 0 ≤ 1 - a := sub_nonneg.2 ha1
                    have hin : |inner ℝ u w| * ‖u‖ ≤ ‖w‖ := by
                      rw [hu1, mul_one]
                      exact (abs_real_inner_le_norm u w).trans (by rw [hu1, one_mul])
                    gcongr
                _ = ‖w‖ := by ring
            -- `det T = aⁿ / a`, computed in the standard basis (matrix determinant lemma).
            have hdet : LinearMap.det T = a ^ n / a := by
              set e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with he
              have hM : LinearMap.toMatrix e e T = a • (1 + Matrix.replicateCol Unit
                  (((1 - a) / a) • fun i => u i) * Matrix.replicateRow Unit (fun i => u i)) := by
                ext i j
                rw [LinearMap.toMatrix_apply]
                simp [he, hT, Matrix.one_apply, Matrix.mul_apply, EuclideanSpace.inner_single_right]
                have h' : a * ((1 - a) / a) = 1 - a := mul_div_cancel₀ _ ha0.ne'
                split_ifs <;> linear_combination (-(u i * u j)) * h'
              have hdot : (fun i => u i) ⬝ᵥ (fun i => u i) = 1 := by
                have h := EuclideanSpace.norm_sq_eq u
                rw [hu1, one_pow] at h
                rw [h, dotProduct]
                simp [sq]
              rw [← LinearMap.det_toMatrix e, hM, Matrix.det_smul,
                Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hdot,
                Fintype.card_fin, smul_eq_mul, mul_one]
              field_simp
              ring
            have hdet0 : LinearMap.det T ≠ 0 := by rw [hdet]; positivity
            have hTs : Function.Surjective T := ((Module.End.isUnit_iff T).1
              ((LinearMap.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet0))).2
            -- `G ∘ T` is `2δ`-Lipschitz on `T⁻¹(s ∩ t j)`.
            have hLip : LipschitzOnWith (2 * δ).toNNReal (G ∘ T) (T ⁻¹' (s ∩ t j)) := by
              refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
              rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
              have h1 : ‖G (T z) - G (T z') - A j (T z - T z')‖ ≤ δ * ‖T z - T z'‖ :=
                hA j (T z) hz (T z') hz'
              have h2 : ‖A j (T z - T z')‖ ≤ δ * ‖z - z'‖ := by
                rw [← map_sub, hAT, norm_smul, Real.norm_of_nonneg ha0.le]
                calc a * ‖A j (z - z')‖ ≤ a * (L * ‖z - z'‖) := by
                      gcongr
                      exact ((A j).le_opNorm _).trans (by gcongr; linarith)
                  _ = δ * ‖z - z'‖ := by rw [ha]; field_simp
              have h3 : ‖T z - T z'‖ ≤ ‖z - z'‖ := by rw [← map_sub]; exact hTn _
              calc ‖(G ∘ T) z - (G ∘ T) z'‖
                  = ‖(G (T z) - G (T z') - A j (T z - T z')) + A j (T z - T z')‖ := by
                    rw [sub_add_cancel]; rfl
                _ ≤ ‖G (T z) - G (T z') - A j (T z - T z')‖ + ‖A j (T z - T z')‖ :=
                    norm_add_le _ _
                _ ≤ δ * ‖z - z'‖ + δ * ‖z - z'‖ := by
                    gcongr
                    exact h1.trans (by gcongr)
                _ = 2 * δ * ‖z - z'‖ := by ring
            -- `Hⁿ(G(s ∩ t j)) ≤ (2δ)ⁿ |T⁻¹(s ∩ t j)| = (2δ)ⁿ a¹⁻ⁿ |s ∩ t j| = 2ⁿ ε L⁻¹ |s ∩ t j|`.
            calc (μHE[n] : Measure (Eucl P)) (G '' (s ∩ t j))
                = (μHE[n] : Measure (Eucl P)) ((G ∘ T) '' (T ⁻¹' (s ∩ t j))) := by
                  rw [image_comp, image_preimage_eq _ hTs]
              _ ≤ ((2 * δ).toNNReal : ℝ≥0∞) ^ n *
                    (μHE[n] : Measure (Eucl n)) (T ⁻¹' (s ∩ t j)) :=
                  Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
                    n hLip
              _ = ENNReal.ofReal ((2 * δ) ^ n * (a / a ^ n)) * volume (s ∩ t j) := by
                  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
                    Measure.addHaar_preimage_linearMap volume hdet0, hdet, inv_div,
                    abs_of_pos (by positivity), ← mul_assoc, ENNReal.ofReal_mul (by positivity),
                    ENNReal.ofReal_pow (by positivity)]
                  rfl
              _ ≤ ENNReal.ofReal (2 ^ n * ε) * volume (s ∩ t j) := by
                  gcongr ENNReal.ofReal ?_ * _
                  have hδa : δ = a * L := by rw [ha]; field_simp
                  have hεδ : ε = δ * L ^ n := by rw [hδ]; field_simp
                  have hval : (2 * δ) ^ n * (a / a ^ n) = 2 ^ n * ε / L := by
                    rw [hεδ, hδa, mul_pow, mul_pow]
                    field_simp
                  rw [hval]
                  exact div_le_self (by positivity) hL1
          calc (μHE[n] : Measure (Eucl P)) (G '' s)
              ≤ (μHE[n] : Measure (Eucl P)) (⋃ j, G '' (s ∩ t j)) := by
                refine measure_mono ?_
                rw [← image_iUnion, ← inter_iUnion]
                exact image_mono (subset_inter subset_rfl hst)
            _ ≤ ∑' j, (μHE[n] : Measure (Eucl P)) (G '' (s ∩ t j)) := measure_iUnion_le _
            _ ≤ ∑' j, ENNReal.ofReal (2 ^ n * ε) * volume (s ∩ t j) :=
                ENNReal.tsum_le_tsum hpiece
            _ = ENNReal.ofReal (2 ^ n * ε) * ∑' j, (volume.restrict s) (t j) := by
                rw [ENNReal.tsum_mul_left]
                congr 1
                refine tsum_congr fun j => ?_
                rw [Measure.restrict_apply (htm j), inter_comm]
            _ = ENNReal.ofReal (2 ^ n * ε) * (volume.restrict s) (⋃ j, t j) := by
                rw [measure_iUnion htd htm]
            _ ≤ ENNReal.ofReal (2 ^ n * ε) * volume s := by
                gcongr _ * ?_
                exact (measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ s)
        -- Let `ε → 0`.
        refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) zero_le
        rw [zero_add]
        have hη' : (0 : ℝ) < η := NNReal.coe_pos.2 hη
        have hV0 : 0 ≤ (volume s).toReal := ENNReal.toReal_nonneg
        have hV1 : 0 < (volume s).toReal + 1 := by linarith
        obtain ⟨ε, hε, hε1, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
            2 ^ n * ε * (volume s).toReal ≤ η := by
          refine ⟨min 1 (η / (2 ^ n * ((volume s).toReal + 1))), lt_min one_pos (by positivity),
            min_le_left _ _, ?_⟩
          calc 2 ^ n * min 1 (η / (2 ^ n * ((volume s).toReal + 1))) * (volume s).toReal
              ≤ 2 ^ n * (η / (2 ^ n * ((volume s).toReal + 1))) * ((volume s).toReal + 1) := by
                gcongr
                · exact min_le_right _ _
                · linarith
            _ = η := by field_simp
        calc (μHE[n] : Measure (Eucl P)) (G '' s) ≤ ENNReal.ofReal (2 ^ n * ε) * volume s :=
              hkey ε hε hε1
          _ = ENNReal.ofReal (2 ^ n * ε * (volume s).toReal) := by
              rw [ENNReal.ofReal_mul' hV0, ENNReal.ofReal_toReal hsfin]
          _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεη
          _ = η := ENNReal.ofReal_coe_nnreal
      refine measure_mono_null ?_ (measure_iUnion_null hR)
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨R, hRx⟩ := exists_nat_gt ‖x‖
      exact mem_iUnion.2 ⟨R, x, ⟨hx, mem_ball_zero_iff.2 hRx⟩, rfl⟩
    refine measure_mono_null ?_ hcrit
    rintro y ⟨⟨w, rfl⟩, hy⟩
    refine ⟨w, fun hinj => ?_, rfl⟩
    obtain ⟨k, hk⟩ := hreg w hinj
    exact hy (mem_iUnion.2 ⟨k, w, hk, rfl⟩)

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
