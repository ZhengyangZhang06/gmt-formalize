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

/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Z) < ∞` and `|η(x)| ≤ c` everywhere (Euclidean
coefficient norm) with `c > 0`, then `|Z(η)| ≤ c · M(Z)`. -/
theorem Submission.fiw_tb_te_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U n) (η : TestFormOn U n) (c : ℝ),
      0 < c → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ c) →
      Z.mass ≠ ∞ → |Z η| ≤ c * Z.mass.toReal := by
  intro P n U Z η c hc hη hZ
  -- Homogeneity of the Euclidean coefficient norm: `|t β| = |t| |β|`.
  have hsmul : ∀ (t : ℝ) (β : Covector (Eucl P) n),
      covectorEuclideanNorm (t • β) = |t| * covectorEuclideanNorm β := by
    intro t β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- If `|θ| ≤ c` pointwise, then `c⁻¹ θ` is mass-admissible, hence `Z(θ) ≤ c · M(Z)`.
  have hone : ∀ θ : TestFormOn U n,
      (∀ x, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) n) x) ≤ c) →
        Z θ ≤ c * Z.mass.toReal := by
    intro θ hθ
    have hadm : c⁻¹ • θ ∈ massAdmissibleOn U n U := by
      refine ⟨(c⁻¹ • θ).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (c⁻¹ • (θ : DifferentialForm (Eucl P) n) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ hc, mul_one]
      exact hθ x
    have hle : ENNReal.ofReal (Z (c⁻¹ • θ)) ≤ Z.mass := Z.le_massOn hadm
    rwa [ENNReal.ofReal_le_iff_le_toReal hZ, map_smul, smul_eq_mul, inv_mul_le_iff₀ hc] at hle
  -- Apply this to `η` and to `-η`, using `|-η(x)| = |η(x)|` and `Z(-η) = -Z(η)`.
  have hneg := hone (-η) fun x => by
    change covectorEuclideanNorm (-(η : DifferentialForm (Eucl P) n) x) ≤ c
    rw [covectorEuclideanNorm_neg]
    exact hη x
  have hZneg : Z (-η) = -Z η := map_neg Z.toCurrent η
  rw [hZneg] at hneg
  exact abs_le.mpr ⟨by linarith, hone η hη⟩
/-- Simon Ch. 6, proof of 7.2 (translation estimate): for `φ ∈ C_c^∞(ℝⁿ)`, `n = m + 1`, and
`h ∈ ℝⁿ`, the test `m`-form `ω = φ α` with `α = ∑ₖ (-1)ᵏ hₖ dx⁽ᵏ⁾`, where `dx⁽ᵏ⁾` is the wedge of
the coordinate covectors `dxʲ`, `j ≠ k`, in increasing order (indices `0, …, m`), satisfies
`|ω(x)| = ‖h‖ |φ(x)|` and `dω(x)(e₀, …, eₘ) = ∑ᵢ hᵢ ∂ᵢφ(x) = Dφ(x) h`. -/
theorem Submission.fiw_tb_te_directional_form :
    ∀ (m : ℕ) (φ : Eucl (m + 1) → ℝ) (h : Eucl (m + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∃ ω : TestFormOn (univ : Set (Eucl (m + 1))) m,
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ ‖h‖ * |φ x|) ∧
        ∀ x, ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) m ω :
            TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1))
          x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h := by
  intro m φ h hφ hcs
  -- The coordinate `m`-covector omitting direction `k`, on the frame omitting `eᵢ`, is `δₖᵢ`.
  have hcoord : ∀ k i : Fin (m + 1),
      (wedgeCovectors m (fun a => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ)))
        (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = if k = i then 1 else 0 := by
    intro k i
    rw [wedgeCovectors_apply_det]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl]
      have hM : (Matrix.of fun a b => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ)
          (EuclideanSpace.single (k.succAbove b) (1 : ℝ))) = 1 := by
        ext a b
        simp [Matrix.one_apply]
      rw [hM, Matrix.det_one]
    · -- `i = k.succAbove a₀` for some `a₀`, and row `a₀` of the matrix vanishes.
      rw [ite_eq_right hki]
      obtain ⟨a₀, ha₀⟩ : i ∈ Set.range k.succAbove := by
        rw [Fin.range_succAbove]; exact Ne.symm hki
      apply Matrix.det_eq_zero_of_row_eq_zero a₀
      intro b
      simp [ha₀, (Fin.succAbove_ne i b).symm]
  -- The strictly increasing `I : Fin m → Fin (m + 1)` are exactly the maps `k.succAbove`.
  have hincr : ∀ I : Fin m → Fin (m + 1), StrictMono I → ∃ k : Fin (m + 1), I = k.succAbove := by
    intro I hI
    have hinj := hI.injective
    have hns : ¬ Function.Surjective I := by
      intro hs
      have := Fintype.card_le_of_surjective I hs
      simp at this
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨k, hk⟩ := hns
    refine ⟨k, ?_⟩
    have hsub : Set.range I ⊆ Set.range k.succAbove := by
      rw [Fin.range_succAbove]
      rintro _ ⟨a, rfl⟩
      exact hk a
    have hcard : (Set.range k.succAbove).ncard ≤ (Set.range I).ncard := by
      rw [Set.ncard_range_of_injective hinj,
        Set.ncard_range_of_injective Fin.succAbove_right_injective]
    have heq : Set.range I = Set.range k.succAbove := Set.eq_of_subset_of_ncard_le hsub hcard
    exact (StrictMono.range_inj_of_wellFoundedLT hI (Fin.strictMono_succAbove k)).1 heq
  -- The constant covector `α` with `α(e ∘ i.succAbove) = (-1)ⁱ hᵢ`.
  set α : Covector (Eucl (m + 1)) m := ∑ k : Fin (m + 1), ((-1 : ℝ) ^ (k : ℕ) * h k) •
    wedgeCovectors m (fun a => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ))
    with hα
  have hαe : ∀ i : Fin (m + 1),
      α (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = (-1 : ℝ) ^ (i : ℕ) * h i := by
    intro i
    simp only [hα, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hcoord, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  -- `ω₀ = φ α` is a test form on `univ`.
  set ω₀ : DifferentialForm (Eucl (m + 1)) m := fun y => φ y • α with hω₀
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω₀ := hφ.smul contDiff_const
  have hcs₀ : HasCompactSupport ω₀ := hcs.smul_right
  have hmem : ω₀ ∈ testFormOnSubmodule (univ : Set (Eucl (m + 1))) m :=
    ⟨⟨hsmooth, hcs₀⟩, subset_univ _⟩
  refine ⟨⟨ω₀, hmem⟩, ?_, ?_⟩
  · -- Norm: reindex the increasing multi-indices by `k ↦ k.succAbove`; then `|ω₀(x)| = |φ(x)| ‖h‖`.
    intro x
    apply le_of_eq
    change covectorEuclideanNorm (φ x • α) = ‖h‖ * |φ x|
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin m → Fin (m + 1),
        if StrictMono I then
          ((φ x • α) (fun i ↦ EuclideanSpace.basisFun (Fin (m + 1)) ℝ (I i))) ^ 2
        else 0) = ∑ k : Fin (m + 1), (φ x) ^ 2 * (h k) ^ 2 := by
      symm
      apply Fintype.sum_of_injective (fun k : Fin (m + 1) => k.succAbove)
        Fin.succAbove_left_injective
      · intro I hI
        rw [ite_eq_right]
        intro hmono
        obtain ⟨k, rfl⟩ := hincr I hmono
        exact hI ⟨k, rfl⟩
      · intro k
        simp only [Fin.strictMono_succAbove, ite_true, EuclideanSpace.basisFun_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        rw [hαe k, mul_pow, mul_pow, ← pow_mul, mul_comm (k : ℕ) 2, pow_mul]
        norm_num
    rw [hsum, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      EuclideanSpace.norm_eq, mul_comm]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.norm_eq_abs, sq_abs]
  · -- Exterior derivative: `dω₀(x)(e) = ∑ᵢ (-1)ⁱ (-1)ⁱ hᵢ Dφ(x) eᵢ = Dφ(x) h`.
    intro x
    change exteriorDerivative ω₀ x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h
    have hdiff : DifferentiableAt ℝ ω₀ x := (hsmooth.differentiable (by simp)).differentiableAt
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply hdiff]
    have key : ∀ i : Fin (m + 1),
        (fun y => ω₀ y (i.removeNth (fun j => EuclideanSpace.single j (1 : ℝ)))) =
          fun y => ((-1 : ℝ) ^ (i : ℕ) * h i) * φ y := by
      intro i
      funext y
      change (φ y • α) (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = _
      rw [ContinuousAlternatingMap.smul_apply, hαe i, smul_eq_mul, mul_comm]
    have hstep : ∀ i : Fin (m + 1),
        (-1 : ℤ) ^ (i : ℕ) • fderiv ℝ
            (fun y => ω₀ y (i.removeNth (fun j => EuclideanSpace.single j (1 : ℝ)))) x
            (EuclideanSpace.single i (1 : ℝ)) =
          h i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      intro i
      rw [key i, fderiv_const_mul hφd]
      simp only [smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, smul_eq_mul]
/-- Weak translation estimate: if `|∫ u · Dφ(h)| ≤ B` for every `C^∞` compactly supported `φ`
with `|φ| ≤ 1`, then `|∫ (u(· + h) − u) · g| ≤ B` for every such `g`.  For `φ_t = g(· − t h)`,
`F(t) = ∫ u(y) g(y − t h) dy` has `F'(t) = −∫ u(y) Dφ_t(y)(h) dy`, so `|F'| ≤ B`, and
`F(1) − F(0) = ∫ (u(x + h) − u(x)) g(x) dx` by translation invariance. -/
theorem Submission.fiw_tb_te_translation_dual :
    ∀ (n : ℕ) (u : Eucl n → ℝ) (h : Eucl n) (B : ℝ), Integrable u →
      (∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, |φ x| ≤ 1) → |∫ x, u x * fderiv ℝ φ x h| ≤ B) →
      ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        (∀ x, |g x| ≤ 1) → |∫ x, (u (x + h) - u x) * g x| ≤ B := by
  intro n u h B hu hB g hg hgc hg1
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- `Dg` is continuous with compact support, hence bounded.
  obtain ⟨K, hK⟩ := (hg.continuous_fderiv hn).bounded_above_of_compact_support (hgc.fderiv ℝ)
  have hcont : ∀ t : ℝ, Continuous fun y : Eucl n => g (y - t • h) := fun t =>
    hg.continuous.comp (continuous_id.sub continuous_const)
  have hcont' : ∀ t : ℝ, Continuous fun y : Eucl n => fderiv ℝ g (y - t • h) (-h) := fun t =>
    ((hg.continuous_fderiv hn).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const
  have hgle : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure (Eucl n)), ‖g (y - t • h)‖ ≤ 1 := fun t =>
    ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hg1 _
  -- Differentiation under the integral sign, dominated by `‖u‖ K ‖h‖`:
  -- `d/dt ∫ u(y) g(y - t h) dy = ∫ u(y) Dg(y - t h)(-h) dy`.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ∫ y, u y * g (y - s • h))
      (∫ y, u y * fderiv ℝ g (y - t • h) (-h)) t := by
    intro t
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
      (F := fun s y => u y * g (y - s • h)) (F' := fun s y => u y * fderiv ℝ g (y - s • h) (-h))
      (bound := fun y => ‖u y‖ * (K * ‖h‖)) Filter.univ_mem
      (Filter.Eventually.of_forall fun s => hu.aestronglyMeasurable.mul
        (hcont s).aestronglyMeasurable)
      (hu.mul_bdd (hcont t).aestronglyMeasurable (hgle t))
      (hu.aestronglyMeasurable.mul (hcont' t).aestronglyMeasurable)
      (ae_of_all _ fun y s _ => ?_) (hu.norm.mul_const _) (ae_of_all _ fun y s _ => ?_)).2
    · rw [norm_mul]
      gcongr
      calc ‖fderiv ℝ g (y - s • h) (-h)‖ ≤ K * ‖-h‖ :=
            (fderiv ℝ g (y - s • h)).le_of_opNorm_le (hK _) (-h)
        _ = K * ‖h‖ := by rw [norm_neg]
    · have hline : HasDerivAt (fun s : ℝ => y - s • h) (-h) s := by
        simpa using ((hasDerivAt_id s).smul_const h).const_sub y
      exact ((hg.differentiable hn (y - s • h)).hasFDerivAt.comp_hasDerivAt s hline).const_mul (u y)
  -- Each derivative is bounded by `B`: apply the hypothesis to `φ_t = g(· - t h)`.
  have hbound : ∀ t : ℝ, ‖∫ y, u y * fderiv ℝ g (y - t • h) (-h)‖ ≤ B := by
    intro t
    have hφ := hB (fun y => g (y - t • h)) (hg.comp (contDiff_id.sub contDiff_const))
      (hgc.comp_homeomorph (Homeomorph.subRight (t • h))) (fun y => hg1 _)
    simp only [fderiv_comp_sub] at hφ
    have heq : ∫ y, u y * fderiv ℝ g (y - t • h) (-h) = -∫ y, u y * fderiv ℝ g (y - t • h) h := by
      rw [← integral_neg]
      simp only [map_neg, mul_neg]
    rw [heq, norm_neg, Real.norm_eq_abs]
    exact hφ
  -- Mean value inequality on `[0, 1]`.
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => ∫ y, u y * g (y - s • h))
    (fun t _ => (hderiv t).hasDerivWithinAt) (fun t _ => hbound t)
  -- Identify the endpoints, using translation invariance of Lebesgue measure.
  have h1 : ∫ y, u y * g (y - (1 : ℝ) • h) = ∫ x, u (x + h) * g x := by
    rw [one_smul, ← integral_add_right_eq_self (μ := volume) (fun y => u y * g (y - h)) h]
    simp only [add_sub_cancel_right]
  have h0 : ∫ y, u y * g (y - (0 : ℝ) • h) = ∫ x, u x * g x := by
    simp only [zero_smul, sub_zero]
  have hint1 : Integrable fun x => u (x + h) * g x := by
    simpa using (hu.comp_add_right h).mul_bdd (hcont 0).aestronglyMeasurable (hgle 0)
  have hint0 : Integrable fun x => u x * g x := by
    simpa using hu.mul_bdd (hcont 0).aestronglyMeasurable (hgle 0)
  have hJ : ∫ x, (u (x + h) - u x) * g x = (∫ x, u (x + h) * g x) - ∫ x, u x * g x := by
    rw [← integral_sub hint1 hint0]
    simp only [sub_mul]
  rw [hJ, ← h1, ← h0, ← Real.norm_eq_abs]
  exact hmvt
/-- Smooth `±1` separation of two disjoint compact sets `K₁, K₂ ⊆ ℝ^n`: a `C^∞` function
`g : ℝ^n → ℝ` with compact support, `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`.
`Disjoint.exists_thickenings` gives `δ > 0` with disjoint open thickenings `Vᵢ ⊇ Kᵢ`; the smooth
Urysohn lemma `exists_contDiff_support_eq_eq_one_iff` gives `gᵢ : ℝ^n → [0, 1]` with
`support gᵢ = Vᵢ` and `gᵢ = 1` on `Kᵢ`, compactly supported since `closure Vᵢ ⊆ cthickening δ Kᵢ`.
At each point one of `g₁, g₂` vanishes, and `g = g₁ - g₂`. -/
theorem Submission.fiw_tb_te_l1d_smooth_sign_sep : ∀ (n : ℕ) (K₁ K₂ : Set (Eucl n)), IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ → ∃ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧ (∀ x, |g x| ≤ 1) ∧ (∀ x ∈ K₁, g x = 1) ∧ (∀ x ∈ K₂, g x = -1) := by
  intro n K₁ K₂ hK₁ hK₂ hd
  -- Steps 1–2: disjoint δ-thickenings `V₁ ⊇ K₁`, `V₂ ⊇ K₂`.
  obtain ⟨δ, hδ, hdδ⟩ := hd.exists_thickenings hK₁ hK₂.isClosed
  -- Step 3: smooth Urysohn functions `gᵢ : ℝ^n → [0, 1]`, `support gᵢ = Vᵢ`, `gᵢ = 1` on `Kᵢ`.
  obtain ⟨g₁, hg₁, hr₁, hs₁, he₁⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₁)) hK₁.isClosed (self_subset_thickening hδ K₁)
  obtain ⟨g₂, hg₂, hr₂, hs₂, he₂⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₂)) hK₂.isClosed (self_subset_thickening hδ K₂)
  -- Step 4: `tsupport gᵢ = closure Vᵢ ⊆ cthickening δ Kᵢ`, which is compact.
  have hc : ∀ (K : Set (Eucl n)) (f : Eucl n → ℝ), IsCompact K →
      Function.support f = thickening δ K → HasCompactSupport f := by
    intro K f hK hs
    refine (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport f) ?_
    rw [tsupport, hs]
    exact closure_thickening_subset_cthickening δ K
  have h01₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1 := fun x => hr₁ (mem_range_self x)
  have h01₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1 := fun x => hr₂ (mem_range_self x)
  -- Step 5: at every point one of `g₁, g₂` vanishes, since `V₁ ∩ V₂ = ∅`.
  have hdis : ∀ x, g₁ x = 0 ∨ g₂ x = 0 := by
    intro x
    by_contra h
    rw [not_or] at h
    have h1 : x ∈ Function.support g₁ := h.1
    have h2 : x ∈ Function.support g₂ := h.2
    rw [hs₁] at h1
    rw [hs₂] at h2
    exact Set.disjoint_left.mp hdδ h1 h2
  -- Steps 6–8: `g = g₁ - g₂`.
  refine ⟨g₁ - g₂, hg₁.sub hg₂, (hc K₁ g₁ hK₁ hs₁).sub (hc K₂ g₂ hK₂ hs₂), ?_, ?_, ?_⟩
  · intro x
    have a := h01₁ x
    have b := h01₂ x
    rw [Pi.sub_apply, abs_le]
    rcases hdis x with h | h <;> constructor <;> linarith
  · intro x hx
    have h1 : g₁ x = 1 := (he₁ x).1 hx
    have h2 : g₂ x = 0 := by
      rcases hdis x with h | h
      · rw [h1] at h; norm_num at h
      · exact h
    simp [h1, h2]
  · intro x hx
    have h2 : g₂ x = 1 := (he₂ x).1 hx
    have h1 : g₁ x = 0 := by
      rcases hdis x with h | h
      · exact h
      · rw [h2] at h; norm_num at h
    simp [h1, h2]
/-- Compact approximation of the sign of an integrable `w : ℝ^n → ℝ`: for `ε > 0` there are
disjoint compact sets `K₁, K₂` such that every a.e.-strongly measurable `g` with `|g| ≤ 1`,
`g = 1` on `K₁` and `g = -1` on `K₂` satisfies `∫ |w| < ∫ w g + ε`.
For a Borel representative `v` of `w`, the finite measure `ν = |v| dx` is inner regular, so there
are compact `K₁ ⊆ {v > 0}` and `K₂ ⊆ {v < 0}` with `ν({v > 0} \ K₁), ν({v < 0} \ K₂) < ε/4`.
Off `S = ({v > 0} \ K₁) ∪ ({v < 0} \ K₂)` we have `v g = |v|`, and on `S` we have `v g ≥ -|v|`,
so `∫ |v| ≤ ∫ v g + 2 ν(S) < ∫ v g + ε`. -/
theorem Submission.fiw_tb_te_l1d_compact_sign_approx : ∀ (n : ℕ) (w : Eucl n → ℝ), Integrable w → ∀ ε : ℝ, 0 < ε → ∃ K₁ K₂ : Set (Eucl n), IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧ ∀ g : Eucl n → ℝ, AEStronglyMeasurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ K₁, g x = 1) → (∀ x ∈ K₂, g x = -1) → (∫ x, |w x|) < (∫ x, w x * g x) + ε := by
  intro n w hw ε hε
  -- A Borel representative `v` of `w` and the finite measure `ν = |v| dx`.
  set v : Eucl n → ℝ := hw.aestronglyMeasurable.mk w with hv_def
  have hv_meas : StronglyMeasurable v := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hwv : w =ᵐ[volume] v := hw.aestronglyMeasurable.ae_eq_mk
  have hvi : Integrable v := hw.congr hwv
  set ν : Measure (Eucl n) := volume.withDensity (fun x => ENNReal.ofReal |v x|) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hvi.abs.hasFiniteIntegral
  -- Inner approximation of `{v > 0}` and `{v < 0}` by compact sets.
  set Ap : Set (Eucl n) := {x | 0 < v x} with hAp_def
  set Am : Set (Eucl n) := {x | v x < 0} with hAm_def
  have hAp : MeasurableSet Ap := measurableSet_lt measurable_const hv_meas.measurable
  have hAm : MeasurableSet Am := measurableSet_lt hv_meas.measurable measurable_const
  have hε4 : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨Kp, hKpA, hKp, hKpν⟩ := hAp.exists_isCompact_sdiff_lt (measure_ne_top ν Ap) hε4
  obtain ⟨Km, hKmA, hKm, hKmν⟩ := hAm.exists_isCompact_sdiff_lt (measure_ne_top ν Am) hε4
  have hdisj : Disjoint Kp Km := by
    rw [Set.disjoint_left]
    intro x hp hm
    have h1 : 0 < v x := hKpA hp
    have h2 : v x < 0 := hKmA hm
    linarith
  refine ⟨Kp, Km, hKp, hKm, hdisj, ?_⟩
  intro g hg hg1 hgp hgm
  -- The pointwise inequality `|v| - 2·1_S|v| ≤ v g`.
  set S : Set (Eucl n) := (Ap \ Kp) ∪ (Am \ Km) with hS_def
  have hS : MeasurableSet S := (hAp.diff hKp.measurableSet).union (hAm.diff hKm.measurableSet)
  have hpt : ∀ x, |v x| - 2 * S.indicator (fun y => |v y|) x ≤ v x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have h : |v x * g x| ≤ |v x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hg1 x)
      linarith [(abs_le.mp h).1]
    · rw [indicator_of_notMem hx]
      have hx' : (0 < v x → x ∈ Kp) ∧ (v x < 0 → x ∈ Km) := by
        constructor
        · intro h
          by_contra hK
          exact hx (Or.inl ⟨h, hK⟩)
        · intro h
          by_contra hK
          exact hx (Or.inr ⟨h, hK⟩)
      rcases lt_trichotomy (v x) 0 with h | h | h
      · rw [hgm x (hx'.2 h), abs_of_neg h]
        linarith
      · rw [h]
        simp
      · rw [hgp x (hx'.1 h), abs_of_pos h]
        linarith
  -- Integrate.
  have hvg : Integrable (fun x => v x * g x) :=
    hvi.mul_bdd hg (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg1 x)
  have hind : Integrable (fun x => S.indicator (fun y => |v y|) x) := hvi.abs.indicator hS
  have hlhs : Integrable (fun x => |v x| - 2 * S.indicator (fun y => |v y|) x) :=
    hvi.abs.sub (hind.const_mul 2)
  have hmono := integral_mono hlhs hvg hpt
  rw [integral_sub hvi.abs (hind.const_mul 2), integral_const_mul, integral_indicator hS] at hmono
  -- `∫_S |v| = (ν S).toReal < ε / 2`.
  have hνS : ν S = ∫⁻ x in S, ENNReal.ofReal |v x| := withDensity_apply _ hS
  have hSint : ∫ x in S, |v x| = (ν S).toReal := by
    rw [hνS, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _)
      hvi.abs.aestronglyMeasurable.restrict]
  have hνS_lt : ν S < ENNReal.ofReal (ε / 2) := by
    calc ν S ≤ ν (Ap \ Kp) + ν (Am \ Km) := measure_union_le _ _
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := ENNReal.add_lt_add hKpν hKmν
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
  have hSlt : ∫ x in S, |v x| < ε / 2 := by
    rw [hSint]
    exact ENNReal.toReal_lt_of_lt_ofReal hνS_lt
  -- Transfer back from `v` to `w`.
  have h1 : ∫ x, |w x| = ∫ x, |v x| := integral_congr_ae (hwv.fun_comp abs)
  have h2 : ∫ x, w x * g x = ∫ x, v x * g x :=
    integral_congr_ae (hwv.mono fun x hx => by simp only [hx])
  rw [h1, h2]
  linarith

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

/-- **`L¹` norm by duality with smooth test functions** (proof of the translation estimate,
Step 4).  If `w : ℝⁿ → ℝ` is integrable and `∫ w g ≤ C` for every `C^∞` compactly supported `g`
with `|g| ≤ 1`, then `∫ |w| ≤ C`.  Given `ε > 0`, inner regularity of the finite measure `|w| dx`
gives disjoint compact sets `K₁, K₂`, approximating `{w > 0}` and `{w < 0}`, such that
`∫ |w| < ∫ w g + ε` for every measurable `g` with `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`.
Smooth Urysohn functions on disjoint thickenings of `K₁, K₂` give such a `g ∈ C_c^∞`, so
`∫ |w| < C + ε`. -/
theorem Submission.fiw_tb_te_l1_le_of_smooth_dual : ∀ (n : ℕ) (w : Eucl n → ℝ) (C : ℝ), Integrable w → (∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → (∀ x, |g x| ≤ 1) → ∫ x, w x * g x ≤ C) → ∫ x, |w x| ≤ C := by
  intro n w C hw H
  -- Step 8: it suffices that `∫ |w| < C + ε` for every `ε > 0`.
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- Steps 1, 2, 6, 7: compact `K₁, K₂` on which a `±1`-valued `g` nearly attains `∫ |w|`.
  obtain ⟨K₁, K₂, hK₁, hK₂, hd, hB⟩ := Submission.fiw_tb_te_l1d_compact_sign_approx n w hw ε hε
  -- Steps 3–5: a `C^∞` compactly supported `g` with `|g| ≤ 1`, `g = 1` on `K₁`, `g = -1` on `K₂`.
  obtain ⟨g, hg, hgc, hg1, hgK₁, hgK₂⟩ :=
    Submission.fiw_tb_te_l1d_smooth_sign_sep n K₁ K₂ hK₁ hK₂ hd
  -- `g` is continuous, hence a.e.-strongly measurable: `∫ |w| < ∫ w g + ε ≤ C + ε`.
  have h1 := hB g hg.continuous.aestronglyMeasurable hg1 hgK₁ hgK₂
  have h2 := H g hg hgc hg1
  linarith

end GMT.Ch06
