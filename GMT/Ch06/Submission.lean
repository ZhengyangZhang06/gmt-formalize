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

/-- Simon Ch. 6, Lemma 5.4, proof p. 163 ("by (7), (8) and the chain rule"), pointwise form:
if `f` is `K₁`-Lipschitz at `x` within `A`, `f` maps `A` into `B`, and `g` is `K₂`-Lipschitz at
`f x` within `B`, then `g ∘ f` is `K₁ K₂`-Lipschitz at `x` within `A`.  With
`η = min{1, ε/(K₁ + K₂ + 1)}` and `δ = min{δ₁, δ₂/(K₁ + η)}` one gets
`(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + ε`. -/
theorem Submission.dr_cc_lip_at_comp : ∀ (X Y Z : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z] (f : X → Y) (g : Y → Z) (A : Set X) (B : Set Y) (x : X) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ → MapsTo f A B → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (f x') (f x) ≤ (K₁ + ε) * dist x' x) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' (f x) < δ → dist (g y') (g (f x)) ≤ (K₂ + ε) * dist y' (f x)) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (g (f x')) (g (f x)) ≤ (K₁ * K₂ + ε) * dist x' x := by
  intro X Y Z _ _ _ f g A B x K₁ K₂ hK₁ hK₂ hfAB hf hg ε hε
  -- The auxiliary level `η = min{1, ε/(K₁ + K₂ + 1)}`: `0 < η ≤ 1` and `η(K₁ + K₂ + 1) ≤ ε`.
  have hS : 0 < K₁ + K₂ + 1 := by linarith
  obtain ⟨η, hη, hη1, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η * (K₁ + K₂ + 1) ≤ ε :=
    ⟨min 1 (ε / (K₁ + K₂ + 1)), lt_min one_pos (div_pos hε hS), min_le_left _ _,
      (le_div_iff₀ hS).1 (min_le_right _ _)⟩
  -- `δ₁` for `f` and `δ₂` for `g` at level `η`; then `δ = min{δ₁, δ₂/(K₁ + η)}`.
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf η hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg η hη
  have hL : 0 < K₁ + η := by linarith
  refine ⟨min δ₁ (δ₂ / (K₁ + η)), lt_min hδ₁ (div_pos hδ₂ hL), fun x' hx' hd => ?_⟩
  -- `d(f x', f x) ≤ (K₁ + η) d(x', x) < δ₂`, and `f x' ∈ B`, so the bound for `g` applies.
  have hfx : dist (f x') (f x) ≤ (K₁ + η) * dist x' x := h₁ x' hx' (hd.trans_le (min_le_left _ _))
  have hd₂ : (K₁ + η) * dist x' x < δ₂ := by
    rw [← lt_div_iff₀' hL]
    exact hd.trans_le (min_le_right _ _)
  have hgx := h₂ (f x') (hfAB hx') (hfx.trans_lt hd₂)
  -- `(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + η(K₁ + K₂ + 1) ≤ K₁K₂ + ε`.
  have hη2 : η * (K₁ + K₂ + η) ≤ η * (K₁ + K₂ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  calc dist (g (f x')) (g (f x)) ≤ (K₂ + η) * dist (f x') (f x) := hgx
    _ ≤ (K₂ + η) * ((K₁ + η) * dist x' x) := mul_le_mul_of_nonneg_left hfx (by linarith)
    _ = (K₁ * K₂ + η * (K₁ + K₂ + η)) * dist x' x := by ring
    _ ≤ (K₁ * K₂ + ε) * dist x' x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
/-- Union rule for pointwise upper Lipschitz bounds (used for Simon Ch. 6, Lemma 5.4, p. 162,
where `y` may lie on several closed faces): if `g` is `K`-Lipschitz at `y` within `G k ∩ B` for
every closed piece `G k ∋ y`, and `B ⊆ ⋃ k, G k` with finitely many pieces, then `g` is
`K`-Lipschitz at `y` within `B`.  Pieces missing `y` stay a positive distance away from `y`, and
the minimum of finitely many radii is a common radius. -/
theorem Submission.dr_cc_lip_at_union : ∀ (X Y : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] (ι : Type) [Finite ι] (G : ι → Set X) (B : Set X) (g : X → Y) (y : X) (K : ℝ), (∀ k, IsClosed (G k)) → B ⊆ ⋃ k, G k → (∀ k, y ∈ G k → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ G k ∩ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y := by
  intro X Y _ _ ι _ G B g y K hG hB hloc ε hε
  -- A radius `r k > 0` for each piece: from the hypothesis if `y ∈ G k`, and otherwise a ball
  -- around `y` missing the closed set `G k` (the bound then holds vacuously).
  have hr : ∀ k, ∃ r : ℝ, 0 < r ∧
      ∀ y' ∈ G k ∩ B, dist y' y < r → dist (g y') (g y) ≤ (K + ε) * dist y' y := by
    intro k
    by_cases hyk : y ∈ G k
    · exact hloc k hyk ε hε
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hG k).isOpen_compl y hyk
      exact ⟨r, hr, fun y' hy' hdist => absurd hy'.1 (hball (Metric.mem_ball.2 hdist))⟩
  choose r hr0 hrb using hr
  -- A common radius `δ ≤ r k`: the minimum over the finite index type (`1` if `ι` is empty).
  obtain ⟨δ, hδ, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ r k := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun k => isEmptyElim k⟩
    · obtain ⟨k₀, hk₀⟩ := Finite.exists_min r
      exact ⟨r k₀, hr0 k₀, hk₀⟩
  -- A point `y' ∈ B` lies in some piece `G k`, and `dist y' y < δ ≤ r k`.
  refine ⟨δ, hδ, fun y' hy' hdist => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hB hy')
  exact hrb k y' ⟨hk, hy'⟩ (hdist.trans_le (hδr k))
/-- Simon Ch. 6, Lemma 5.4, proof p. 161, displays (1) and (2): elementary facts on the dual
skeleton `La = {y : y_i − a_i ∈ ℤ for m + 2 indices i}` of a point `a ∈ (1/4, 3/4)^d`.
`La` is a finite union of finite intersections of the closed sets `{y : y_i − a_i ∈ ℤ}`, hence
closed; a point agreeing with `a` on `m + 2` coordinates lies in `La`; and if `y ∈ La ∩ [0,1]^d`
lies on the ray from the centre `c` of a face of `[0,1]^d` (free coordinates `J`) through `x`,
then each witness coordinate `i` of `y` has `y_i − a_i ∈ (−1, 1) ∩ ℤ = {0}`, so `i ∈ J` (else
`a_i = y_i = c_i ∈ {0, 1}`) and `x_i = a_i` as `s > 0`. -/
theorem Submission.dr_cc_skeleton_facts :
    ∀ (m ℓ : ℕ) (a : Eucl (m + 1 + ℓ)), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → IsClosed La ∧ (∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)), m + 2 ≤ J.card → (∀ i ∈ J, c i = a i) → c ∈ La) ∧ ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s → (∀ i, y i - c i = s * (x i - c i)) → y ∈ La → x ∈ La := by
  intro m ℓ a ha La hLa
  refine ⟨?_, ?_, ?_⟩
  · -- `La = ⋃_{|J| = m+2} ⋂_{i ∈ J} {y : y_i − a_i ∈ ℤ}`, a finite union of closed sets.
    have hLa' : La = ⋃ J ∈ {J : Finset (Fin (m + 1 + ℓ)) | J.card = m + 2},
        ⋂ i ∈ J, (fun y : Eucl (m + 1 + ℓ) => y i - a i) ⁻¹' range ((↑) : ℤ → ℝ) := by
      rw [hLa]
      ext y
      simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_preimage, mem_range, exists_prop]
      exact exists_congr fun J => and_congr_right fun _ =>
        forall₂_congr fun i _ => exists_congr fun k => eq_comm
    rw [hLa']
    refine (toFinite _).isClosed_biUnion fun J _ => isClosed_biInter fun i _ => ?_
    exact Real.isClosed_range_intCast.preimage (by fun_prop)
  · -- Face centres: any `m + 2` of the coordinates where `c = a` witness `c ∈ La`.
    intro J c hJ hc
    obtain ⟨J', hJ'J, hJ'⟩ := Finset.exists_subset_card_eq hJ
    rw [hLa]
    exact ⟨J', hJ', fun i hi => ⟨0, by rw [hc i (hJ'J hi), sub_self, Int.cast_zero]⟩⟩
  · -- Cone property: every witness coordinate of `y` is free and has `x_i = y_i = a_i`.
    intro J c x y s hcJ hc01 hxc hy hs hyx hyLa
    rw [hLa] at hyLa ⊢
    obtain ⟨J', hJ', hyJ'⟩ := hyLa
    refine ⟨J', hJ', fun i hi => ⟨0, ?_⟩⟩
    obtain ⟨k, hk⟩ := hyJ' i hi
    obtain ⟨ha1, ha2⟩ := ha i
    obtain ⟨hy0, hy1⟩ := hy i
    -- `y_i − a_i ∈ (−1, 1)` is an integer, hence `0`.
    have hk0 : k = 0 := by
      have h1 : (-1 : ℝ) < k := by linarith
      have h2 : (k : ℝ) < 1 := by linarith
      have h1' : -1 < k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    rw [hk0, Int.cast_zero] at hk
    rw [Int.cast_zero]
    have h := hyx i
    by_cases hiJ : i ∈ J
    · rw [hcJ i hiJ, hk] at h
      exact (mul_eq_zero.1 h.symm).resolve_left hs.ne'
    · -- A fixed coordinate would give `a_i = y_i = c_i ∈ {0, 1}`.
      rw [hxc i hiJ, sub_self, mul_zero] at h
      rcases hc01 i hiJ with h0 | h0 <;> linarith
/-- Simon Ch. 6, Lemma 5.4, displays (4)–(7) (corrected similarity bound): if `y ∈ [0,1]^d` lies
on the ray `y = c + s(x - c)` from a face centre `c` (with `c_i = a_i` on `J`, `c_i ∈ {0,1}`
and `x_i = c_i` off `J`), then `min{1/4, s·dist(x, La)} ≤ dist(y, La)`.  A point `w ∈ La` either
has a witness coordinate where `y_i ∈ [0,1]` is `1/4`-far from `a_i + ℤ`, or all its witness
coordinates are free with zero shift, and then `w' = c + s⁻¹(w - c) ∈ La` and
`y - w = s(x - w')`. -/
theorem Submission.dr_cc_similarity_bound : ∀ (m ℓ : ℕ) (a : Eucl (m + 1 + ℓ)), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s → (∀ i, y i - c i = s * (x i - c i)) → min (1 / 4) (s * infDist x La) ≤ infDist y La := by
  intro m ℓ a ha La hLa J c x y s hcJ hcJc hxJc hy hs hrel
  -- `La = ∅` is trivial; otherwise it suffices to bound `dist y w` for each `w ∈ La`.
  rcases La.eq_empty_or_nonempty with hE | hne
  · simp [hE]
  rw [Metric.le_infDist hne]
  intro w hw
  -- The witness set `J'` (of `m + 2` indices) and the integers `k_i` for `w ∈ La`.
  rw [hLa, Set.mem_ofPred_eq] at hw
  obtain ⟨J', hJ'card, hJ'⟩ := hw
  -- `|y_i - w_i| ≤ |y - w|`, so a coordinate gap of `1/4` gives the bound.
  have hcoord : ∀ i, 1 / 4 ≤ |y i - w i| → min (1 / 4) (s * infDist x La) ≤ dist y w := by
    intro i hi
    have hi' := PiLp.dist_apply_le y w i
    rw [Real.dist_eq] at hi'
    exact (min_le_left _ _).trans (hi.trans hi')
  by_cases h1 : ∃ i ∈ J', i ∉ J
  · -- Case 1: a witness index `i ∉ J`, where `y_i = c_i ∈ {0, 1}`.
    obtain ⟨i, hiJ', hiJ⟩ := h1
    obtain ⟨k, hk⟩ := hJ' i hiJ'
    obtain ⟨ha1, ha2⟩ := ha i
    have hyi : y i = c i := by
      have hri := hrel i
      rw [hxJc i hiJ, sub_self, mul_zero, sub_eq_zero] at hri
      exact hri
    refine hcoord i ?_
    rcases hcJc i hiJ with hc | hc
    · have hk' : (k : ℝ) ≤ -1 ∨ (0 : ℝ) ≤ k := by
        rcases le_or_gt 0 k with h | h
        · right; exact_mod_cast h
        · left; exact_mod_cast (show k ≤ -1 by omega)
      rcases hk' with hk1 | hk1
      · exact (show (1 : ℝ) / 4 ≤ y i - w i by linarith).trans (le_abs_self _)
      · exact (show (1 : ℝ) / 4 ≤ -(y i - w i) by linarith).trans (neg_le_abs _)
    · have hk' : (k : ℝ) ≤ 0 ∨ (1 : ℝ) ≤ k := by
        rcases le_or_gt 1 k with h | h
        · right; exact_mod_cast h
        · left; exact_mod_cast (show k ≤ 0 by omega)
      rcases hk' with hk1 | hk1
      · exact (show (1 : ℝ) / 4 ≤ y i - w i by linarith).trans (le_abs_self _)
      · exact (show (1 : ℝ) / 4 ≤ -(y i - w i) by linarith).trans (neg_le_abs _)
  push Not at h1
  by_cases h2 : ∃ i ∈ J', w i ≠ a i
  · -- Case 2: a nonzero shift `k_i` at a witness index, where `y_i ∈ [0, 1]`.
    obtain ⟨i, hiJ', hwi⟩ := h2
    obtain ⟨k, hk⟩ := hJ' i hiJ'
    obtain ⟨ha1, ha2⟩ := ha i
    obtain ⟨hy0, hy1⟩ := hy i
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Int.cast_zero, sub_eq_zero] at hk
      exact hwi hk
    have hk' : (k : ℝ) ≤ -1 ∨ (1 : ℝ) ≤ k := by
      rcases le_or_gt 1 k with h | h
      · right; exact_mod_cast h
      · left; exact_mod_cast (show k ≤ -1 by omega)
    refine hcoord i ?_
    rcases hk' with hk1 | hk1
    · exact (show (1 : ℝ) / 4 ≤ y i - w i by linarith).trans (le_abs_self _)
    · exact (show (1 : ℝ) / 4 ≤ -(y i - w i) by linarith).trans (neg_le_abs _)
  -- Case 3: all witness indices lie in `J` with zero shifts; `w' = c + s⁻¹(w - c) ∈ La`.
  push Not at h2
  have hw' : c + s⁻¹ • (w - c) ∈ La := by
    rw [hLa, Set.mem_ofPred_eq]
    refine ⟨J', hJ'card, fun i hi => ⟨0, ?_⟩⟩
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, h2 i hi,
      hcJ i (h1 i hi), sub_self, mul_zero, add_zero, Int.cast_zero]
  have hyw : y - w = s • (x - (c + s⁻¹ • (w - c))) := by
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    calc y i - w i = (y i - c i) - (w i - c i) := by ring
      _ = s * (x i - c i) - s * s⁻¹ * (w i - c i) := by rw [hrel i, mul_inv_cancel₀ hs.ne', one_mul]
      _ = s * (x i - (c i + s⁻¹ * (w i - c i))) := by ring
  have hdist : dist y w = s * dist x (c + s⁻¹ • (w - c)) := by
    rw [dist_eq_norm, dist_eq_norm, hyw, norm_smul, Real.norm_of_nonneg hs.le]
  rw [hdist]
  exact (min_le_right _ _).trans
    (mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem hw') hs.le)
/-- Simon Ch. 6, proof of Lemma 5.4: the radial retraction `ψ_F` with origin `c` (p. 161) of
`F = {x ∈ [0,1]^D : xᵢ = cᵢ (i ∉ J)}` onto its relative boundary, with its pointwise Lipschitz
bound (printed (8), p. 163).  Here `g(x) = c + N(x - c)⁻¹ • (x - c)` for the gauge
`N(v) = max_{i ∈ J} max (vᵢ/(1 - aᵢ)) (-vᵢ/aᵢ)`, and `s = N(x - c)⁻¹`. -/
theorem Submission.dr_cc_radial_map : ∀ (D : ℕ) (a : Eucl D), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ (J : Finset (Fin D)) (c : Eucl D), (∀ i ∈ J, c i = a i) → ∃ g : Eucl D → Eucl D, ∀ x : Eucl D, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i ∉ J, x i = c i) → x ≠ c → (∀ i, 0 ≤ g x i ∧ g x i ≤ 1) ∧ (∃ i ∈ J, g x i = 0 ∨ g x i = 1) ∧ ∃ s : ℝ, 0 < s ∧ (∀ i, g x i - c i = s * (x i - c i)) ∧ s * dist x c ≤ Real.sqrt (D : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl D, (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) → dist x' x < δ → dist (g x') (g x) ≤ ((1 + 4 * Real.sqrt (D : ℝ)) * s + ε) * dist x' x := by
  intro D a ha J c hcJ
  -- Step 1: for `J = ∅` the face is `{c}`, so no `x` is admissible.
  rcases J.eq_empty_or_nonempty with hJ | hJ
  · refine ⟨id, fun x _ hxJ hxc => absurd ?_ hxc⟩
    ext i
    exact hxJ i (by simp [hJ])
  -- Step 0: `aᵢ, 1 - aᵢ > 1/4`, coordinates are bounded by the norm, `diam [0,1]^D ≤ √D`.
  have ha0 : ∀ i, 0 < a i := fun i => by linarith [(ha i).1]
  have ha1 : ∀ i, 0 < 1 - a i := fun i => by linarith [(ha i).2]
  have hcoord : ∀ (v : Eucl D) (i : Fin D), |v i| ≤ ‖v‖ := by
    intro v i
    have h := PiLp.norm_apply_le v i
    rwa [Real.norm_eq_abs] at h
  have hdiam : ∀ p q : Eucl D, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → (∀ i, 0 ≤ q i ∧ q i ≤ 1) →
      dist p q ≤ Real.sqrt D := by
    intro p q hp hq
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (p i) (q i) ^ 2 ≤ ∑ _i : Fin D, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : 0 ≤ 1 - p i + q i := by linarith [(hp i).2, (hq i).1]
          have h2 : 0 ≤ 1 + p i - q i := by linarith [(hp i).1, (hq i).2]
          rw [Real.dist_eq, sq_abs]
          nlinarith [mul_nonneg h1 h2]
      _ = D := by simp
  -- Step 2: the gauge `N(v) = max_{i ∈ J} fᵢ(v)`, `fᵢ(v) = max (vᵢ/(1 - aᵢ)) (-vᵢ/aᵢ)`.
  obtain ⟨f, hf⟩ : ∃ f : Eucl D → Fin D → ℝ,
      ∀ v i, f v i = max (v i / (1 - a i)) (-v i / a i) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Eucl D → ℝ, ∀ v, N v = J.sup' hJ (f v) := ⟨_, fun _ => rfl⟩
  have hfN : ∀ v, ∀ i ∈ J, f v i ≤ N v := by
    intro v i hi
    rw [hN]
    exact Finset.le_sup' (f v) hi
  have hNatt : ∀ v, ∃ i ∈ J, N v = f v i := by
    intro v
    obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup' hJ (f v)
    exact ⟨i, hi, (hN v).trans h⟩
  -- (N2): each `fᵢ`, hence `N`, is `4`-Lipschitz.
  have hfLip : ∀ v w : Eucl D, ∀ i, f w i ≤ f v i + 4 * ‖w - v‖ := by
    intro v w i
    have hwv : |w i - v i| ≤ ‖w - v‖ := hcoord (w - v) i
    have e1 : |w i / (1 - a i) - v i / (1 - a i)| ≤ 4 * |w i - v i| := by
      rw [← sub_div, abs_div, abs_of_pos (ha1 i), div_le_iff₀ (ha1 i)]
      nlinarith [abs_nonneg (w i - v i), (ha i).2]
    have e2 : |-w i / a i - -v i / a i| ≤ 4 * |w i - v i| := by
      rw [← sub_div, abs_div, abs_of_pos (ha0 i), div_le_iff₀ (ha0 i), neg_sub_neg,
        abs_sub_comm (v i) (w i)]
      nlinarith [abs_nonneg (w i - v i), (ha i).1]
    have e3 := (abs_le.mp (abs_max_sub_max_le_max (w i / (1 - a i)) (-w i / a i)
      (v i / (1 - a i)) (-v i / a i))).2
    have e4 := max_le e1 e2
    rw [hf, hf]
    linarith
  have hNle : ∀ v w : Eucl D, N w ≤ N v + 4 * ‖w - v‖ := by
    intro v w
    rw [hN w]
    exact Finset.sup'_le hJ (f w) fun i hi => (hfLip v w i).trans (by linarith [hfN v i hi])
  have hNlip : ∀ v w : Eucl D, |N w - N v| ≤ 4 * ‖w - v‖ := by
    intro v w
    rw [abs_le]
    constructor
    · have h := hNle w v
      rw [norm_sub_rev] at h
      linarith
    · linarith [hNle v w]
  -- Step 8 (core): the estimate `|u w - t v| ≤ ((1 + 4√D) t + ε) |w - v|` for `t = N(v)⁻¹`,
  -- `u = N(w)⁻¹`, written with `W = w - v`, `V = v`, `ν = N(v)`, `μ = N(w)`, `ρ = |w - v|`.
  have key : ∀ (ν μ ρ ε : ℝ) (V W : Eucl D), 0 < ν → ‖W‖ = ρ → |μ - ν| ≤ 4 * ρ →
      ν⁻¹ * ‖V‖ ≤ Real.sqrt D → ρ < ν / 8 → ρ < ε * ν ^ 2 / (8 * (1 + 4 * Real.sqrt D)) →
      ‖μ⁻¹ • W + (μ⁻¹ - ν⁻¹) • V‖ ≤ ((1 + 4 * Real.sqrt D) * ν⁻¹ + ε) * ρ := by
    intro ν μ ρ ε V W hν hW hμν hV hρ1 hρ2
    have hβ : 0 < 1 + 4 * Real.sqrt D := by positivity
    have hρ0 : 0 ≤ ρ := hW ▸ norm_nonneg W
    have hμ : ν / 2 < μ := by linarith [(abs_le.mp hμν).1]
    have hμ0 : 0 < μ := by linarith
    have ht : 0 < ν⁻¹ := inv_pos.mpr hν
    have hu : 0 < μ⁻¹ := inv_pos.mpr hμ0
    have htν : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν.ne'
    have huμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0.ne'
    generalize ν⁻¹ = t at ht htν hV ⊢
    generalize μ⁻¹ = u at hu huμ ⊢
    -- (b): `u - t = u t (ν - μ)`, so `|u - t| ≤ 4 u t ρ`; and `u < 2 t`.
    have hut : u - t = u * t * (ν - μ) := by linear_combination (-u) * htν + t * huμ
    have habs : |u - t| ≤ 4 * u * t * ρ := by
      rw [hut, abs_mul, abs_of_pos (mul_pos hu ht), abs_sub_comm ν μ]
      have h := mul_le_mul_of_nonneg_left hμν (mul_pos hu ht).le
      linarith
    have hu2t : u < 2 * t := by
      have h1 : u * (μ * ν) = ν := by rw [← mul_assoc, huμ, one_mul]
      have h2 : 2 * t * (μ * ν) = 2 * μ := by
        have h : 2 * t * (μ * ν) = 2 * μ * (t * ν) := by ring
        rw [h, htν, mul_one]
      have h3 : u * (μ * ν) < 2 * t * (μ * ν) := by rw [h1, h2]; linarith
      exact lt_of_mul_lt_mul_right h3 (mul_pos hμ0 hν).le
    -- (d): `u ≤ t + 8 t² ρ` and `8 (1 + 4√D) t² ρ ≤ ε`.
    have hu_le : u ≤ t + 8 * t ^ 2 * ρ := by
      have h1 : u - t ≤ 4 * u * t * ρ := (le_abs_self _).trans habs
      have h2 := mul_le_mul_of_nonneg_right hu2t.le (by positivity : (0 : ℝ) ≤ 4 * t * ρ)
      nlinarith
    have h8 : 8 * (1 + 4 * Real.sqrt D) * t ^ 2 * ρ ≤ ε := by
      have h1 : ρ * (8 * (1 + 4 * Real.sqrt D)) < ε * ν ^ 2 := by
        rwa [lt_div_iff₀ (by positivity)] at hρ2
      calc 8 * (1 + 4 * Real.sqrt D) * t ^ 2 * ρ
          = t ^ 2 * (ρ * (8 * (1 + 4 * Real.sqrt D))) := by ring
        _ ≤ t ^ 2 * (ε * ν ^ 2) := mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = ε * (t * ν) ^ 2 := by ring
        _ = ε := by rw [htν, one_pow, mul_one]
    -- (a), (c), (e).
    calc ‖u • W + (u - t) • V‖ ≤ ‖u • W‖ + ‖(u - t) • V‖ := norm_add_le _ _
      _ = u * ρ + |u - t| * ‖V‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu, hW]
      _ ≤ u * ρ + 4 * u * t * ρ * ‖V‖ := by
          have h := mul_le_mul_of_nonneg_right habs (norm_nonneg V)
          linarith
      _ = u * ρ * (1 + 4 * (t * ‖V‖)) := by ring
      _ ≤ u * ρ * (1 + 4 * Real.sqrt D) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hu.le hρ0)
          linarith
      _ = (1 + 4 * Real.sqrt D) * u * ρ := by ring
      _ ≤ (1 + 4 * Real.sqrt D) * (t + 8 * t ^ 2 * ρ) * ρ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu_le hβ.le) hρ0
      _ = ((1 + 4 * Real.sqrt D) * t + 8 * (1 + 4 * Real.sqrt D) * t ^ 2 * ρ) * ρ := by ring
      _ ≤ ((1 + 4 * Real.sqrt D) * t + ε) * ρ := by
          refine mul_le_mul_of_nonneg_right ?_ hρ0
          linarith
  -- Step 3: the map `g(y) = c + N(y - c)⁻¹ (y - c)`.
  obtain ⟨g, hg⟩ : ∃ g : Eucl D → Eucl D, ∀ y, g y = c + (N (y - c))⁻¹ • (y - c) :=
    ⟨_, fun _ => rfl⟩
  have hgi : ∀ y i, g y i = c i + (N (y - c))⁻¹ * (y i - c i) := by
    intro y i
    rw [hg]
    rfl
  refine ⟨g, fun x hx hxJ hxc => ?_⟩
  -- Step 4: `ν = N(x - c) > 0` (N3); `s = ν⁻¹`.
  have hxc_i : ∀ i, (x - c) i = x i - c i := fun i => rfl
  have hν : 0 < N (x - c) := by
    by_contra hle
    rw [not_lt] at hle
    apply hxc
    ext i
    by_cases hi : i ∈ J
    · have h := (hfN (x - c) i hi).trans hle
      rw [hf, max_le_iff, div_le_iff₀ (ha1 i), div_le_iff₀ (ha0 i), zero_mul, zero_mul,
        hxc_i] at h
      linarith [h.1, h.2]
    · exact hxJ i hi
  -- Step 5: `g(x) ∈ [0,1]^D` (printed (R1)).
  have hgx_cube : ∀ i, 0 ≤ g x i ∧ g x i ≤ 1 := by
    intro i
    rw [hgi]
    by_cases hi : i ∈ J
    · have h := hfN (x - c) i hi
      rw [hf, max_le_iff, div_le_iff₀ (ha1 i), div_le_iff₀ (ha0 i), hxc_i] at h
      have k1 : (N (x - c))⁻¹ * (x i - c i) ≤ 1 - a i := by
        rw [inv_mul_le_iff₀ hν]
        exact h.1
      have k2 : -((N (x - c))⁻¹ * (x i - c i)) ≤ a i := by
        rw [← mul_neg, inv_mul_le_iff₀ hν]
        exact h.2
      constructor <;> linarith [hcJ i hi]
    · rw [← hxJ i hi, sub_self, mul_zero, add_zero]
      exact hx i
  -- Step 7: `s |x - c| = |g(x) - c| ≤ √D` (printed (R5)), as `c ∈ [0,1]^D`.
  have hc_cube : ∀ i, 0 ≤ c i ∧ c i ≤ 1 := by
    intro i
    by_cases hi : i ∈ J
    · rw [hcJ i hi]
      exact ⟨(ha0 i).le, by linarith [ha1 i]⟩
    · rw [← hxJ i hi]
      exact hx i
  have hR5 : (N (x - c))⁻¹ * ‖x - c‖ ≤ Real.sqrt D := by
    have h := hdiam (g x) c hgx_cube hc_cube
    rwa [hg, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hν)] at h
  refine ⟨hgx_cube, ?_, (N (x - c))⁻¹, inv_pos.mpr hν, fun i => by rw [hgi]; ring,
    by rw [dist_eq_norm]; exact hR5, ?_⟩
  · -- Step 6: a coordinate `i₀ ∈ J` realizing the maximum is sent to `0` or `1`.
    obtain ⟨i₀, hi₀, hmax⟩ := hNatt (x - c)
    refine ⟨i₀, hi₀, ?_⟩
    rw [hgi, hcJ i₀ hi₀]
    rw [hf, hxc_i, hcJ i₀ hi₀] at hmax
    rcases le_total (-(x i₀ - a i₀) / a i₀) ((x i₀ - a i₀) / (1 - a i₀)) with h | h
    · right
      rw [max_eq_left h] at hmax
      have e : x i₀ - a i₀ = N (x - c) * (1 - a i₀) := by
        rw [hmax, div_mul_cancel₀ _ (ha1 i₀).ne']
      rw [e, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      ring
    · left
      rw [max_eq_right h] at hmax
      have e : x i₀ - a i₀ = -(N (x - c) * a i₀) := by
        rw [hmax, div_mul_cancel₀ _ (ha0 i₀).ne', neg_neg]
      rw [e, mul_neg, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      ring
  · -- Step 8: the pointwise estimate (printed (8)), with `δ = min (ν/8) (εν²/(8(1 + 4√D)))`.
    intro ε hε
    refine ⟨min (N (x - c) / 8) (ε * N (x - c) ^ 2 / (8 * (1 + 4 * Real.sqrt D))),
      lt_min (by linarith) (div_pos (mul_pos hε (pow_pos hν 2)) (by positivity)), ?_⟩
    intro x' _ _ hx'
    have hid : g x' - g x = (N (x' - c))⁻¹ • ((x' - c) - (x - c)) +
        ((N (x' - c))⁻¹ - (N (x - c))⁻¹) • (x - c) := by
      rw [hg, hg]
      module
    have hwv : ‖(x' - c) - (x - c)‖ = dist x' x := by
      rw [sub_sub_sub_cancel_right, dist_eq_norm]
    have hμν : |N (x' - c) - N (x - c)| ≤ 4 * dist x' x := by
      have h := hNlip (x - c) (x' - c)
      rwa [hwv] at h
    rw [dist_eq_norm (g x') (g x), hid]
    exact key (N (x - c)) (N (x' - c)) (dist x' x) ε (x - c) ((x' - c) - (x - c)) hν hwv hμν hR5
      (hx'.trans_le (min_le_left _ _)) (hx'.trans_le (min_le_right _ _))

/-- Simon Ch. 6, Lemma 5.4, printed proof p. 161 (book `n = m + 1`), in the one-step form
`ψ₀ = R^ℓ`.  A point `y ∈ C ∖ La` whose carrier `J(y) = {i : 0 < yᵢ < 1}` has at least `m + 2`
elements is pushed radially from the centre `a_F` of its carrier face `F` onto `∂F`,
`R(y)ᵢ = aᵢ + (yᵢ - aᵢ) / N(y)` on `J(y)`, with the gauge
`N(y) = max_{i ∈ J(y)} max ((yᵢ - aᵢ) / (1 - aᵢ), (aᵢ - yᵢ) / aᵢ)`; `R` fixes every other point.
Each step stays in `C ∖ La` (cone property of `dr_cc_skeleton_facts`) and lowers `|J(y)|`, so
`R^ℓ` maps `C ∖ La` into the `(m+1)`-skeleton (α) and fixes the `(m+1)`-skeleton (S1); `R`
commutes with integer translations (β); and the exit point `y` of the ray from `a_F` through
`x ∈ F ∖ La` is `R(x)` or `x` itself (S2). -/
theorem Submission.dr_cc_construction :
    ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ a : Eucl (m + 1 + ℓ), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) →
      ∀ La : Set (Eucl (m + 1 + ℓ)),
        La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧
          ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} →
        ∃ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
          (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
            (∀ i, 0 ≤ ψ₀ x i ∧ ψ₀ x i ≤ 1) ∧
              ∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ψ₀ x i = 0 ∨ ψ₀ x i = 1) ∧
          (∀ x x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
            (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → (∀ i, ∃ k : ℤ, x' i - x i = k) →
              ∀ i, ψ₀ x' i - ψ₀ x i = x' i - x i) ∧
          (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
            (∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, x i = 0 ∨ x i = 1) →
              ψ₀ x = x) ∧
          ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), m + 2 ≤ J.card →
            (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
            x ∉ La → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s →
            (∀ i, y i - c i = s * (x i - c i)) → (∃ i ∈ J, y i = 0 ∨ y i = 1) → ψ₀ y = ψ₀ x := by
  intro m ℓ _ a ha La hLa
  classical
  -- Cone property: if `y ∈ C ∩ La` lies on the ray from the face centre `c` through `x`
  -- (`y - c = s • (x - c)`, `s > 0`), then `x ∈ La`.
  obtain ⟨-, -, hcone⟩ := Submission.dr_cc_skeleton_facts m ℓ a ha La hLa
  have ha1 : ∀ i, 0 < a i := fun i => by linarith [(ha i).1]
  have ha2 : ∀ i, 0 < 1 - a i := fun i => by linarith [(ha i).2]
  -- The carrier `J(y) = {i : 0 < yᵢ < 1}`.
  obtain ⟨Jx, hJx⟩ : ∃ Jx : Eucl (m + 1 + ℓ) → Finset (Fin (m + 1 + ℓ)),
      ∀ y i, i ∈ Jx y ↔ (0 < y i ∧ y i < 1) :=
    ⟨fun y => Finset.univ.filter (fun i => 0 < y i ∧ y i < 1), fun y i => by simp⟩
  have hoff01 : ∀ y : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → ∀ i, i ∉ Jx y →
      y i = 0 ∨ y i = 1 := by
    intro y hy i hi
    rw [hJx] at hi
    rcases (hy i).1.lt_or_eq with h0 | h0
    · exact Or.inr (le_antisymm (hy i).2 (not_lt.1 fun h1 => hi ⟨h0, h1⟩))
    · exact Or.inl h0.symm
  -- The gauge `N(y) = max_{i ∈ J(y)} max ((yᵢ - aᵢ) / (1 - aᵢ), (aᵢ - yᵢ) / aᵢ)`.
  obtain ⟨N, hNle, hNex⟩ : ∃ N : Eucl (m + 1 + ℓ) → ℝ,
      (∀ y, ∀ i ∈ Jx y, max ((y i - a i) / (1 - a i)) ((a i - y i) / a i) ≤ N y) ∧
      (∀ y, (Jx y).Nonempty → ∃ i ∈ Jx y,
        N y = max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) := by
    refine ⟨fun y => if h : (Jx y).Nonempty then
      (Jx y).sup' h (fun i => max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) else 0, ?_, ?_⟩
    · intro y i hi
      have h : (Jx y).Nonempty := ⟨i, hi⟩
      simp only [dite_eq_left h]
      exact Finset.le_sup' (fun i => max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) hi
    · intro y h
      obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' h
        (fun i => max ((y i - a i) / (1 - a i)) ((a i - y i) / a i))
      exact ⟨i, hi, by simp only [dite_eq_left h]; exact he⟩
  -- `y` is *active* if `y ∈ C ∖ La` and `|J(y)| ≥ m + 2`.  `R` retracts an active `y` radially
  -- from the centre of its carrier face onto the boundary of that face and fixes all other points.
  obtain ⟨R, hRa, hRn⟩ : ∃ R : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
      (∀ y, ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) →
        ∀ i, R y i = if i ∈ Jx y then a i + (y i - a i) / N y else y i) ∧
      (∀ y, ¬((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) → R y = y) := by
    refine ⟨fun y => if ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) then
      WithLp.toLp 2 (fun i => if i ∈ Jx y then a i + (y i - a i) / N y else y i) else y, ?_, ?_⟩
    · intro y hy i
      dsimp only
      rw [ite_eq_left hy]
    · intro y hy
      dsimp only
      rw [ite_eq_right hy]
  -- One step: for active `y`, `N(y) > 0`, `R(y) ∈ C ∖ La` and `|J(R y)| < |J(y)|`.
  have step : ∀ y, ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) →
      0 < N y ∧ (∀ i, 0 ≤ R y i ∧ R y i ≤ 1) ∧ R y ∉ La ∧ (Jx (R y)).card + 1 ≤ (Jx y).card := by
    intro y hact
    have hRi := hRa y hact
    obtain ⟨hyC, hyL, hyJ⟩ := hact
    -- `N(y) ≤ 0` would force `y = a` on `J(y)`, hence `y ∈ La`.
    have hNpos : 0 < N y := by
      by_contra hle
      rw [not_lt] at hle
      apply hyL
      rw [hLa]
      obtain ⟨J', hJ'sub, hJ'card⟩ := Finset.exists_subset_card_eq hyJ
      refine ⟨J', hJ'card, fun i hi => ⟨0, ?_⟩⟩
      have hi' := hJ'sub hi
      have h := (hNle y i hi').trans hle
      have h1 : (y i - a i) / (1 - a i) ≤ 0 := (le_max_left _ _).trans h
      have h2 : (a i - y i) / a i ≤ 0 := (le_max_right _ _).trans h
      rw [div_le_iff₀ (ha2 i), zero_mul] at h1
      rw [div_le_iff₀ (ha1 i), zero_mul] at h2
      simp only [Int.cast_zero]
      linarith
    have hbd : ∀ i ∈ Jx y, 0 ≤ a i + (y i - a i) / N y ∧ a i + (y i - a i) / N y ≤ 1 := by
      intro i hi
      have h := hNle y i hi
      have h1 : (y i - a i) / (1 - a i) ≤ N y := (le_max_left _ _).trans h
      have h2 : (a i - y i) / a i ≤ N y := (le_max_right _ _).trans h
      rw [div_le_iff₀ (ha2 i)] at h1
      rw [div_le_iff₀ (ha1 i)] at h2
      constructor
      · have h3 : (a i - y i) / N y ≤ a i := by rw [div_le_iff₀ hNpos]; linarith
        have e : (y i - a i) / N y = -((a i - y i) / N y) := by ring
        linarith
      · have h3 : (y i - a i) / N y ≤ 1 - a i := by rw [div_le_iff₀ hNpos]; linarith
        linarith
    have hRC : ∀ i, 0 ≤ R y i ∧ R y i ≤ 1 := by
      intro i
      rw [hRi]
      split_ifs with hi
      · exact hbd i hi
      · exact hyC i
    -- A maximising coordinate `i₀` of the gauge is sent to `0` or `1`.
    have hne : (Jx y).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨i₀, hi₀, hNi₀⟩ := hNex y hne
    have hext : R y i₀ = 0 ∨ R y i₀ = 1 := by
      rw [hRi, ite_eq_left hi₀]
      rcases max_cases ((y i₀ - a i₀) / (1 - a i₀)) ((a i₀ - y i₀) / a i₀) with ⟨hm, _⟩ | ⟨hm, _⟩
      · right
        rw [hm] at hNi₀
        have h4 : (y i₀ - a i₀) / N y = 1 - a i₀ := by
          rw [div_eq_iff hNpos.ne', hNi₀, mul_comm, div_mul_cancel₀ _ (ha2 i₀).ne']
        linarith
      · left
        rw [hm] at hNi₀
        have h4 : (a i₀ - y i₀) / N y = a i₀ := by
          rw [div_eq_iff hNpos.ne', hNi₀, mul_comm, div_mul_cancel₀ _ (ha1 i₀).ne']
        have e : (y i₀ - a i₀) / N y = -((a i₀ - y i₀) / N y) := by ring
        linarith
    have hsub : Jx (R y) ⊆ (Jx y).erase i₀ := by
      intro i hi
      rw [hJx] at hi
      rw [Finset.mem_erase]
      constructor
      · rintro rfl
        rcases hext with h | h <;> rw [h] at hi <;> linarith [hi.1, hi.2]
      · by_contra hni
        rw [hRi, ite_eq_right hni] at hi
        exact hni ((hJx y i).2 hi)
    have hcard : (Jx (R y)).card + 1 ≤ (Jx y).card := by
      have h5 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi₀] at h5
      have : 0 < (Jx y).card := Finset.card_pos.2 hne
      omega
    -- `R(y) - c = N(y)⁻¹ (y - c)` for the centre `c` of the carrier face, so `R(y) ∉ La`.
    have hRL : R y ∉ La := by
      intro hRyL
      apply hyL
      let c : Eucl (m + 1 + ℓ) := WithLp.toLp 2 (fun i => if i ∈ Jx y then a i else y i)
      have hc : ∀ i, c i = if i ∈ Jx y then a i else y i := fun i => rfl
      refine hcone (Jx y) c y (R y) (N y)⁻¹ (fun i hi => by rw [hc, ite_eq_left hi])
        (fun i hi => by rw [hc, ite_eq_right hi]; exact hoff01 y hyC i hi)
        (fun i hi => by rw [hc, ite_eq_right hi]) hRC (inv_pos.2 hNpos) (fun i => ?_) hRyL
      rw [hRi, hc]
      split_ifs with hi
      · ring
      · ring
    exact ⟨hNpos, hRC, hRL, hcard⟩
  -- Iteration: `R^k` stays in `C ∖ La`, and `|J(R^k y)| ≤ m + 1` or `|J(R^k y)| + k ≤ |J(y)|`.
  have iter : ∀ k : ℕ, ∀ y : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → y ∉ La →
      (∀ i, 0 ≤ R^[k] y i ∧ R^[k] y i ≤ 1) ∧ R^[k] y ∉ La ∧
        ((Jx (R^[k] y)).card ≤ m + 1 ∨ (Jx (R^[k] y)).card + k ≤ (Jx y).card) := by
    intro k
    induction k with
    | zero => intro y hyC hyL; exact ⟨hyC, hyL, Or.inr (by simp)⟩
    | succ k ih =>
      intro y hyC hyL
      obtain ⟨hzC, hzL, hzJ⟩ := ih y hyC hyL
      rw [Function.iterate_succ_apply']
      by_cases hact : ((∀ i, 0 ≤ R^[k] y i ∧ R^[k] y i ≤ 1) ∧ R^[k] y ∉ La ∧
          m + 2 ≤ (Jx (R^[k] y)).card)
      · obtain ⟨-, hC', hL', hJ'⟩ := step _ hact
        refine ⟨hC', hL', ?_⟩
        have := hact.2.2
        omega
      · rw [hRn _ hact]
        refine ⟨hzC, hzL, Or.inl ?_⟩
        by_contra h
        exact hact ⟨hzC, hzL, by omega⟩
  -- After `ℓ` steps the carrier has at most `m + 1` elements, as `|J(y)| ≤ m + 1 + ℓ`.
  have hfinal : ∀ y : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → y ∉ La →
      (Jx (R^[ℓ] y)).card ≤ m + 1 := by
    intro y hyC hyL
    obtain ⟨-, -, h⟩ := iter ℓ y hyC hyL
    have := Finset.card_le_univ (Jx y)
    rw [Fintype.card_fin] at this
    omega
  refine ⟨R^[ℓ], ?_, ?_, ?_, ?_⟩
  · -- (α): at least `ℓ` coordinates of `R^ℓ x` lie outside the carrier, i.e. in `{0, 1}`.
    intro x hx hxL
    obtain ⟨hC, -, -⟩ := iter ℓ x hx hxL
    have hc := hfinal x hx hxL
    refine ⟨hC, ?_⟩
    have hcompl : ℓ ≤ (Finset.univ \ Jx (R^[ℓ] x)).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_fin]; omega
    obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hcompl
    exact ⟨I, hIcard, fun i hi => hoff01 _ hC i (Finset.mem_sdiff.1 (hIsub hi)).2⟩
  · -- (β): `R` commutes with integer translations inside `C ∖ La` (same carrier, same gauge).
    have stepT : ∀ y y' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → y ∉ La →
        (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → y' ∉ La → (∀ i, ∃ k : ℤ, y' i - y i = k) →
        ∀ i, R y' i - R y i = y' i - y i := by
      intro y y' hyC hyL hy'C hy'L hz
      have hsame : ∀ i, (0 < y i ∧ y i < 1) ∨ (0 < y' i ∧ y' i < 1) → y' i = y i := by
        intro i hi
        obtain ⟨k, hk⟩ := hz i
        have hk0 : k = 0 := by
          have hb : (-1 : ℝ) < k ∧ (k : ℝ) < 1 := by
            rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · constructor <;> linarith [(hy'C i).1, (hy'C i).2]
            · constructor <;> linarith [(hyC i).1, (hyC i).2]
          have h1 : (-1 : ℤ) < k := by exact_mod_cast hb.1
          have h2 : k < 1 := by exact_mod_cast hb.2
          omega
        rw [hk0, Int.cast_zero] at hk
        linarith
      have hJeq : Jx y' = Jx y := by
        ext i
        rw [hJx, hJx]
        constructor
        · intro h; rw [← hsame i (Or.inr h)]; exact h
        · intro h; rw [hsame i (Or.inl h)]; exact h
      by_cases hact : ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card)
      · have hact' : ((∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ y' ∉ La ∧ m + 2 ≤ (Jx y').card) :=
          ⟨hy'C, hy'L, by rw [hJeq]; exact hact.2.2⟩
        have hterm : ∀ i ∈ Jx y, max ((y' i - a i) / (1 - a i)) ((a i - y' i) / a i) =
            max ((y i - a i) / (1 - a i)) ((a i - y i) / a i) := by
          intro i hi
          rw [hsame i (Or.inl ((hJx y i).1 hi))]
        have hNeq : N y' = N y := by
          have hne : (Jx y).Nonempty := Finset.card_pos.1 (by have := hact.2.2; omega)
          obtain ⟨i₀, hi₀, h₀⟩ := hNex y hne
          obtain ⟨i₁, hi₁, h₁⟩ := hNex y' (by rw [hJeq]; exact hne)
          rw [hJeq] at hi₁
          apply le_antisymm
          · rw [h₁, hterm i₁ hi₁]; exact hNle y i₁ hi₁
          · rw [h₀, ← hterm i₀ hi₀]; exact hNle y' i₀ (by rw [hJeq]; exact hi₀)
        intro i
        rw [hRa y' hact' i, hRa y hact i, hJeq, hNeq]
        split_ifs with hi
        · rw [hsame i (Or.inl ((hJx y i).1 hi))]; ring
        · ring
      · have hact' : ¬((∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ y' ∉ La ∧ m + 2 ≤ (Jx y').card) := by
          rintro ⟨-, -, h⟩
          exact hact ⟨hyC, hyL, by rw [← hJeq]; exact h⟩
        intro i
        rw [hRn y hact, hRn y' hact']
    intro x x' hx hxL hx' hx'L hz
    have hk : ∀ k : ℕ, ∀ i, R^[k] x' i - R^[k] x i = x' i - x i := by
      intro k
      induction k with
      | zero => intro i; rfl
      | succ k ih =>
        intro i
        obtain ⟨hC, hL, -⟩ := iter k x hx hxL
        obtain ⟨hC', hL', -⟩ := iter k x' hx' hx'L
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hz' : ∀ j, ∃ k' : ℤ, R^[k] x' j - R^[k] x j = k' := fun j => by
          rw [ih j]; exact hz j
        rw [stepT _ _ hC hL hC' hL' hz' i, ih i]
    exact hk ℓ
  · -- (S1): `ℓ` coordinates in `{0, 1}` leave a carrier of size `≤ m + 1`, so `R` fixes `x`.
    rintro x hx hxL ⟨I, hIcard, hI⟩
    have hsub : Jx x ⊆ Finset.univ \ I := by
      intro i hi
      rw [hJx] at hi
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hiI => ?_⟩
      rcases hI i hiI with h | h <;> rw [h] at hi <;> linarith [hi.1, hi.2]
    have hc : (Jx x).card ≤ m + 1 := by
      have h5 := Finset.card_le_card hsub
      rw [Finset.card_univ_sdiff, Fintype.card_fin, hIcard] at h5
      omega
    have hR : R x = x := hRn x (fun h => by have := h.2.2; omega)
    exact Function.iterate_fixed hR ℓ
  · -- (S2): the exit point `y` of the ray from the face centre `c` through `x` is `R(x)` or `x`.
    intro J c x y s hJ hcJ hc01 hx hxL hxc hy hs hray hext
    have hyoff : ∀ i ∉ J, y i = c i := fun i hi => by
      have := hray i
      rw [hxc i hi, sub_self, mul_zero] at this
      linarith
    by_cases hint : ∀ i ∈ J, 0 < x i ∧ x i < 1
    · -- Case A: `x` lies in the relative interior of the face, so `J(x) = J`, `N(x) = s⁻¹` and
      -- `y = R(x)`; then `R^ℓ y = R (R^ℓ x) = R^ℓ x`.
      have hJeq : Jx x = J := by
        ext i
        rw [hJx]
        constructor
        · intro h
          by_contra hiJ
          rw [hxc i hiJ] at h
          rcases hc01 i hiJ with h0 | h0 <;> rw [h0] at h <;> linarith [h.1, h.2]
        · exact hint i
      have hact : ((∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x ∉ La ∧ m + 2 ≤ (Jx x).card) :=
        ⟨hx, hxL, by rw [hJeq]; exact hJ⟩
      have hterm_le : ∀ i ∈ J, max ((x i - a i) / (1 - a i)) ((a i - x i) / a i) ≤ s⁻¹ := by
        intro i hi
        have hyi := hy i
        have hr := hray i
        rw [hcJ i hi] at hr
        apply max_le
        · rw [div_le_iff₀ (ha2 i)]
          have h6 : s * (x i - a i) ≤ 1 - a i := by linarith [hyi.2]
          calc x i - a i = s⁻¹ * (s * (x i - a i)) := by field_simp
            _ ≤ s⁻¹ * (1 - a i) := mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hs.le)
        · rw [div_le_iff₀ (ha1 i)]
          have h6 : s * (a i - x i) ≤ a i := by linarith [hyi.1]
          calc a i - x i = s⁻¹ * (s * (a i - x i)) := by field_simp
            _ ≤ s⁻¹ * a i := mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hs.le)
      have hNx : N x = s⁻¹ := by
        apply le_antisymm
        · obtain ⟨i₀, hi₀, h₀⟩ := hNex x (Finset.card_pos.1 (by rw [hJeq]; omega))
          rw [h₀]
          rw [hJeq] at hi₀
          exact hterm_le i₀ hi₀
        · obtain ⟨i₁, hi₁J, hi₁⟩ := hext
          have hle := hNle x i₁ (by rw [hJeq]; exact hi₁J)
          have hr := hray i₁
          rw [hcJ i₁ hi₁J] at hr
          rcases hi₁ with h0 | h1
          · have h7 : (a i₁ - x i₁) / a i₁ = s⁻¹ := by
              rw [div_eq_iff (ha1 i₁).ne']
              rw [h0] at hr
              field_simp
              linarith
            rw [← h7]
            exact (le_max_right _ _).trans hle
          · have h7 : (x i₁ - a i₁) / (1 - a i₁) = s⁻¹ := by
              rw [div_eq_iff (ha2 i₁).ne']
              rw [h1] at hr
              field_simp
              linarith
            rw [← h7]
            exact (le_max_left _ _).trans hle
      have hRx : R x = y := by
        ext i
        rw [hRa x hact i, hJeq]
        split_ifs with hi
        · rw [hNx]
          have hr := hray i
          rw [hcJ i hi] at hr
          rw [div_inv_eq_mul]
          linarith
        · rw [hyoff i hi, hxc i hi]
      rw [← hRx, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
      have hc := hfinal x hx hxL
      exact hRn _ (fun h => by have := h.2.2; omega)
    · -- Case B: `x` lies on the relative boundary of the face; then `s = 1` and `y = x`.
      push Not at hint
      obtain ⟨i₂, hi₂J, hi₂⟩ := hint
      have hx01 : x i₂ = 0 ∨ x i₂ = 1 := by
        rcases (hx i₂).1.lt_or_eq with h0 | h0
        · right; exact le_antisymm (hx i₂).2 (hi₂ h0)
        · left; exact h0.symm
      have hs1 : s ≤ 1 := by
        have hr := hray i₂
        rw [hcJ i₂ hi₂J] at hr
        have hyi := hy i₂
        have hai1 := ha1 i₂
        have hai2 := ha2 i₂
        rcases hx01 with h0 | h1
        · rw [h0] at hr
          nlinarith
        · rw [h1] at hr
          nlinarith
      have hs1' : 1 ≤ s := by
        obtain ⟨i₁, hi₁J, hi₁⟩ := hext
        have hr := hray i₁
        rw [hcJ i₁ hi₁J] at hr
        have hxi := hx i₁
        have hai1 := ha1 i₁
        have hai2 := ha2 i₁
        rcases hi₁ with h0 | h1
        · rw [h0] at hr
          nlinarith [mul_nonneg hs.le hxi.1]
        · rw [h1] at hr
          nlinarith [mul_le_mul_of_nonneg_left hxi.2 hs.le]
      have hyx : y = x := by
        ext i
        have := hray i
        rw [le_antisymm hs1 hs1', one_mul] at this
        linarith
      rw [hyx]
/-- Simon Ch. 6, Lemma 5.4, proof p. 163 ("by (7), (8) and the chain rule"), pointwise form:
if `f` is `K₁`-Lipschitz at `x` within `A`, `f` maps `A` into `B`, and `g` is `K₂`-Lipschitz at
`f x` within `B`, then `g ∘ f` is `K₁ K₂`-Lipschitz at `x` within `A`.  With
`η = min{1, ε/(K₁ + K₂ + 1)}` and `δ = min{δ₁, δ₂/(K₁ + η)}` one gets
`(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + ε`. -/
theorem Submission.dr_cc_lip_at_comp : ∀ (X Y Z : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z] (f : X → Y) (g : Y → Z) (A : Set X) (B : Set Y) (x : X) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ → MapsTo f A B → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (f x') (f x) ≤ (K₁ + ε) * dist x' x) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' (f x) < δ → dist (g y') (g (f x)) ≤ (K₂ + ε) * dist y' (f x)) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (g (f x')) (g (f x)) ≤ (K₁ * K₂ + ε) * dist x' x := by
  intro X Y Z _ _ _ f g A B x K₁ K₂ hK₁ hK₂ hfAB hf hg ε hε
  -- The auxiliary level `η = min{1, ε/(K₁ + K₂ + 1)}`: `0 < η ≤ 1` and `η(K₁ + K₂ + 1) ≤ ε`.
  have hS : 0 < K₁ + K₂ + 1 := by linarith
  obtain ⟨η, hη, hη1, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η * (K₁ + K₂ + 1) ≤ ε :=
    ⟨min 1 (ε / (K₁ + K₂ + 1)), lt_min one_pos (div_pos hε hS), min_le_left _ _,
      (le_div_iff₀ hS).1 (min_le_right _ _)⟩
  -- `δ₁` for `f` and `δ₂` for `g` at level `η`; then `δ = min{δ₁, δ₂/(K₁ + η)}`.
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf η hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg η hη
  have hL : 0 < K₁ + η := by linarith
  refine ⟨min δ₁ (δ₂ / (K₁ + η)), lt_min hδ₁ (div_pos hδ₂ hL), fun x' hx' hd => ?_⟩
  -- `d(f x', f x) ≤ (K₁ + η) d(x', x) < δ₂`, and `f x' ∈ B`, so the bound for `g` applies.
  have hfx : dist (f x') (f x) ≤ (K₁ + η) * dist x' x := h₁ x' hx' (hd.trans_le (min_le_left _ _))
  have hd₂ : (K₁ + η) * dist x' x < δ₂ := by
    rw [← lt_div_iff₀' hL]
    exact hd.trans_le (min_le_right _ _)
  have hgx := h₂ (f x') (hfAB hx') (hfx.trans_lt hd₂)
  -- `(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + η(K₁ + K₂ + 1) ≤ K₁K₂ + ε`.
  have hη2 : η * (K₁ + K₂ + η) ≤ η * (K₁ + K₂ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  calc dist (g (f x')) (g (f x)) ≤ (K₂ + η) * dist (f x') (f x) := hgx
    _ ≤ (K₂ + η) * ((K₁ + η) * dist x' x) := mul_le_mul_of_nonneg_left hfx (by linarith)
    _ = (K₁ * K₂ + η * (K₁ + K₂ + η)) * dist x' x := by ring
    _ ≤ (K₁ * K₂ + ε) * dist x' x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
/-- Union rule for pointwise upper Lipschitz bounds (used for Simon Ch. 6, Lemma 5.4, p. 162,
where `y` may lie on several closed faces): if `g` is `K`-Lipschitz at `y` within `G k ∩ B` for
every closed piece `G k ∋ y`, and `B ⊆ ⋃ k, G k` with finitely many pieces, then `g` is
`K`-Lipschitz at `y` within `B`.  Pieces missing `y` stay a positive distance away from `y`, and
the minimum of finitely many radii is a common radius. -/
theorem Submission.dr_cc_lip_at_union : ∀ (X Y : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] (ι : Type) [Finite ι] (G : ι → Set X) (B : Set X) (g : X → Y) (y : X) (K : ℝ), (∀ k, IsClosed (G k)) → B ⊆ ⋃ k, G k → (∀ k, y ∈ G k → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ G k ∩ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y := by
  intro X Y _ _ ι _ G B g y K hG hB hloc ε hε
  -- A radius `r k > 0` for each piece: from the hypothesis if `y ∈ G k`, and otherwise a ball
  -- around `y` missing the closed set `G k` (the bound then holds vacuously).
  have hr : ∀ k, ∃ r : ℝ, 0 < r ∧
      ∀ y' ∈ G k ∩ B, dist y' y < r → dist (g y') (g y) ≤ (K + ε) * dist y' y := by
    intro k
    by_cases hyk : y ∈ G k
    · exact hloc k hyk ε hε
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hG k).isOpen_compl y hyk
      exact ⟨r, hr, fun y' hy' hdist => absurd hy'.1 (hball (Metric.mem_ball.2 hdist))⟩
  choose r hr0 hrb using hr
  -- A common radius `δ ≤ r k`: the minimum over the finite index type (`1` if `ι` is empty).
  obtain ⟨δ, hδ, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ r k := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun k => isEmptyElim k⟩
    · obtain ⟨k₀, hk₀⟩ := Finite.exists_min r
      exact ⟨r k₀, hr0 k₀, hk₀⟩
  -- A point `y' ∈ B` lies in some piece `G k`, and `dist y' y < δ ≤ r k`.
  refine ⟨δ, hδ, fun y' hy' hdist => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hB hy')
  exact hrb k y' ⟨hk, hy'⟩ (hdist.trans_le (hδr k))

/-- Simon Ch. 6, Lemma 5.4, claim (3) (pp. 162–163), as a pointwise upper Lipschitz bound.  Let
`ψ₀` satisfy (S1) (`ψ₀ x = x` on `C ∖ La` where `ℓ` coordinates lie in `{0, 1}`) and (S2) (on each
face of dimension `≥ m + 2`, `ψ₀` is constant along the rays from its centre `c` up to its
boundary).  Then near `x ∈ C ∖ La`, `|ψ₀ x' - ψ₀ x| ≤ (c₁ / dist(x, La) + ε) |x' - x|`.

Induction on the dimension `j` of the faces `F` of `C = [0,1]^d`, with
`c₁(j) = β r q^(j - (m + 2))`, `r = √d`, `β = 1 + 4r`, `q = 4rβ`.  On `F ∖ La`, `ψ₀ = ψ₀ ∘ g` for
the radial projection `g` from `c` onto `∂F` (S2).  For `j = m + 2`, `ψ₀ = g` there (S1).  For
`j + 1`, the bound at `g x` on the facets through `g x` glues to `∂F ∖ La` and composes with that
of `g`.  Finally `dist(g x, La) ≥ min(1/4, s dist(x, La))` turns `β s c₁(j) / dist(g x, La)` into
`c₁(j + 1) / dist(x, La)`. -/
theorem Submission.dr_cc_pointwise_lip :
    ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ a : Eucl (m + 1 + ℓ), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) →
      ∀ La : Set (Eucl (m + 1 + ℓ)),
        La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧
          ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} →
      ∀ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
        (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
          (∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, x i = 0 ∨ x i = 1) → ψ₀ x = x) →
        (∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), m + 2 ≤ J.card →
          (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
          x ∉ La → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s →
          (∀ i, y i - c i = s * (x i - c i)) → (∃ i ∈ J, y i = 0 ∨ y i = 1) → ψ₀ y = ψ₀ x) →
        ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La →
            dist x' x < δ → dist (ψ₀ x') (ψ₀ x) ≤ (c₁ / infDist x La + ε) * dist x' x := by
  intro m ℓ hℓ
  -- Constants: `r = √d ≥ 1`, `β = 1 + 4r ≤ q = 4rβ`, `c₁(j) = β r q^(j - (m + 2))`, `c₁ = c₁(d)`.
  obtain ⟨r, hr⟩ : ∃ r : ℝ, Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [← hr, Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ m + 1 + ℓ by omega)
  have hr0 : 0 ≤ r := by linarith
  have hβ : 0 < 1 + 4 * r := by linarith
  have hq : 0 < 4 * r * (1 + 4 * r) := mul_pos (by linarith) hβ
  have hβq : 1 + 4 * r ≤ 4 * r * (1 + 4 * r) := by nlinarith
  refine ⟨(1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (m + 1 + ℓ - (m + 2)), by positivity, ?_⟩
  intro a ha La hLa ψ₀ hS1 hS2
  -- `La` is closed, contains the centre of every face of dimension `≥ m + 2` (so `a ∈ La`), and
  -- has the cone property; so `dist(z, La) > 0` for `z ∉ La`.
  obtain ⟨hLac, hcLa, hcone⟩ := Submission.dr_cc_skeleton_facts m ℓ a ha La hLa
  have hLane : La.Nonempty :=
    ⟨a, hcLa Finset.univ a (by rw [Finset.card_univ, Fintype.card_fin]; omega) fun i _ => rfl⟩
  have hdpos : ∀ z, z ∉ La → 0 < infDist z La := fun z hz =>
    (hLac.notMem_iff_infDist_pos hLane).1 hz
  -- A face `(J, c)` (`c i = a i` on `J`, `c i ∈ {0, 1}` off `J`) has point set
  -- `F = {x ∈ C : x i = c i for i ∉ J}`.  For `|J| ≥ m + 2`, the radial map `g` from `c ∈ La`
  -- sends `F ∖ La` into `∂F ∖ La` with `ψ₀ ∘ g = ψ₀` there (S2), and is `β s`-Lipschitz at `x`.
  have setup : ∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)), m + 2 ≤ J.card →
      (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) →
      ∃ g : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
        (∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) →
          x' ∉ La → (∀ i, 0 ≤ g x' i ∧ g x' i ≤ 1) ∧ (∀ i ∉ J, g x' i = c i) ∧
            (∃ i ∈ J, g x' i = 0 ∨ g x' i = 1) ∧ g x' ∉ La ∧ ψ₀ (g x') = ψ₀ x') ∧
        ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i ∉ J, x i = c i) → x ∉ La →
          ∃ s : ℝ, 0 < s ∧ (∀ i, g x i - c i = s * (x i - c i)) ∧ s * infDist x La ≤ r ∧
            ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ),
              (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) → dist x' x < δ →
              dist (g x') (g x) ≤ ((1 + 4 * r) * s + ε) * dist x' x := by
    intro J c hJ hcJ hcJc
    obtain ⟨g, hg⟩ := Submission.dr_cc_radial_map (m + 1 + ℓ) a ha J c hcJ
    have hc : c ∈ La := hcLa J c hJ hcJ
    refine ⟨g, fun x' hx'C hx'F hx'La => ?_, fun x hxC hxF hxLa => ?_⟩
    · obtain ⟨hgC, hgJ, s', hs', hscale, -⟩ := hg x' hx'C hx'F fun h => hx'La (h ▸ hc)
      have hgF : ∀ i ∉ J, g x' i = c i := fun i hi => by
        have h := hscale i
        rwa [hx'F i hi, sub_self, mul_zero, sub_eq_zero] at h
      exact ⟨hgC, hgF, hgJ, fun h => hx'La (hcone J c x' (g x') s' hcJ hcJc hx'F hgC hs' hscale h),
        hS2 J c x' (g x') s' hJ hcJ hcJc hx'C hx'La hx'F hgC hs' hscale hgJ⟩
    · obtain ⟨-, -, s, hs, hscale, hsr, hlip⟩ := hg x hxC hxF fun h => hxLa (h ▸ hc)
      rw [hr] at hsr hlip
      exact ⟨s, hs, hscale,
        (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem hc) hs.le).trans hsr, hlip⟩
  -- Claim `P(j)`: on every face of dimension `j ≥ m + 2`, `ψ₀` is `c₁(j) / dist(x, La)`-Lipschitz
  -- at every `x ∈ F ∖ La` within `F ∖ La`.
  have key : ∀ j : ℕ, m + 2 ≤ j → ∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)),
      J.card = j → (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) →
      ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i ∉ J, x i = c i) → x ∉ La →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ),
        (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) → x' ∉ La → dist x' x < δ →
        dist (ψ₀ x') (ψ₀ x) ≤
          ((1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) / infDist x La + ε) *
            dist x' x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      -- `|J| = m + 2`: `g` lands where `ℓ` coordinates lie in `{0, 1}`, so `ψ₀ = g` on `F ∖ La`
      -- by (S1), and `β s ≤ β r / dist(x, La)` as `s dist(x, La) ≤ s |x - c| ≤ r`.
      intro J c hJc hcJ hcJc x hxC hxF hxLa ε hε
      obtain ⟨g, hgA, hgx⟩ := setup J c hJc.ge hcJ hcJc
      have hψg : ∀ z : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ z i ∧ z i ≤ 1) → (∀ i ∉ J, z i = c i) →
          z ∉ La → ψ₀ z = g z := by
        intro z hzC hzF hzLa
        obtain ⟨hgzC, hgzF, ⟨i, hiJ, hi⟩, hgzLa, hψ⟩ := hgA z hzC hzF hzLa
        rw [← hψ]
        refine hS1 (g z) hgzC hgzLa ⟨insert i (Finset.univ \ J), ?_, fun k hk => ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hiJ]), Finset.card_univ_sdiff,
            Fintype.card_fin, hJc]
          omega
        · rcases Finset.mem_insert.1 hk with rfl | hk
          · exact hi
          · have hkJ : k ∉ J := (Finset.mem_sdiff.1 hk).2
            rw [hgzF k hkJ]
            exact hcJc k hkJ
      obtain ⟨s, hs, -, hsr, hlip⟩ := hgx x hxC hxF hxLa
      obtain ⟨δ, hδ, hδlip⟩ := hlip ε hε
      refine ⟨δ, hδ, fun x' hx'C hx'F hx'La hx'x => ?_⟩
      rw [hψg x' hx'C hx'F hx'La, hψg x hxC hxF hxLa]
      refine (hδlip x' hx'C hx'F hx'x).trans
        (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) dist_nonneg)
      rw [Nat.sub_self, pow_zero, mul_one, le_div_iff₀ (hdpos x hxLa)]
      nlinarith [mul_le_mul_of_nonneg_left hsr hβ.le]
    | succ j hj ih =>
      intro J c hJc hcJ hcJc x hxC hxF hxLa
      obtain ⟨g, hgA, hgx⟩ := setup J c (by omega) hcJ hcJc
      obtain ⟨s, hs, hscale, hsr, hlip⟩ := hgx x hxC hxF hxLa
      obtain ⟨hyC, hyF, -, hyLa, hψy⟩ := hgA x hxC hxF hxLa
      have hdx := hdpos x hxLa
      have hdy := hdpos (g x) hyLa
      -- `ψ₀` is `c₁(j) / dist(g x, La)`-Lipschitz at `g x` within `∂F ∖ La`: `P(j)` on each facet
      -- `F ∩ {y i = b}` (`i ∈ J`, `b ∈ {0, 1}`) through `g x`, glued over the finitely many facets.
      have hψB : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ {y' : Eucl (m + 1 + ℓ) |
          (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ (∀ i ∉ J, y' i = c i) ∧ (∃ i ∈ J, y' i = 0 ∨ y' i = 1) ∧
            y' ∉ La}, dist y' (g x) < δ → dist (ψ₀ y') (ψ₀ (g x)) ≤
          ((1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) / infDist (g x) La + ε) *
            dist y' (g x) := by
        have hcoord : ∀ k : Fin (m + 1 + ℓ), Continuous fun y' : Eucl (m + 1 + ℓ) => y' k :=
          fun k => PiLp.continuous_apply 2 _ k
        refine Submission.dr_cc_lip_at_union (Eucl (m + 1 + ℓ)) (Eucl (m + 1 + ℓ))
          (Fin (m + 1 + ℓ) × Bool) (fun p => {y' : Eucl (m + 1 + ℓ) | (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧
            (∀ i ∉ J, y' i = c i) ∧ p.1 ∈ J ∧ y' p.1 = if p.2 then 1 else 0}) _ ψ₀ (g x) _
          (fun p => ?_) ?_ ?_
        · -- Each facet is closed.
          have h1 : IsClosed {y' : Eucl (m + 1 + ℓ) | ∀ i, 0 ≤ y' i ∧ y' i ≤ 1} := by
            simp only [Set.ofPred_forall]
            exact isClosed_iInter fun i => (isClosed_le continuous_const (hcoord i)).inter
              (isClosed_le (hcoord i) continuous_const)
          have h2 : IsClosed {y' : Eucl (m + 1 + ℓ) | ∀ i ∉ J, y' i = c i} := by
            simp only [Set.ofPred_forall]
            exact isClosed_iInter fun i =>
              isClosed_iInter fun _ => isClosed_eq (hcoord i) continuous_const
          exact h1.inter (h2.inter
            (isClosed_const.inter (isClosed_eq (hcoord p.1) continuous_const)))
        · -- The facets cover `∂F ∖ La`.
          rintro y' ⟨hy'C, hy'F, ⟨i, hiJ, hi | hi⟩, -⟩
          · exact Set.mem_iUnion.2 ⟨(i, false), hy'C, hy'F, hiJ, by simp [hi]⟩
          · exact Set.mem_iUnion.2 ⟨(i, true), hy'C, hy'F, hiJ, by simp [hi]⟩
        · -- The facet through `g x` is the face `(J.erase i, c')`, `c' i = b`, of dimension `j`.
          rintro ⟨i, b⟩ hy ε hε
          obtain ⟨-, -, hiJ, hyi⟩ : (∀ k, 0 ≤ g x k ∧ g x k ≤ 1) ∧ (∀ k ∉ J, g x k = c k) ∧
              i ∈ J ∧ g x i = if b then 1 else 0 := hy
          obtain ⟨c', hc'i, hc'k⟩ : ∃ c' : Eucl (m + 1 + ℓ),
              c' i = (if b then 1 else 0) ∧ ∀ k ≠ i, c' k = c k :=
            ⟨WithLp.toLp 2 fun k => if k = i then (if b then 1 else 0) else c k, by simp,
              fun k hk => by simp [hk]⟩
          have hF' : ∀ z : Eucl (m + 1 + ℓ), (∀ k ∉ J, z k = c k) →
              z i = (if b then 1 else 0) → ∀ k ∉ J.erase i, z k = c' k := by
            intro z hzF hzi k hk
            by_cases hki : k = i
            · rw [hki, hzi, hc'i]
            · rw [hzF k fun h => hk (Finset.mem_erase.2 ⟨hki, h⟩), hc'k k hki]
          obtain ⟨δ, hδ, hδlip⟩ := ih (J.erase i) c'
            (by rw [Finset.card_erase_of_mem hiJ, hJc, Nat.add_sub_cancel])
            (fun k hk => by
              obtain ⟨hki, hkJ⟩ := Finset.mem_erase.1 hk
              rw [hc'k k hki]
              exact hcJ k hkJ)
            (fun k hk => by
              by_cases hki : k = i
              · rw [hki, hc'i]
                cases b <;> simp
              · rw [hc'k k hki]
                exact hcJc k fun h => hk (Finset.mem_erase.2 ⟨hki, h⟩))
            (g x) hyC (hF' (g x) hyF hyi) hyLa ε hε
          refine ⟨δ, hδ, fun y' hy' hy'y => ?_⟩
          obtain ⟨⟨hy'C, hy'F, -, hy'i⟩, -, -, -, hy'La⟩ := hy'
          exact hδlip y' hy'C (hF' y' hy'F hy'i) hy'La hy'y
      -- Chain rule for `ψ₀ ∘ g`, which equals `ψ₀` on `F ∖ La`.
      have hcomp := Submission.dr_cc_lip_at_comp (Eucl (m + 1 + ℓ)) (Eucl (m + 1 + ℓ))
        (Eucl (m + 1 + ℓ)) g ψ₀
        {x' : Eucl (m + 1 + ℓ) | (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) ∧ (∀ i ∉ J, x' i = c i) ∧ x' ∉ La}
        {y' : Eucl (m + 1 + ℓ) | (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ (∀ i ∉ J, y' i = c i) ∧
          (∃ i ∈ J, y' i = 0 ∨ y' i = 1) ∧ y' ∉ La}
        x ((1 + 4 * r) * s)
        ((1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) / infDist (g x) La)
        (by positivity) (by positivity)
        (fun x' hx' => by
          obtain ⟨hx'C, hx'F, hx'La⟩ := hx'
          obtain ⟨h1, h2, h3, h4, -⟩ := hgA x' hx'C hx'F hx'La
          exact ⟨h1, h2, h3, h4⟩)
        (fun ε hε => by
          obtain ⟨δ, hδ, h⟩ := hlip ε hε
          exact ⟨δ, hδ, fun x' hx' hx'x => h x' hx'.1 hx'.2.1 hx'x⟩)
        hψB
      -- The constant: `β s c₁(j) / dist(g x, La) ≤ q c₁(j) / dist(x, La) = c₁(j + 1) / dist(x, La)`
      -- by `dist(g x, La) ≥ min(1/4, s dist(x, La))` and `s dist(x, La) ≤ r`.
      have hsim := Submission.dr_cc_similarity_bound m ℓ a ha La hLa J c x (g x) s hcJ hcJc hxF
        hyC hs hscale
      have hkey : (1 + 4 * r) * s * infDist x La ≤ 4 * r * (1 + 4 * r) * infDist (g x) La := by
        rcases le_total (1 / 4) (s * infDist x La) with h14 | h14
        · rw [min_eq_left h14] at hsim
          nlinarith [mul_le_mul_of_nonneg_left hsr hβ.le, mul_le_mul_of_nonneg_left hsim hq.le]
        · rw [min_eq_right h14] at hsim
          nlinarith [mul_le_mul_of_nonneg_left hsim hq.le,
            mul_le_mul_of_nonneg_right hβq (mul_nonneg hs.le hdx.le)]
      have hQ : 0 ≤ (1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) := by positivity
      intro ε hε
      obtain ⟨δ, hδ, hδlip⟩ := hcomp ε hε
      refine ⟨δ, hδ, fun x' hx'C hx'F hx'La hx'x => ?_⟩
      have h := hδlip x' ⟨hx'C, hx'F, hx'La⟩ hx'x
      rw [(hgA x' hx'C hx'F hx'La).2.2.2.2, hψy] at h
      refine h.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) dist_nonneg)
      rw [show j + 1 - (m + 2) = j - (m + 2) + 1 by omega, pow_succ, mul_div_assoc',
        div_le_div_iff₀ hdy hdx]
      nlinarith [mul_le_mul_of_nonneg_left hkey hQ]
  -- `P(d)` on the face `C` itself (`J` = all indices, `c = a`) is the claim.
  intro x hxC hxLa ε hε
  obtain ⟨δ, hδ, h⟩ := key (m + 1 + ℓ) (by omega) Finset.univ a
    (by rw [Finset.card_univ, Fintype.card_fin]) (fun i _ => rfl)
    (fun i hi => absurd (Finset.mem_univ i) hi) x hxC (fun i hi => absurd (Finset.mem_univ i) hi)
    hxLa ε hε
  exact ⟨δ, hδ, fun x' hx'C hx'La hx'x =>
    h x' hx'C (fun i hi => absurd (Finset.mem_univ i) hi) hx'La hx'x⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
