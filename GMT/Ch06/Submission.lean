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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
