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

/-- `C_c^∞` fields are dense in `L¹(Ω)`: for `Ω ⊆ ℝⁿ` open, `c : ℝⁿ → ℝⁿ` integrable on `Ω` and
`δ > 0` there is a smooth `b` with compact support, `spt b ⊆ Ω` and `∫_Ω |c − b| < δ`.  The
exhaustion `K_j = F_j ∩ B̄(0, j)` of `Ω` gives a compact `K ⊆ Ω` with `∫_{Ω∖K} |c| < δ/2`;
`1_K c` is within `δ/2` in `L¹(ℝⁿ)` of a smooth compactly supported `b₀` (approximate simple
functions, using the regularity of `Lⁿ` and the smooth Urysohn lemma); and `b = χ b₀` for a
smooth cutoff `0 ≤ χ ≤ 1` with `χ = 1` on `K` and `spt χ ⊆ Ω`. -/
theorem Submission.slicing_im_ll_gws_smooth_dense :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (c : Eucl n → Eucl n), IsOpen Ω → IntegrableOn c Ω (volume : Measure (Eucl n)) → ∀ δ : ℝ, 0 < δ → ∃ b : Eucl n → Eucl n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ tsupport b ⊆ Ω ∧ ∫ w in Ω, ‖c w - b w‖ < δ := by
  intro n Ω c hΩ hc δ hδ
  -- Step 1: the compact exhaustion `K j = F j ∩ B̄(0, j)` of `Ω`.
  obtain ⟨F, hFc, hFΩ, hFU, hFm⟩ := hΩ.exists_iUnion_isClosed
  have hKc : ∀ j : ℕ, IsCompact (F j ∩ closedBall 0 j) := fun j =>
    (isCompact_closedBall 0 j).inter_left (hFc j)
  have hKΩ : ∀ j : ℕ, F j ∩ closedBall 0 j ⊆ Ω := fun j => inter_subset_left.trans (hFΩ j)
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Eucl n) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Eucl n) j = Ω := by
    refine Subset.antisymm (iUnion_subset hKΩ) fun w hw => ?_
    rw [← hFU] at hw
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    refine mem_iUnion.2 ⟨max i ⌈‖w‖⌉₊, hFm (le_max_left _ _) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))
  -- Step 2: a compact `K = K j ⊆ Ω` with `∫_{Ω \ K} |c| < δ / 2`.
  have hcn : IntegrableOn (fun w => ‖c w‖) Ω := hc.norm
  obtain ⟨K, hK, hKΩ', htail⟩ : ∃ K : Set (Eucl n), IsCompact K ∧ K ⊆ Ω ∧
      ∫ w in Ω \ K, ‖c w‖ < δ / 2 := by
    have hlim := tendsto_setIntegral_of_monotone (fun j => (hKc j).measurableSet) hKm
      (by rw [hKU]; exact hcn)
    rw [hKU] at hlim
    obtain ⟨j, hj⟩ := ((tendsto_order.1 hlim).1 _ (sub_lt_self _ (half_pos hδ))).exists
    refine ⟨_, hKc j, hKΩ j, ?_⟩
    rw [setIntegral_sdiff (hKc j).measurableSet hcn (hKΩ j)]
    linarith
  -- Step 3: `C_c^∞` is dense in `L¹(ℝⁿ)` (simple functions, regularity and smooth Urysohn).
  have hdense : ∀ f : Eucl n → Eucl n, Integrable f → ∀ ε : ℝ, 0 < ε →
      ∃ g : Eucl n → Eucl n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧
        ∫ w, ‖f w - g w‖ ≤ ε := by
    intro f hf ε hε
    have hind : ∀ (v : Eucl n) ⦃s : Set (Eucl n)⦄, MeasurableSet s → volume s < ∞ →
        ∀ {η : ℝ≥0∞}, η ≠ 0 → ∃ g : Eucl n → Eucl n,
          eLpNorm (g - s.indicator fun _ => v) 1 volume ≤ η ∧
            (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g) := by
      intro v s hs hμs η hη
      obtain ⟨θ, hθ0, hθ⟩ := ENNReal.exists_nnreal_pos_mul_lt
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top : 2 * ‖v‖ₑ ≠ ∞) hη
      have hθ0' : (θ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hθ0.ne'
      obtain ⟨A, hAs, hA, hsA⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hθ0'
      obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hθ0'
      obtain ⟨L, hL, hAL, hLU⟩ := exists_compact_between hA hU (hAs.trans hsU)
      obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) isOpen_interior hA.isClosed hAL
      have hχ0 : ∀ x, x ∉ interior L → χ x = 0 := fun x hx =>
        Function.notMem_support.1 (by rw [hχs]; exact hx)
      refine ⟨fun x => χ x • v, ?_, hχ.smul contDiff_const, ?_⟩
      · calc eLpNorm ((fun x => χ x • v) - s.indicator fun _ => v) 1 volume
            ≤ eLpNorm ((U \ A).indicator fun _ => v) 1 volume := by
              refine eLpNorm_mono ((hχ.continuous.smul continuous_const).aestronglyMeasurable.sub
                (aestronglyMeasurable_const.indicator hs)) fun x => ?_
              rw [Pi.sub_apply]
              by_cases hxA : x ∈ A
              · simp [(hχ1 x).1 hxA, indicator_of_mem (hAs hxA)]
              by_cases hxU : x ∈ U
              · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxA)]
                obtain ⟨h0, h1⟩ := hχr (mem_range_self x)
                by_cases hxs : x ∈ s
                · rw [indicator_of_mem hxs,
                    show χ x • v - v = (χ x - 1) • v by rw [sub_smul, one_smul], norm_smul,
                    Real.norm_eq_abs]
                  calc |χ x - 1| * ‖v‖ ≤ 1 * ‖v‖ := by
                        gcongr; rw [abs_le]; constructor <;> linarith
                    _ = ‖v‖ := one_mul _
                · rw [indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs]
                  calc |χ x| * ‖v‖ ≤ 1 * ‖v‖ := by
                        gcongr; rw [abs_le]; constructor <;> linarith
                    _ = ‖v‖ := one_mul _
              · have hxs : x ∉ s := fun h => hxU (hsU h)
                have hxL : x ∉ interior L := fun h => hxU (hLU (interior_subset h))
                simp [hχ0 x hxL, hxs]
          _ = ‖v‖ₑ * volume (U \ A) := by
              rw [eLpNorm_indicator_const (hU.measurableSet.diff hA.measurableSet).nullMeasurableSet
                one_ne_zero ENNReal.one_ne_top]
              simp
          _ ≤ ‖v‖ₑ * (θ + θ) := by
              gcongr
              calc volume (U \ A) ≤ volume ((U \ s) ∪ (s \ A)) := measure_mono fun x hx => by
                    by_cases hxs : x ∈ s
                    · exact Or.inr ⟨hxs, hx.2⟩
                    · exact Or.inl ⟨hx.1, hxs⟩
                _ ≤ volume (U \ s) + volume (s \ A) := measure_union_le _ _
                _ ≤ θ + θ := add_le_add hUs.le hsA.le
          _ = θ * (2 * ‖v‖ₑ) := by ring
          _ ≤ η := hθ.le
      · exact HasCompactSupport.intro hL fun x hx => by
          simp [hχ0 x fun h => hx (interior_subset h)]
    obtain ⟨g, hfg, hg, hgc⟩ := (memLp_one_iff_integrable.2 hf).induction_dense
      ENNReal.one_ne_top
      (fun g : Eucl n → Eucl n => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g)
      hind (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.2 hε).ne'
    refine ⟨g, hg, hgc, ?_⟩
    have hm : AEStronglyMeasurable (f - g) volume :=
      (hf.sub (hg.continuous.integrable_of_hasCompactSupport hgc)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hm] at hfg
    change ∫ w, ‖(f - g) w‖ ≤ ε
    rw [integral_norm_eq_lintegral_enorm hm]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hfg
  -- Step 3 applied to `1_K c`.
  have hKi : Integrable (K.indicator c) :=
    (integrable_indicator_iff hK.measurableSet).2 (hc.mono_set hKΩ')
  obtain ⟨b₀, hb₀, hb₀c, hb₀K⟩ := hdense _ hKi (δ / 2) (half_pos hδ)
  have hb₀i : Integrable b₀ := hb₀.continuous.integrable_of_hasCompactSupport hb₀c
  -- Step 4: a smooth cutoff `χ`, `χ = 1` exactly on `K`, `0 ≤ χ ≤ 1`, `tsupport χ ⊆ L ⊆ Ω`.
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ'
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) isOpen_interior hK.isClosed hKL
  have hχL : tsupport χ ⊆ L := by
    rw [tsupport, hχs]
    exact closure_minimal interior_subset hL.isClosed
  have hχc : HasCompactSupport χ := hL.of_isClosed_subset (isClosed_tsupport _) hχL
  -- Step 5: `b = χ b₀`.
  have hbc : HasCompactSupport fun w => χ w • b₀ w := hχc.smul_right
  have hbi : Integrable fun w => χ w • b₀ w :=
    (hχ.continuous.smul hb₀.continuous).integrable_of_hasCompactSupport hbc
  refine ⟨fun w => χ w • b₀ w, hχ.smul hb₀, hbc,
    (tsupport_smul_subset_left _ _).trans (hχL.trans hLΩ), ?_⟩
  -- Step 6: `|c - b| ≤ |1_{Kᶜ} c| + |1_K c - b₀|` pointwise.
  have hptw : ∀ w, ‖c w - χ w • b₀ w‖ ≤ ‖Kᶜ.indicator c w‖ + ‖K.indicator c w - b₀ w‖ := by
    intro w
    by_cases hw : w ∈ K
    · simp [(hχ1 w).1 hw, hw]
    · rw [indicator_of_mem (mem_compl hw), indicator_of_notMem hw, zero_sub, norm_neg]
      obtain ⟨h0, h1⟩ := hχr (mem_range_self w)
      calc ‖c w - χ w • b₀ w‖ ≤ ‖c w‖ + ‖χ w • b₀ w‖ := norm_sub_le _ _
        _ ≤ ‖c w‖ + ‖b₀ w‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
          exact mul_le_of_le_one_left (norm_nonneg _) h1
  -- Step 7: integrate over `Ω`.
  have h1 : ∫ w in Ω, ‖Kᶜ.indicator c w‖ < δ / 2 := by
    simp_rw [norm_indicator_eq_indicator_norm]
    rw [setIntegral_indicator hK.measurableSet.compl, ← sdiff_eq]
    exact htail
  have h2 : ∫ w in Ω, ‖K.indicator c w - b₀ w‖ ≤ δ / 2 :=
    (setIntegral_le_integral (hKi.sub hb₀i).norm
      (Eventually.of_forall fun _ => norm_nonneg _)).trans hb₀K
  calc ∫ w in Ω, ‖c w - χ w • b₀ w‖
      ≤ ∫ w in Ω, (‖Kᶜ.indicator c w‖ + ‖K.indicator c w - b₀ w‖) :=
        setIntegral_mono (hc.sub hbi.integrableOn).norm
          ((hc.indicator hK.measurableSet.compl).norm.add (hKi.sub hb₀i).norm.integrableOn) hptw
    _ = (∫ w in Ω, ‖Kᶜ.indicator c w‖) + ∫ w in Ω, ‖K.indicator c w - b₀ w‖ :=
        integral_add (hc.indicator hK.measurableSet.compl).norm (hKi.sub hb₀i).norm.integrableOn
    _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le h1 h2
    _ = δ := add_halves δ

/-- `C_c^∞(Ω)` is dense in `L¹(Ω)` for real functions: for `Ω ⊆ ℝᵏ` open, `η` integrable on `Ω`
and `ε > 0` there is a smooth `φ` with compact support, `spt φ ⊆ Ω` and `∫_Ω |η − φ| < ε`.  For
`k = 0` the space is a point, so `Ω = ∅` (take `φ = 0`) or `Ω = ℝ⁰` (take `φ = η`, a constant).
For `k ≥ 1` the field `c = η e₀` is approximated by `b` (`slicing_im_ll_gws_smooth_dense`) and
`φ = b₀` is its first coordinate, so `|η − φ| = |(c − b)₀| ≤ |c − b|`. -/
theorem Submission.deformation_ipl_mwc_td_scalar_smooth_dense :
    ∀ (k : ℕ) (Ω : Set (Eucl k)) (η : Eucl k → ℝ), IsOpen Ω → IntegrableOn η Ω (volume : Measure (Eucl k)) → ∀ ε : ℝ, 0 < ε → ∃ φ : Eucl k → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧ ∫ w in Ω, |η w - φ w| ∂(volume : Measure (Eucl k)) < ε := by
  intro k Ω η hΩ hη ε hε
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: `Eucl 0` is a single point, so `Ω = ∅` or `Ω = univ`.
    by_cases hΩe : Ω = ∅
    · subst hΩe
      exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simpa using hε⟩
    · have hΩu : Ω = univ := by
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hΩe
        exact eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      have hconst : η = fun _ => η 0 := funext fun x => congrArg η (Subsingleton.elim x 0)
      refine ⟨η, ?_, ?_, by simp [hΩu], by simpa using hε⟩
      · rw [hconst]
        exact contDiff_const
      · exact subsingleton_of_subsingleton.isCompact.of_isClosed_subset (isClosed_tsupport _)
          (subset_univ _)
  · -- `k ≥ 1`: carry `η` as the first coordinate of a vector field and project back.
    let i₀ : Fin k := ⟨0, hk⟩
    let e : Eucl k := EuclideanSpace.single i₀ (1 : ℝ)
    have he : e i₀ = 1 := by simp [e]
    have hc : IntegrableOn (fun w => η w • e) Ω := hη.smul_const e
    obtain ⟨b, hb, hbc, hbΩ, hbε⟩ :=
      Submission.slicing_im_ll_gws_smooth_dense k Ω (fun w => η w • e) hΩ hc ε hε
    let p : Eucl k →L[ℝ] ℝ := EuclideanSpace.proj i₀
    have hp : ∀ v : Eucl k, p v = v i₀ := fun v => rfl
    have hp0 : p 0 = 0 := map_zero p
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p ∘ b) := p.contDiff.comp hb
    have hφc : HasCompactSupport (p ∘ b) := hbc.comp_left hp0
    refine ⟨p ∘ b, hφ, hφc, (tsupport_comp_subset hp0 b).trans hbΩ, ?_⟩
    have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbc
    have hφi : Integrable (p ∘ b) := hφ.continuous.integrable_of_hasCompactSupport hφc
    -- `|η − φ| = |(c − b)₀| ≤ ‖c − b‖` pointwise, and both sides are integrable on `Ω`.
    have hptw : ∀ w, |η w - (p ∘ b) w| ≤ ‖η w • e - b w‖ := fun w => by
      have h1 : (η w • e - b w) i₀ = η w - (p ∘ b) w := by
        simp [Function.comp, hp, he]
      rw [← h1, ← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ _
    calc ∫ w in Ω, |η w - (p ∘ b) w| ≤ ∫ w in Ω, ‖η w • e - b w‖ :=
          setIntegral_mono (hη.sub hφi.integrableOn).abs (hc.sub hbi.integrableOn).norm hptw
      _ < ε := hbε
/-- Leibniz bound for determinants: if every entry of a real `n × n` matrix satisfies
`|A i j| ≤ c`, then `|det A| ≤ n! · cⁿ`.  Expand `det A = ∑_σ sgn(σ) • ∏_i A (σ i) i`, apply the
triangle inequality, drop the sign `±1`, bound each product of `n` entries by `cⁿ`, and count the
`n!` permutations of `Fin n`. -/
theorem Submission.deformation_ipl_mwc_mil_abs_det_le :
    ∀ (n : ℕ) (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, |A i j| ≤ c) →
      |Matrix.det A| ≤ (n.factorial : ℝ) * c ^ n := by
  intro n c A hA
  rw [Matrix.det_apply]
  calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, |A (σ i) i| := by
        -- `sgn σ = ±1`, and `|·|` is multiplicative on finite products.
        refine Finset.sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
          simp [h, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
        refine Finset.sum_le_sum fun σ _ => ?_
        calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c :=
              Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA _ _)
          _ = c ^ n := by simp
    _ = (n.factorial : ℝ) * c ^ n := by
        simp [Fintype.card_perm]

/-- **Dominated convergence for `h_m · det A_m`.**  If the entries of `A_m(x)` are bounded by
`C`, `|h_m| ≤ H` with `H` integrable for all large `m`, and `h_m → h₀`, `A_m → A₀` entrywise
`μ`-a.e., then `∫ h_m det A_m dμ → ∫ h₀ det A₀ dμ`.  Dominated convergence with the bound
`H · n! Cⁿ` (`deformation_ipl_mwc_mil_abs_det_le`); `det A_m` is a.e.-strongly measurable by
the Leibniz formula and `det` is continuous in the entries. -/
theorem Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (n : ℕ) (C : ℝ) (A : ℕ → Fin n → Fin n → α → ℝ) (A₀ : Fin n → Fin n → α → ℝ) (h : ℕ → α → ℝ) (h₀ H : α → ℝ), (∀ m t s, AEStronglyMeasurable (A m t s) μ) → (∀ m, AEStronglyMeasurable (h m) μ) → Integrable H μ → (∀ m t s x, |A m t s x| ≤ C) → (∀ᶠ m in atTop, ∀ x, |h m x| ≤ H x) → (∀ᵐ x ∂μ, Tendsto (fun m => h m x) atTop (𝓝 (h₀ x))) → (∀ᵐ x ∂μ, ∀ t s, Tendsto (fun m => A m t s x) atTop (𝓝 (A₀ t s x))) → Tendsto (fun m => ∫ x, h m x * Matrix.det (Matrix.of fun t s => A m t s x) ∂μ) atTop (𝓝 (∫ x, h₀ x * Matrix.det (Matrix.of fun t s => A₀ t s x) ∂μ)) := by
  intro α _ μ n C A A₀ h h₀ H hAm hhm hH hAb hhb hhl hAl
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => H x * ((n.factorial : ℝ) * C ^ n)) ?_ ?_ (hH.mul_const _) ?_
  · -- Leibniz: `det A_m(x) = ∑_σ sgn σ ∏_i A_m(σ i, i, x)`, finite sums and products of
    -- a.e.-strongly measurable functions.
    refine Eventually.of_forall fun m => (hhm m).mul ?_
    have hdet : (fun x => Matrix.det (Matrix.of fun t s => A m t s x)) =
        fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A m (σ i) i x := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [hdet]
    refine Finset.aestronglyMeasurable_fun_sum _ fun σ _ => ?_
    exact aestronglyMeasurable_const.mul
      (Finset.aestronglyMeasurable_fun_prod _ fun i _ => hAm m _ _)
  · -- `|h_m(x) det A_m(x)| ≤ H(x) · n! Cⁿ` for every `x`, once `|h_m| ≤ H`.
    filter_upwards [hhb] with m hm
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hm x)
      (Submission.deformation_ipl_mwc_mil_abs_det_le n C _ fun t s => hAb m t s x)
      (abs_nonneg _) ((abs_nonneg _).trans (hm x))
  · -- Entrywise convergence gives `A_m(x) → A₀(x)` in the product topology; `det` is continuous.
    filter_upwards [hhl, hAl] with x hx1 hx2
    refine hx1.mul ?_
    have hc : Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := continuous_id.matrix_det
    exact (hc.tendsto _).comp (tendsto_pi_nhds.2 fun t => tendsto_pi_nhds.2 fun s => hx2 t s)
/-- A.e. derivative of a coordinate of a Lipschitz map (the Rademacher step of the Lipschitz
minor integration by parts in the proof of Simon Ch. 6, 3.9): if `v : ℝᵏ → ℝ^Q` is `C`-Lipschitz
on an open `Ω` and `g = v^c := proj_c ∘ v` on `Ω`, then for Lebesgue-a.e. `w ∈ Ω`,
`Dg(w) x = proj_c (Dv(w) x)` for every `x`.  By Rademacher's theorem `v` is differentiable within
`Ω` at a.e. `w ∈ Ω`, hence at `w` as `Ω` is open; `g` and `v^c` agree near `w`, so they have the
same `fderiv`, which is `proj_c ∘L Dv(w)` by the chain rule.  No regularity of `g` is needed. -/
theorem Submission.deformation_ipl_mwc_mil_ae_fderiv_eq_proj :
    ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : Eucl k → Eucl Q) (c : Fin Q)
      (g : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω →
      EqOn g (fun w => EuclideanSpace.proj c (v w)) Ω →
      ∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → ∀ x : Eucl k,
        fderiv ℝ g w x = EuclideanSpace.proj c (fderiv ℝ v w x) := by
  intro k Q Ω C v c g hΩ hv hg
  -- Rademacher's theorem on `Ω`: `v` is differentiable within `Ω` at a.e. `w ∈ Ω`.
  filter_upwards [hv.ae_differentiableWithinAt_of_mem (μ := volume)] with w hw hwΩ x
  -- `Ω` is a neighbourhood of `w`, so `v` is differentiable at `w` and `g = proj_c ∘ v` near `w`.
  have hd : DifferentiableAt ℝ v w := (hw hwΩ).differentiableAt (hΩ.mem_nhds hwΩ)
  have heq : g =ᶠ[𝓝 w] (fun w => EuclideanSpace.proj c (v w)) :=
    eventuallyEq_of_mem (hΩ.mem_nhds hwΩ) hg
  -- Chain rule for the continuous linear map `proj_c`.
  have hcomp : HasFDerivAt (fun w => EuclideanSpace.proj c (v w))
      ((EuclideanSpace.proj c).comp (fderiv ℝ v w)) w :=
    (EuclideanSpace.proj c : Eucl Q →L[ℝ] ℝ).hasFDerivAt.comp w hd.hasFDerivAt
  -- Locality of `fderiv`: `Dg(w) = D(proj_c ∘ v)(w) = proj_c ∘L Dv(w)`.
  rw [heq.fderiv_eq, hcomp.fderiv]
  rfl
/-- **A directional derivative of a compactly supported `C¹` function has integral `0`.**  For
`h : ℝᵏ → ℝ` of class `C¹` with compact support and `e ∈ ℝᵏ`, `∫ Dh(w)(e) dw = 0`, where
`Dh(w) = fderiv ℝ h w`.  `h` is Lipschitz, so integration by parts for Lipschitz functions against
the constant function `1` gives `∫ ∂ₑ1 · h = ∫ ∂₋ₑh · 1`.  The left side vanishes and, `h` being
differentiable, `∂₋ₑh(w) = Dh(w)(-e) = -Dh(w)(e)`, so the right side is `-∫ Dh(w)(e) dw`. -/
theorem Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero :
    ∀ (k : ℕ) (h : Eucl k → ℝ) (e : Eucl k), ContDiff ℝ 1 h → HasCompactSupport h →
      ∫ w, fderiv ℝ h w e ∂(volume : Measure (Eucl k)) = 0 := by
  intro k h e hh hcs
  -- `h` is Lipschitz; integrate by parts against the constant function `1`.
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hh one_ne_zero
  have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Eucl k)))
    (LipschitzWith.const (α := Eucl k) (1 : ℝ)) hD hcs e
  -- Both functions are differentiable, so their line derivatives are Fréchet derivatives.
  have h1 : ∀ w, lineDeriv ℝ (fun _ : Eucl k => (1 : ℝ)) w e = 0 := fun w => by
    rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
    simp
  have h2 : ∀ w, lineDeriv ℝ h w (-e) = -fderiv ℝ h w e := fun w => by
    rw [((hh.differentiable one_ne_zero) w).lineDeriv_eq_fderiv]
    simp
  simp only [h1, h2, zero_mul, integral_zero, mul_one, integral_neg] at key
  linarith
/-- **The determinant of a matrix of `C^m` functions is `C^m`.**  Let `M t s : ℝᵏ → ℝ`
(`t, s : Fin n`) be `C^m` for some `m : WithTop ℕ∞` (finite, `∞` or `ω`).  Then
`w ↦ det (M t s w)ₜₛ` is `C^m`.  By the Leibniz formula `det A = ∑_σ sign σ · ∏ᵢ A (σ i) i`, this
function is a finite sum, over the permutations `σ` of `Fin n`, of constant multiples of finite
products of entries (for `n = 0` it is the constant `1`). -/
theorem Submission.deformation_ipl_mwc_mis_det_contDiff :
    ∀ (k n : ℕ) (m : WithTop ℕ∞) (M : Fin n → Fin n → Eucl k → ℝ),
      (∀ t s, ContDiff ℝ m (M t s)) →
        ContDiff ℝ m (fun w => Matrix.det (Matrix.of fun t s : Fin n => M t s w)) := by
  intro k n m M hM
  -- Leibniz formula: `det (M t s w)ₜₛ = ∑_σ sign σ * ∏ᵢ M (σ i) i w`.
  simp only [Matrix.det_apply', Matrix.of_apply]
  -- Each summand is a constant times a finite product of `C^m` entries.
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hM _ _
/-- Signed first-row cofactors as restricted Leibniz sums: `(-1)^q` times the minor of the
`r × (r + 1)` array `N` with column `q` deleted is the sum of `sgn σ * ∏ t, N t (σ t.succ)` over
the permutations `σ` of `Fin (r + 1)` with `σ 0 = q`.  Both sides are the determinant of the
matrix with row `0` equal to `Pi.single q 1` and row `t.succ` equal to `N t`. -/
theorem Submission.deformation_ipl_mwc_pi_cofactor_leibniz : ∀ (r : ℕ) (N : Fin r → Fin (r + 1) → ℝ) (q : Fin (r + 1)), (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) = ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
  intro r N q
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := Matrix.of (Matrix.vecCons (Pi.single q 1) N)
  -- Laplace expansion along row `0`: only the column `j = q` survives.
  have h1 : A.det = (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single q]
    · have hsub : A.submatrix Fin.succ q.succAbove =
          Matrix.of fun t s : Fin r => N t (q.succAbove s) := by
        ext t s
        simp [A]
      rw [hsub]
      simp [A]
    · intro j _ hj
      simp [A, hj]
    · intro h
      exact absurd (Finset.mem_univ q) h
  -- Leibniz formula for `Aᵀ`: the row-`0` factor `Pi.single q 1 (σ 0)` selects `σ 0 = q`.
  have h2 : A.det = ∑ σ : Equiv.Perm (Fin (r + 1)),
      (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [A, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Pi.single_apply]
    split_ifs <;> ring
  rw [← h1, h2]
/-- Schwarz symmetry of mixed directional second derivatives of a `C²` function on `ℝ^k`:
`∂_v (∂_u f)(x) = ∂_u (∂_v f)(x)`. -/
theorem Submission.deformation_ipl_mwc_pi_hessian_symm :
    ∀ (k : ℕ) (f : Eucl k → ℝ), ContDiff ℝ 2 f → ∀ x u v : Eucl k,
      fderiv ℝ (fun y : Eucl k => fderiv ℝ f y u) x v =
        fderiv ℝ (fun y : Eucl k => fderiv ℝ f y v) x u := by
  intro k f hf x u v
  -- `Df` is `C¹`, hence differentiable at `x`; by Schwarz, `D²f(x)` is symmetric.
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := (h1.differentiable (by norm_num)) x
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  -- Differentiating `y ↦ Df(y) u` at `x` in direction `v` gives `D²f(x) v u`.
  rw [fderiv_clm_apply hd (differentiableAt_const u),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa using hs v u
/-- Product rule for a weighted sum of finite products: if every `g i t` is differentiable at
`w`, the derivative of `x ↦ ∑ i, a i * ∏ t, g i t x` at `w` in direction `v` is
`∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ≠ u, g i t w`. -/
theorem Submission.deformation_ipl_mwc_pi_fderiv_sum_prod : ∀ (k r : ℕ) (ι : Type) [Fintype ι] (a : ι → ℝ) (g : ι → Fin r → Eucl k → ℝ) (w v : Eucl k), (∀ i t, DifferentiableAt ℝ (g i t) w) → fderiv ℝ (fun x : Eucl k => ∑ i, a i * ∏ t, g i t x) w v = ∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ∈ Finset.univ.erase u, g i t w := by
  intro k r ι _ a g w v hg
  -- Product rule for each `∏ t, g i t`, then the constant factor `a i` and the sum over `ι`.
  have hs : HasFDerivAt (fun x => ∑ i, a i * ∏ t, g i t x)
      (∑ i, a i • ∑ u, (∏ t ∈ Finset.univ.erase u, g i t w) • fderiv ℝ (g i u) w) w :=
    HasFDerivAt.fun_sum fun i _ =>
      (HasFDerivAt.finsetProd fun t _ => (hg i t).hasFDerivAt).const_mul (a i)
  -- Evaluate the derivative at `v` termwise and commute the real factors.
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  ring
/-- Algebraic core of the Piola identity: an alternating sum over permutations against a kernel
`H u` symmetric in its two arguments vanishes, since `σ ↦ σ * swap 0 u.succ` reverses the sign,
exchanges the two arguments of `H u` and fixes every other factor. -/
theorem Submission.deformation_ipl_mwc_pi_swap_cancel : ∀ (r : ℕ) (H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ) (N : Fin r → Fin (r + 1) → ℝ), (∀ u i j, H u i j = H u j i) → ∑ σ : Equiv.Perm (Fin (r + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ u : Fin r, H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) = 0 := by
  intro r H N hH
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  -- Pair `σ` with `σ * τ`, `τ = (0 u.succ)`; the terms `T σ` and `T (σ * τ)` cancel.
  let τ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 u.succ
  have hτne : (0 : Fin (r + 1)) ≠ u.succ := (Fin.succ_ne_zero u).symm
  let T : Equiv.Perm (Fin (r + 1)) → ℝ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * (H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ))
  have hT : ∀ σ : Equiv.Perm (Fin (r + 1)), T (σ * τ) = - T σ := by
    intro σ
    have h0 : (σ * τ) 0 = σ u.succ := by simp [τ, Equiv.Perm.mul_apply]
    have h1 : (σ * τ) u.succ = σ 0 := by simp [τ, Equiv.Perm.mul_apply]
    have hprod : ∏ t ∈ Finset.univ.erase u, N t ((σ * τ) t.succ) =
        ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) := by
      refine Finset.prod_congr rfl (fun t ht => ?_)
      have htu : t ≠ u := Finset.ne_of_mem_erase ht
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero t)
        (fun h => htu (Fin.succ_injective _ h))]
    have hsign : ((Equiv.Perm.sign (σ * τ) : ℤ) : ℝ) = - ((Equiv.Perm.sign σ : ℤ) : ℝ) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hτne]
      push_cast
      ring
    simp only [T]
    rw [h0, h1, hprod, hsign, hH u (σ u.succ) (σ 0)]
    ring
  have hS : ∑ σ, T σ = - ∑ σ, T σ :=
    calc ∑ σ, T σ = ∑ σ, T (σ * τ) := (Equiv.sum_comp (Equiv.mulRight τ) T).symm
      _ = ∑ σ, - T σ := Finset.sum_congr rfl (fun σ _ => hT σ)
      _ = - ∑ σ, T σ := Finset.sum_neg_distrib _
  linarith

/-- Piola identity (step (3.2)(i) of the proof of `minor_weak_continuity`; Evans, PDE, §8.1.4(b),
Lemma 1): for `C²` functions `W_0, …, W_{r-1}` on `ℝ^k` and `b : Fin (r + 1) → Fin k`, the signed
minors `c_q = (-1)^q det (∂_{b (q.succAbove s)} W_t)_{t,s}` satisfy `∑_q ∂_{b q} c_q = 0`.
By the cofactor formula `c_q = ∑_{σ 0 = q} sgn σ ∏_t ∂_{b (σ t.succ)} W_t` and the product rule,
`∑_q ∂_{b q} c_q = ∑_σ sgn σ ∑_u H_u(σ 0, σ u.succ) ∏_{t ≠ u} ∂_{b (σ t.succ)} W_t` with
`H_u(i, j) = ∂_{b i} ∂_{b j} W_u`; this vanishes since `H_u` is symmetric (Schwarz) and
`σ ↦ σ * swap 0 u.succ` changes the sign. -/
theorem Submission.deformation_ipl_mwc_piola_identity :
    ∀ (k r : ℕ) (W : Fin r → Eucl k → ℝ) (b : Fin (r + 1) → Fin k), (∀ t, ContDiff ℝ 2 (W t)) →
      ∀ w : Eucl k, ∑ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w
          (EuclideanSpace.single (b q) 1) = 0 := by
  intro k r W b hW w
  -- `D t i x = ∂_{b i} W_t (x)`, the entries of the minors; `C¹` since `W_t` is `C²`.
  let D : Fin r → Fin (r + 1) → Eucl k → ℝ := fun t i x =>
    fderiv ℝ (W t) x (EuclideanSpace.single (b i) 1)
  have hD : ∀ t i, DifferentiableAt ℝ (D t i) w := fun t i =>
    (((hW t).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero w).clm_apply
      (differentiableAt_const _)
  -- `H u i j = ∂_{b i} ∂_{b j} W_u (w)` is symmetric in `(i, j)`.
  let H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ := fun u i j =>
    fderiv ℝ (D u j) w (EuclideanSpace.single (b i) 1)
  have hH : ∀ u i j, H u i j = H u j i := fun u i j =>
    Submission.deformation_ipl_mwc_pi_hessian_symm k (W u) (hW u) w
      (EuclideanSpace.single (b j) 1) (EuclideanSpace.single (b i) 1)
  -- Cofactor formula and product rule: `∂_{b q} c_q = ∑_{σ 0 = q} sgn σ ∂_{b q} ∏_t D t (σ t.succ)`
  have hc : ∀ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w
        (EuclideanSpace.single (b q) 1) =
      ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) *
        ∑ u : Fin r, H u q (σ u.succ) * ∏ t ∈ Finset.univ.erase u, D t (σ t.succ) w := by
    intro q
    have hcof : (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) =
        fun x => ∑ σ : Equiv.Perm (Fin (r + 1)),
          (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, D t (σ t.succ) x :=
      funext fun x => Submission.deformation_ipl_mwc_pi_cofactor_leibniz r (fun t i => D t i x) q
    rw [hcof]
    exact Submission.deformation_ipl_mwc_pi_fderiv_sum_prod k r (Equiv.Perm (Fin (r + 1)))
      (fun σ => if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0)
      (fun σ t => D t (σ t.succ)) w _ fun σ t => hD t (σ t.succ)
  -- Sum over `q`: only `q = σ 0` survives, and the sum cancels in pairs `σ, σ * swap 0 u.succ`.
  refine Eq.trans ?_
    (Submission.deformation_ipl_mwc_pi_swap_cancel r H (fun t i => D t i w) hH)
  rw [Fintype.sum_congr _ _ hc, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun σ => ?_
  rw [Finset.sum_eq_single (σ 0) (fun q _ hq => by rw [ite_eq_right (Ne.symm hq), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- Integration by parts for Jacobian minors of `C²` functions (step (3.2)(ii) of the weak
continuity of Jacobian minors behind the Lipschitz push-forward limits in the proof of the
Deformation Theorem, Simon Ch. 6, 5.1): for `C²` functions `V₀, …, V_r : ℝᵏ → ℝ`, directions
`b : Fin (r + 1) → Fin k` and `φ ∈ C¹_c(ℝᵏ)`, with
`A = (∂_{b(s)} V_t)_{t,s}` and the signed first-row cofactors
`C_q = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1})_{t,s}`, `∫ φ det A = -∑_q ∫ V₀ C_q ∂_{b(q)} φ`.
Laplace expansion along row `0` gives `det A = ∑_q ∂_{b(q)} V₀ · C_q`.  The directional derivative
`∂_{b(q)}(V₀ φ C_q)` of the compactly supported `C¹` function `V₀ φ C_q` has integral `0`, and the
product rule turns this into `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`.
Summing over `q`, the last terms cancel by the Piola identity `∑_q ∂_{b(q)} C_q = 0`. -/
theorem Submission.deformation_ipl_mwc_minor_ibp_smooth :
    ∀ (k r : ℕ) (V : Fin (r + 1) → Eucl k → ℝ) (b : Fin (r + 1) → Fin k) (φ : Eucl k → ℝ),
      (∀ t, ContDiff ℝ 2 (V t)) → ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
          fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k)) =
        -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) *
          Matrix.det (Matrix.of fun t s : Fin r =>
            fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
          fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
  intro k r V b φ hV hφ hφc
  -- `C q w = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1}(w))_{t,s}`: the signed first-row cofactors.
  obtain ⟨C, hC⟩ : ∃ C : Fin (r + 1) → Eucl k → ℝ, ∀ q w, C q w = (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1)) :=
    ⟨_, fun _ _ => rfl⟩
  have hCf : ∀ q, C q = fun w => (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1)) :=
    fun q => funext (hC q)
  -- Step 1 (Laplace expansion along row `0`): `det A = ∑_q ∂_{b(q)} V₀ · C_q`.
  have hLap : ∀ w, Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
      fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) =
      ∑ q, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * C q w := by
    intro w
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hC q w, Matrix.of_apply]
    have hsub : (Matrix.of fun t s : Fin (r + 1) =>
        fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)).submatrix Fin.succ q.succAbove =
        Matrix.of fun t s : Fin r =>
          fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1) := rfl
    rw [hsub]
    ring
  -- Step 2 (regularity): the entries `∂_i V_t` and, by the Leibniz formula, the cofactors `C_q`
  -- are `C¹`.
  have hDV : ∀ t i, ContDiff ℝ 1 fun w => fderiv ℝ (V t) w (EuclideanSpace.single i 1) :=
    fun t i => ((hV t).fderiv_right (m := 1) one_add_one_eq_two.le).clm_apply contDiff_const
  have hV0 : ContDiff ℝ 1 (V 0) := (hV 0).of_le one_le_two
  have hCd : ∀ q, ContDiff ℝ 1 (C q) := by
    intro q
    rw [hCf q]
    exact contDiff_const.mul (Submission.deformation_ipl_mwc_mis_det_contDiff k r 1
      (fun t s w => fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      fun t s => hDV t.succ _)
  -- Step 3 (supports and integrability): `φ` and `Dφ` vanish off the compact set `tsupport φ`,
  -- so every continuous integrand below with a factor `φ` or `∂_i φ` is integrable.
  have hφ0 : ∀ w, w ∉ tsupport φ → φ w = 0 := fun w hw => image_eq_zero_of_notMem_tsupport hw
  have hdφ0 : ∀ w, w ∉ tsupport φ → fderiv ℝ φ w = 0 :=
    fun w hw => fderiv_of_notMem_tsupport ℝ hw
  have hcs : ∀ g : Eucl k → ℝ, (∀ w, w ∉ tsupport φ → g w = 0) → HasCompactSupport g := by
    intro g hg0
    refine hφc.mono' fun w hw => ?_
    by_contra hw'
    exact (Function.mem_support.mp hw) (hg0 w hw')
  have hint : ∀ g : Eucl k → ℝ, Continuous g → (∀ w, w ∉ tsupport φ → g w = 0) →
      Integrable g (volume : Measure (Eucl k)) :=
    fun g hg hg0 => hg.integrable_of_hasCompactSupport (hcs g hg0)
  have hcDφ : ∀ i, Continuous fun w => fderiv ℝ φ w (EuclideanSpace.single i 1) :=
    fun i => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDC : ∀ q i, Continuous fun w => fderiv ℝ (C q) w (EuclideanSpace.single i 1) :=
    fun q i => ((hCd q).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hT1 : ∀ q, Integrable (fun w => fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) *
      φ w * C q w) (volume : Measure (Eucl k)) := fun q =>
    hint _ (((hDV 0 _).continuous.mul hφ.continuous).mul (hCd q).continuous)
      fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul]
  have hT2 : ∀ q, Integrable (fun w => V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) *
      C q w) (volume : Measure (Eucl k)) := fun q =>
    hint _ ((hV0.continuous.mul (hcDφ _)).mul (hCd q).continuous)
      fun w hw => by rw [hdφ0 w hw, zero_apply, mul_zero, zero_mul]
  have hT3 : ∀ q, Integrable (fun w => V 0 w * φ w *
      fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1)) (volume : Measure (Eucl k)) := fun q =>
    hint _ ((hV0.continuous.mul hφ.continuous).mul (hcDC q _))
      fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul]
  -- Product rule for `V₀ φ C_q` in the direction `e_{b(q)}`.
  have hprod : ∀ q w, fderiv ℝ (fun y => V 0 y * φ y * C q y) w (EuclideanSpace.single (b q) 1) =
      fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w +
        V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w +
        V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
    intro q w
    have hd : HasFDerivAt (fun y => V 0 y * φ y * C q y)
        ((V 0 w * φ w) • fderiv ℝ (C q) w +
          C q w • (V 0 w • fderiv ℝ φ w + φ w • fderiv ℝ (V 0) w)) w :=
      ((hV0.differentiable one_ne_zero w).hasFDerivAt.mul
        (hφ.differentiable one_ne_zero w).hasFDerivAt).mul
        ((hCd q).differentiable one_ne_zero w).hasFDerivAt
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- Steps 4–5 (one integration by parts for each `q`): `∫ ∂_{b(q)}(V₀ φ C_q) = 0`, so
  -- `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`.
  have hq : ∀ q, ∫ w, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w =
      -(∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
        ∫ w, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
    intro q
    have h0 := Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero k
      (fun y => V 0 y * φ y * C q y) (EuclideanSpace.single (b q) 1) ((hV0.mul hφ).mul (hCd q))
      (hcs _ fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul])
    simp only [hprod q] at h0
    have h12 : Integrable (fun w => fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w +
        V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w)
        (volume : Measure (Eucl k)) := (hT1 q).add (hT2 q)
    rw [integral_add h12 (hT3 q), integral_add (hT1 q) (hT2 q)] at h0
    linarith
  -- Step 6 (Piola identity for the rows `W_t = V_{t+1}`): `∑_q ∂_{b(q)} C_q = 0`.
  have hdivC : ∀ w, ∑ q, fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) = 0 := by
    intro w
    simp only [hCf]
    exact Submission.deformation_ipl_mwc_piola_identity k r (fun t => V t.succ) b
      (fun t => hV t.succ) w
  calc ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
          fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k))
      = ∫ w, ∑ q, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w := by
        refine integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [hLap w, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ q, ∫ w, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w :=
        integral_finsetSum _ fun q _ => hT1 q
    _ = ∑ q, (-(∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
          ∫ w, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1)) :=
        Finset.sum_congr rfl fun q _ => hq q
    _ = -(∑ q, ∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
          ∫ w, ∑ q, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
        rw [integral_finsetSum _ fun q _ => hT3 q, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    _ = -∑ q, ∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w := by
        simp only [← Finset.mul_sum, hdivC, mul_zero, integral_zero, sub_zero]
    _ = -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) *
          Matrix.det (Matrix.of fun t s : Fin r =>
            fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
          fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
        congr 1
        refine Finset.sum_congr rfl fun q _ => integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [hC q w]
        ring
/-- A smooth approximate identity on `ℝⁿ` (Simon Ch. 6, proof of 2.34, p. 143; Ch. 2, §2):
`ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)` for a smooth bump `0 ≤ h ≤ 1` with `h(0) = 1`,
`spt h ⊆ B_1(0)` and `I = ∫ h > 0`.  Each `ψ_k` is `C^∞`, nonnegative, of integral `1` and
supported in `B̄_{1/(k+1)}(0)`, and `0 ≤ ψ_k ≤ (k+1)ⁿ I⁻¹`.  For locally integrable `g` and every
Lebesgue point `x` of `g` (Simon Ch. 1, 3.17), `|(g ∗ ψ_k)(x) − g(x)| ≤ I⁻¹ Lⁿ(B_1(0)) ·
⨍_{B̄_{1/(k+1)}(x)} |g − g(x)| → 0`, so `g ∗ ψ_k → g` almost everywhere. -/
theorem Submission.constancy_mdc_smooth_approx_identity_ae_tendsto :
    ∀ n : ℕ, ∃ ψ : ℕ → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k : ℕ, tsupport (ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1))) ∧ (∀ k y, 0 ≤ ψ k y) ∧
      (∀ k, ∫ y, ψ k y ∂volume = 1) ∧
      ∀ g : Eucl n → ℝ, LocallyIntegrable g volume → ∀ᵐ x ∂volume,
        Tendsto (fun k => convolution g (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop
          (𝓝 (g x)) := by
  intro n
  -- A smooth bump `h` with `0 ≤ h ≤ 1`, `h 0 = 1` and `spt h ⊆ B_1(0)`; `I = ∫ h > 0`.
  obtain ⟨h, hts, hhc, hhs, hrange, h0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ball_mem_nhds (0 : Eucl n) one_pos)
  have hh0 : ∀ y, 0 ≤ h y := fun y => (hrange ⟨y, rfl⟩).1
  have hh1 : ∀ y, h y ≤ 1 := fun y => (hrange ⟨y, rfl⟩).2
  have hhcont : Continuous h := hhs.continuous
  have hhint : Integrable h volume := hhcont.integrable_of_hasCompactSupport hhc
  have hIpos : 0 < ∫ y, h y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => hh0 y) hhint]
    exact hhcont.isOpen_support.measure_pos volume ⟨0, by simp [Function.mem_support, h0]⟩
  set I := ∫ y, h y with hI
  have hzero : ∀ y : Eucl n, 1 ≤ ‖y‖ → h y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have := hts hy'
    rw [mem_ball, dist_zero_right] at this
    linarith
  -- The kernels `ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)`.
  have hs : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  set Ψ : ℕ → Eucl n → ℝ := fun k y => ((k : ℝ) + 1) ^ n * (I⁻¹ * h (((k : ℝ) + 1) • y))
    with hΨ
  have hΨsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ k) := fun k =>
    contDiff_const.mul (contDiff_const.mul (hhs.comp (contDiff_const_smul _)))
  have hΨzero : ∀ (k : ℕ) (y : Eucl n), 1 / ((k : ℝ) + 1) ≤ ‖y‖ → Ψ k y = 0 := by
    intro k y hy
    have h1 : 1 ≤ ‖((k : ℝ) + 1) • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hs k).le]
      rw [div_le_iff₀ (hs k)] at hy
      linarith
    simp only [hΨ, hzero _ h1, mul_zero]
  have hΨsupp : ∀ k : ℕ, tsupport (Ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1)) := by
    intro k
    refine closure_minimal ?_ isClosed_closedBall
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    exact hy (hΨzero k y hlt.le)
  have hΨc : ∀ k, HasCompactSupport (Ψ k) := fun k =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport _).trans (hΨsupp k))
  have hΨnn : ∀ k y, 0 ≤ Ψ k y := fun k y => by
    have := hh0 (((k : ℝ) + 1) • y)
    have := (hs k).le
    have := inv_nonneg.2 hIpos.le
    simp only [hΨ]
    positivity
  have hΨle : ∀ k y, Ψ k y ≤ ((k : ℝ) + 1) ^ n * I⁻¹ := fun k y => by
    simp only [hΨ]
    have hp : 0 ≤ ((k : ℝ) + 1) ^ n := by positivity
    have hIi : 0 ≤ I⁻¹ := inv_nonneg.2 hIpos.le
    have := hh1 (((k : ℝ) + 1) • y)
    calc ((k : ℝ) + 1) ^ n * (I⁻¹ * h (((k : ℝ) + 1) • y))
        ≤ ((k : ℝ) + 1) ^ n * (I⁻¹ * 1) := by gcongr
      _ = _ := by ring
  have hΨint : ∀ k, Integrable (Ψ k) volume := fun k =>
    (hΨsmooth k).continuous.integrable_of_hasCompactSupport (hΨc k)
  -- `∫ ψ_k = (k+1)ⁿ I⁻¹ (k+1)⁻ⁿ ∫ h = 1` by the linear change of variables `y ↦ (k+1) y`.
  have hΨone : ∀ k, ∫ y, Ψ k y = 1 := by
    intro k
    simp only [hΨ]
    rw [integral_const_mul, integral_const_mul, Measure.integral_comp_smul,
      finrank_euclideanSpace_fin]
    rw [smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < (((k : ℝ) + 1) ^ n)⁻¹), ← hI]
    field_simp
  refine ⟨Ψ, hΨsmooth, hΨc, hΨsupp, hΨnn, hΨone, ?_⟩
  intro g hg
  -- Lebesgue points: `⨍_{B̄_r(x)} |g − g(x)| → 0` as `r ↓ 0`, for a.e. `x`.
  have hleb :=
    IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Eucl n)) hg 1
  filter_upwards [hleb] with x hx
  set r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k, 0 < r k := fun k => by simp only [hr]; positivity
  have hrlim : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => hrpos k⟩
  have havg := hx (fun _ => x) r hrlim (Eventually.of_forall fun k => by
    rw [one_mul]; exact mem_closedBall_self (hrpos k).le)
  set ω := (volume : Measure (Eucl n)).real (ball 0 1) with hω
  have hωpos : 0 < ω := by
    rw [hω, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set C := I⁻¹ * ω with hC
  -- `|(g ∗ ψ_k)(x) − g(x)| ≤ C ⨍_{B̄_{1/(k+1)}(x)} |g − g(x)|` with `C = I⁻¹ Lⁿ(B_1(0))`.
  have hbound : ∀ k, ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ ≤
      C * ⨍ y in closedBall x (r k), ‖g y - g x‖ := by
    intro k
    set K := closedBall x (r k) with hK
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hconv : Integrable (fun t => g t * Ψ k (x - t)) volume := by
      have := (hΨc k).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hg
        (hΨsmooth k).continuous x
      simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using this
    have hconst : Integrable (fun t => g x * Ψ k (x - t)) volume :=
      ((hΨint k).comp_sub_left x).const_mul (g x)
    have hgx : g x = ∫ t, g x * Ψ k (x - t) := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun y => Ψ k y) volume x, hΨone k,
        mul_one]
    have hdiff : convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x =
        ∫ t, (g t - g x) * Ψ k (x - t) := by
      rw [convolution_def]
      conv_lhs => rw [hgx]
      rw [← integral_sub _ hconst]
      · congr 1
        funext t
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        ring
      · simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hconv
    have hoff : ∀ t, t ∉ K → ‖g t - g x‖ * Ψ k (x - t) = 0 := by
      intro t ht
      rw [hK, mem_closedBall, not_le, dist_eq_norm, ← norm_neg, neg_sub] at ht
      rw [hΨzero k (x - t) ht.le, mul_zero]
    have hgK : IntegrableOn g K volume := hg.integrableOn_isCompact hKc
    have hgxK : IntegrableOn (fun t => ‖g t - g x‖) K volume :=
      (hgK.sub (integrableOn_const (hKc.measure_lt_top.ne))).norm
    calc ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖
        = ‖∫ t, (g t - g x) * Ψ k (x - t)‖ := by rw [hdiff]
      _ ≤ ∫ t, ‖(g t - g x) * Ψ k (x - t)‖ := norm_integral_le_integral_norm _
      _ = ∫ t, ‖g t - g x‖ * Ψ k (x - t) := by
          congr 1
          funext t
          rw [norm_mul, Real.norm_of_nonneg (hΨnn k _)]
      _ = ∫ t in K, ‖g t - g x‖ * Ψ k (x - t) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
      _ ≤ ∫ t in K, ‖g t - g x‖ * (((k : ℝ) + 1) ^ n * I⁻¹) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hgxK.mul_const _)
            (Eventually.of_forall fun t => ?_)
          · exact mul_nonneg (norm_nonneg _) (hΨnn k _)
          · exact mul_le_mul_of_nonneg_left (hΨle k _) (norm_nonneg _)
      _ = (∫ t in K, ‖g t - g x‖) * (((k : ℝ) + 1) ^ n * I⁻¹) := integral_mul_const _ _
      _ = C * ⨍ y in K, ‖g y - g x‖ := by
          rw [setAverage_eq, smul_eq_mul, hC]
          have hKvol : (volume : Measure (Eucl n)).real K = r k ^ n * ω := by
            rw [measureReal_def, hK, Measure.addHaar_closedBall _ _ (hrpos k).le,
              finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
              hω, measureReal_def]
          rw [hKvol]
          simp only [hr]
          field_simp
          rw [mul_assoc, ← mul_pow, mul_one_div_cancel (hs k).ne', one_pow, mul_one]
  -- Squeeze: `0 ≤ |(g ∗ ψ_k)(x) − g(x)| ≤ C ⨍ … → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  simpa using havg.const_mul C
/-- Differentiation under the integral sign for the mollification of a globally Lipschitz `F`
by a continuous compactly supported `ρ`: `D(∫ ρ(y) F(· - y) dy)(x) = ∫ ρ(y) DF(x - y) dy`.
By Rademacher's theorem and the invariance of Lebesgue measure under `y ↦ x - y`, `F` is
differentiable at `x - y` for a.e. `y`; `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz on `ℝ^P`
with integrable majorant `L |ρ|`, so `hasFDerivAt_integral_of_dominated_loc_of_lip` applies
with `s = ℝ^P`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt :
    ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ ρ : Eucl P → ℝ, Continuous ρ →
      HasCompactSupport ρ → ∀ x : Eucl P,
        HasFDerivAt (fun x' : Eucl P => ∫ y, ρ y * F (x' - y))
          (∫ y, ρ y • fderiv ℝ F (x - y)) x := by
  intro P F L hF ρ hρc hρs x
  -- Rademacher, pulled back along the measure-preserving map `y ↦ x - y`.
  have hae : ∀ᵐ y : Eucl P, DifferentiableAt ℝ F (x - y) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      hF.ae_differentiableAt
  -- `y ↦ ρ(y) F(x' - y)` is continuous for every `x'`.
  have hcont : ∀ x' : Eucl P, Continuous fun y : Eucl P => ρ y * F (x' - y) := fun x' =>
    hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))
  -- `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz for every `y`.
  have hlip : ∀ y : Eucl P,
      LipschitzOnWith (Real.nnabs (L * |ρ y|)) (fun x' : Eucl P => ρ y * F (x' - y)) univ := by
    refine fun y => (LipschitzWith.of_dist_le_mul fun a b => ?_).lipschitzOnWith
    calc dist (ρ y * F (a - y)) (ρ y * F (b - y)) = |ρ y| * dist (F (a - y)) (F (b - y)) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      _ ≤ |ρ y| * (L * dist (a - y) (b - y)) := by gcongr; exact hF.dist_le_mul _ _
      _ = Real.nnabs (L * |ρ y|) * dist a b := by
          rw [dist_sub_right, Real.coe_nnabs, abs_mul, abs_abs, NNReal.abs_eq]; ring
  -- For a.e. `y`, the chain rule gives the derivative `ρ(y) DF(x - y)` at `x`.
  have hderiv : ∀ᵐ y : Eucl P,
      HasFDerivAt (fun x' : Eucl P => ρ y * F (x' - y)) (ρ y • fderiv ℝ F (x - y)) x := by
    filter_upwards [hae] with y hy
    have h := hy.hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_mul (ρ y)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip univ_mem
    (Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable)
    ((hcont x).integrable_of_hasCompactSupport hρs.mul_right)
    (hρc.measurable.smul ((measurable_fderiv ℝ F).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall hlip)
    ((hρc.abs.integrable_of_hasCompactSupport hρs.abs).const_mul _) hderiv).2
/-- **Uniform error of a mollified Lipschitz function** (Simon Ch. 6, 4.11, p. 158: "use
`f^{(σ)}` in place of `f`").  If `F` is `L`-Lipschitz and `ρ ≥ 0` is continuous with compact
support, `ρ(y) = 0` for `|y| ≥ σ` and `∫ ρ = 1`, then `|∫ ρ(y) F(x − y) dy − F(x)| ≤ L σ`.
As `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`, and pointwise
`|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L |y| ≤ ρ(y) L σ`, since `ρ(y) ≠ 0` forces `|y| < σ`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_close : ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ (ρ : Eucl P → ℝ) (σ : ℝ), Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) → ∫ y, ρ y = 1 → ∀ x : Eucl P, |(∫ y, ρ y * F (x - y)) - F x| ≤ (L : ℝ) * σ := by
  intro P F L hF ρ σ hρc hρs hρ0 hρσ hρ1 x
  -- `ρ` and `y ↦ ρ(y) F(x − y)` are continuous with compact support, hence integrable.
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hgi : Integrable fun y => ρ y * F (x - y) :=
    (hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρs.mul_right
  -- Since `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`.
  have herr : (∫ y, ρ y * F (x - y)) - F x = ∫ y, ρ y * (F (x - y) - F x) := by
    simp_rw [mul_sub]
    rw [integral_sub hgi (hρi.mul_const (F x)), integral_mul_const, hρ1, one_mul]
  -- Pointwise `|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L σ`.
  have hpt : ∀ y, ‖ρ y * (F (x - y) - F x)‖ ≤ ρ y * ((L : ℝ) * σ) := by
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    -- `ρ(y) ≠ 0` forces `|y| < σ`.
    have hyσ : ‖y‖ ≤ σ := (not_le.mp fun h => hy (hρσ y h)).le
    have hlip : |F (x - y) - F x| ≤ (L : ℝ) * σ := by
      rw [← Real.dist_eq]
      calc dist (F (x - y)) (F x) ≤ (L : ℝ) * dist (x - y) x := hF.dist_le_mul _ _
        _ = (L : ℝ) * ‖y‖ := by rw [dist_self_sub_left]
        _ ≤ (L : ℝ) * σ := mul_le_mul_of_nonneg_left hyσ L.coe_nonneg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
    exact mul_le_mul_of_nonneg_left hlip (hρ0 y)
  -- Integrate the pointwise bound, using `∫ ρ = 1` once more.
  rw [herr, ← Real.norm_eq_abs]
  calc ‖∫ y, ρ y * (F (x - y) - F x)‖ ≤ ∫ y, ρ y * ((L : ℝ) * σ) :=
        norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall hpt)
    _ = (L : ℝ) * σ := by rw [integral_mul_const, hρ1, one_mul]

/-- **Smooth approximation of a Lipschitz function with a.e. convergent derivatives**
(mollification).  Let `ψ_m` be the kernels of `constancy_mdc_smooth_approx_identity_ae_tendsto`
and `G_m(x) = ∫ ψ_m(y) g(x − y) dy = (ψ_m ⋆ g)(x)`.  Then `G_m` is `C^∞`, `L`-Lipschitz (an
average of translates of `g`), and `|G_m − g| ≤ 2L/(m+1)` by
`slicing_mb_sa_mollify_lipschitz_close`.  Differentiating under the integral sign
(`slicing_mb_sa_mollify_lipschitz_hasFDerivAt`), `DG_m(x) e_b = (∂_b g ∗ ψ_m)(x)`, which tends to
`∂_b g(x)` for a.e. `x` because `∂_b g` is bounded and measurable; as `‖T‖ ≤ Σ_b |T e_b|` for
`T : ℝ^k →L[ℝ] ℝ`, `DG_m(x) → Dg(x)` for a.e. `x`. -/
theorem Submission.deformation_ipl_mwc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : ℝ≥0) (g : Eucl k → ℝ), LipschitzWith L g → ∃ G : ℕ → Eucl k → ℝ, (∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G m)) ∧ (∀ m, LipschitzWith L (G m)) ∧ TendstoUniformly G g atTop ∧ ∀ᵐ w ∂(volume : Measure (Eucl k)), Tendsto (fun m => fderiv ℝ (G m) w) atTop (𝓝 (fderiv ℝ g w)) := by
  intro k L g hg
  -- The kernels `ψ_m`: `C^∞`, `≥ 0`, `∫ ψ_m = 1`, `spt ψ_m ⊆ B̄_{1/(m+1)}(0)`.
  obtain ⟨ψ, hψs, hψc, hψsupp, hψnn, hψone, hψae⟩ :=
    Submission.constancy_mdc_smooth_approx_identity_ae_tendsto k
  have hψcont : ∀ m, Continuous (ψ m) := fun m => (hψs m).continuous
  have hψint : ∀ m, Integrable (ψ m) volume := fun m =>
    (hψcont m).integrable_of_hasCompactSupport (hψc m)
  -- `ψ_m(y) = 0` for `|y| ≥ 2/(m+1)`.
  have hψzero : ∀ (m : ℕ) (y : Eucl k), 2 / ((m : ℝ) + 1) ≤ ‖y‖ → ψ m y = 0 := by
    intro m y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have h1 := hψsupp m hy'
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : 1 / ((m : ℝ) + 1) < 2 / ((m : ℝ) + 1) :=
      div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith
  -- `G_m(x) = ∫ ψ_m(y) g(x − y) dy`.
  set G : ℕ → Eucl k → ℝ := fun m x => ∫ y, ψ m y * g (x - y) with hG
  refine ⟨G, fun m => ?_, fun m => ?_, ?_, ?_⟩
  · -- `G_m = ψ_m ⋆ g` is `C^∞`.
    have hconv : convolution (ψ m) g (ContinuousLinearMap.lsmul ℝ ℝ) volume = G m := by
      funext x
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hG]
    rw [← hconv]
    exact (hψc m).contDiff_convolution_left _ (hψs m) hg.continuous.locallyIntegrable
  · -- `|G_m(x) − G_m(x')| ≤ ∫ ψ_m(y) |g(x − y) − g(x' − y)| dy ≤ L |x − x'|`.
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hi : ∀ z, Integrable (fun y => ψ m y * g (z - y)) volume := fun z =>
      Continuous.integrable_of_hasCompactSupport
        ((hψcont m).mul (hg.continuous.comp (continuous_const.sub continuous_id))) (hψc m).mul_right
    have hpt : ∀ y, ‖ψ m y * g (x - y) - ψ m y * g (x' - y)‖ ≤ ψ m y * ((L : ℝ) * dist x x') := by
      intro y
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψnn m y)]
      refine mul_le_mul_of_nonneg_left ?_ (hψnn m y)
      rw [← Real.dist_eq]
      calc dist (g (x - y)) (g (x' - y)) ≤ L * dist (x - y) (x' - y) := hg.dist_le_mul _ _
        _ = L * dist x x' := by rw [dist_sub_right]
    rw [Real.dist_eq]
    simp only [hG]
    rw [← integral_sub (hi x) (hi x'), ← Real.norm_eq_abs]
    calc ‖∫ y, ψ m y * g (x - y) - ψ m y * g (x' - y)‖ ≤ ∫ y, ψ m y * ((L : ℝ) * dist x x') :=
          norm_integral_le_of_norm_le ((hψint m).mul_const _) (Eventually.of_forall hpt)
      _ = L * dist x x' := by rw [integral_mul_const, hψone m, one_mul]
  · -- `|G_m − g| ≤ 2L/(m+1) → 0`.
    have hclose : ∀ m x, |G m x - g x| ≤ (L : ℝ) * (2 / ((m : ℝ) + 1)) := fun m x =>
      Submission.slicing_mb_sa_mollify_lipschitz_close k g L hg (ψ m) (2 / ((m : ℝ) + 1))
        (hψcont m) (hψc m) (hψnn m) (hψzero m) (hψone m) x
    have hlim : Tendsto (fun m : ℕ => (L : ℝ) * (2 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (L : ℝ))
      rw [mul_zero] at this
      exact this.congr fun m => by ring
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with m hm x
    rw [dist_comm, Real.dist_eq]
    exact (hclose m x).trans_lt hm
  · set e : Fin k → Eucl k := fun b => EuclideanSpace.basisFun (Fin k) ℝ b with he
    have hDg : ∀ z, ‖fderiv ℝ g z‖ ≤ L := fun z => norm_fderiv_le_of_lipschitz ℝ hg
    -- `DG_m(x) = ∫ ψ_m(y) Dg(x − y) dy`, a Bochner integral of an integrable integrand.
    have hfd : ∀ m x, fderiv ℝ (G m) x = ∫ y, ψ m y • fderiv ℝ g (x - y) := fun m x =>
      (Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt k g L hg (ψ m) (hψcont m)
        (hψc m) x).fderiv
    have hint : ∀ m x, Integrable (fun y => ψ m y • fderiv ℝ g (x - y)) volume := by
      intro m x
      refine ((hψint m).mul_const (L : ℝ)).mono' ?_ (Eventually.of_forall fun y => ?_)
      · exact ((hψcont m).measurable.smul ((measurable_fderiv ℝ g).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
      · rw [norm_smul, Real.norm_of_nonneg (hψnn m y)]
        exact mul_le_mul_of_nonneg_left (hDg _) (hψnn m y)
    -- Hence `DG_m(x) v = (Dg(·) v ∗ ψ_m)(x)`.
    have happly : ∀ m x v, fderiv ℝ (G m) x v =
        convolution (fun t => fderiv ℝ g t v) (ψ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro m x v
      rw [hfd, ContinuousLinearMap.integral_apply (hint m x), convolution_lsmul_swap]
      congr 1
      funext t
      simp only [smul_apply, smul_eq_mul, mul_comm]
    -- `Dg(·) v` is measurable and bounded by `L |v|`, hence locally integrable.
    have hloc : ∀ v, LocallyIntegrable (fun t => fderiv ℝ g t v) volume := by
      intro v
      refine (locallyIntegrable_const ((L : ℝ) * ‖v‖)).mono
        (measurable_fderiv_apply_const ℝ g v).aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg L.coe_nonneg (norm_nonneg v))]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDg t) (norm_nonneg _))
    -- For a.e. `x`: `DG_m(x) e_b → Dg(x) e_b` for every `b`.
    have hae : ∀ᵐ x ∂(volume : Measure (Eucl k)), ∀ b,
        Tendsto (fun m => fderiv ℝ (G m) x (e b)) atTop (𝓝 (fderiv ℝ g x (e b))) := by
      rw [ae_all_iff]
      intro b
      filter_upwards [hψae _ (hloc (e b))] with x hx
      simp_rw [happly]
      exact hx
    -- `‖T‖ ≤ Σ_b |T e_b|`, writing `z = Σ_b z_b e_b` with `|z_b| ≤ |z|`.
    have hnorm : ∀ T : Eucl k →L[ℝ] ℝ, ‖T‖ ≤ ∑ b, |T (e b)| := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound _
        (Finset.sum_nonneg fun b _ => abs_nonneg _) fun z => ?_
      have hz : z = ∑ b, z b • e b := by
        simpa [he] using ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr z).symm
      calc ‖T z‖ = ‖∑ b, z b * T (e b)‖ := by
            conv_lhs => rw [hz]
            simp [map_sum, map_smul]
        _ ≤ ∑ b, ‖z b * T (e b)‖ := norm_sum_le _ _
        _ = ∑ b, ‖z b‖ * |T (e b)| := by simp [norm_mul]
        _ ≤ ∑ b, ‖z‖ * |T (e b)| := Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z b) (abs_nonneg _)
        _ = (∑ b, |T (e b)|) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
    -- Squeeze: `‖DG_m(x) − Dg(x)‖ ≤ Σ_b |DG_m(x) e_b − Dg(x) e_b| → 0`.
    filter_upwards [hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => hnorm _) ?_
    have hsum : Tendsto (fun m => ∑ b, |(fderiv ℝ (G m) x - fderiv ℝ g x) (e b)|) atTop
        (𝓝 (∑ b, |fderiv ℝ g x (e b) - fderiv ℝ g x (e b)|)) := by
      refine tendsto_finsetSum _ fun b _ => ?_
      simp only [sub_apply]
      exact ((hx b).sub_const _).abs
    simpa using hsum

/-- **Integration by parts for the Jacobian minors of a Lipschitz map** (the divergence form of
the minors; cf. J. M. Ball, ARMA 63 (1977)).  Let `v` be `C`-Lipschitz on the open set `Ω`,
`φ ∈ C¹_c(Ω)`, `M = det (∂_{b s} v^{a t})_{t,s}` the `(r+1) × (r+1)` minor with rows `a` and
columns `b`, and `C_q = (-1)^q det (∂_{b (q.succAbove s)} v^{a t.succ})_{t,s}` its cofactors
along the first row.  Then `∫_Ω φ M = -∑_q ∫_Ω v^{a 0} C_q ∂_{b q} φ`.

Extend each coordinate `v^c|_Ω` to a `C`-Lipschitz `ṽ^c` on `ℝ^k` (McShane) and mollify it
(`lipschitz_smooth_approx`): `G^c_m` is `C^∞` and `C`-Lipschitz, `G^c_m → ṽ^c` uniformly and
`DG^c_m → Dṽ^c` a.e.  The identity holds on `ℝ^k` for the rows `G^{a t}_m` (`minor_ibp_smooth`);
the matrix entries are bounded by `C` and converge a.e., and the scalar factors are dominated by
`|φ|` resp. `(|ṽ^{a 0}| + 1) |∂_{b q} φ|` for large `m`, so it passes to the limit
(`mil_tendsto_integral_mul_det`).  Finally `Dṽ^c = proj_c ∘ Dv` a.e. on `Ω`
(`mil_ae_fderiv_eq_proj`), `ṽ^c = v^c` on `Ω`, and every integrand vanishes off
`tsupport φ ⊆ Ω`. -/
theorem Submission.deformation_ipl_mwc_minor_ibp_lipschitz : ∀ (k Q r : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (a : Fin (r + 1) → Fin Q) (b : Fin (r + 1) → Fin k) (v : Eucl k → Eucl Q) (φ : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∫ w in Ω, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) => EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k)) = -∑ q : Fin (r + 1), ∫ w in Ω, EuclideanSpace.proj (a 0) (v w) * ((-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ) (fderiv ℝ v w (EuclideanSpace.single (b (q.succAbove s)) 1)))) * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
  intro k Q r Ω C a b v φ hΩ hv hφ hφc hφΩ
  -- Step 1 (McShane): `v^c = proj_c ∘ v` is `C`-Lipschitz on `Ω`, so it extends to a
  -- `C`-Lipschitz `ṽ^c` on `ℝ^k` with `ṽ^c = v^c` on `Ω`.
  have hvc : ∀ c : Fin Q, LipschitzOnWith C (fun w => EuclideanSpace.proj c (v w)) Ω := by
    intro c
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    calc dist (EuclideanSpace.proj c (v x)) (EuclideanSpace.proj c (v y))
          = ‖(v x - v y) c‖ := by simp [dist_eq_norm]
      _ ≤ ‖v x - v y‖ := PiLp.norm_apply_le _ _
      _ = dist (v x) (v y) := (dist_eq_norm _ _).symm
      _ ≤ C * dist x y := hv.dist_le_mul x hx y hy
  choose vt hvtl hvteq using fun c => (hvc c).extend_real
  -- Step 2: `C^∞`, `C`-Lipschitz `G^c_m → ṽ^c` uniformly, with `DG^c_m → Dṽ^c` a.e.
  choose G hGs hGl hGu hGd using fun c =>
    Submission.deformation_ipl_mwc_lipschitz_smooth_approx k C (vt c) (hvtl c)
  -- Step 3: the smooth identity `(S_m)` for the rows `V^m_t = G^{a t}_m`.
  have hS : ∀ m : ℕ, ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
        fderiv ℝ (G (a t) m) w (EuclideanSpace.single (b s) 1)) =
      -∑ q : Fin (r + 1), ∫ w, G (a 0) m w * ((-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (G (a t.succ) m) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1) := fun m =>
    Submission.deformation_ipl_mwc_minor_ibp_smooth k r (fun t => G (a t) m) b φ
      (fun t => (hGs (a t) m).of_le (WithTop.coe_le_coe.2 le_top)) hφ hφc
  -- Step 4: the entries `∂_i g` of a `C`-Lipschitz `g` are bounded by `C`, and those of `G^c_m`
  -- converge a.e. to those of `ṽ^c`.
  have hent : ∀ g : Eucl k → ℝ, LipschitzWith C g → ∀ (i : Fin k) (w : Eucl k),
      |fderiv ℝ g w (EuclideanSpace.single i 1)| ≤ C := by
    intro g hg i w
    calc |fderiv ℝ g w (EuclideanSpace.single i 1)|
        ≤ ‖fderiv ℝ g w‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          (fderiv ℝ g w).le_opNorm _
      _ ≤ C := by simpa using norm_fderiv_le_of_lipschitz ℝ hg (x₀ := w)
  have hconv : ∀ᵐ w ∂(volume : Measure (Eucl k)), ∀ (c : Fin Q) (i : Fin k),
      Tendsto (fun m => fderiv ℝ (G c m) w (EuclideanSpace.single i 1)) atTop
        (𝓝 (fderiv ℝ (vt c) w (EuclideanSpace.single i 1))) := by
    filter_upwards [ae_all_iff.2 hGd] with w hw c i
    exact ((continuous_id.clm_apply continuous_const).tendsto _).comp (hw c)
  -- Step 5: dominated convergence on both sides of `(S_m)`.
  have hφcont : Continuous φ := hφ.continuous
  have hL := Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det (Eucl k) volume (r + 1)
    C (fun m t s w => fderiv ℝ (G (a t) m) w (EuclideanSpace.single (b s) 1))
    (fun t s w => fderiv ℝ (vt (a t)) w (EuclideanSpace.single (b s) 1)) (fun _ => φ) φ
    (fun w => |φ w|) (fun m t s => (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable)
    (fun _ => hφcont.aestronglyMeasurable) (hφcont.integrable_of_hasCompactSupport hφc).abs
    (fun m t s w => hent _ (hGl _ m) _ w) (Eventually.of_forall fun _ _ => le_rfl)
    (ae_of_all _ fun _ => tendsto_const_nhds) (hconv.mono fun w hw t s => hw _ _)
  have hR : ∀ q : Fin (r + 1), Tendsto (fun m => ∫ w, G (a 0) m w * ((-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (G (a t.succ) m) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1)) atTop
      (𝓝 (∫ w, vt (a 0) w * ((-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (vt (a t.succ)) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1))) := by
    intro q
    have hdφ : Continuous fun w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdφs : HasCompactSupport fun w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1) :=
      hφc.fderiv_apply ℝ _
    -- The majorant `(|ṽ^{a 0}| + 1) |∂_{b q} φ|` is continuous with compact support.
    have hH : Integrable (fun w => (|vt (a 0) w| + 1) *
        |fderiv ℝ φ w (EuclideanSpace.single (b q) 1)|) (volume : Measure (Eucl k)) :=
      (((hvtl (a 0)).continuous.abs.add continuous_const).mul
        hdφ.abs).integrable_of_hasCompactSupport hdφs.abs.mul_left
    -- `|G^{a 0}_m| ≤ |ṽ^{a 0}| + 1` as soon as `sup |G^{a 0}_m − ṽ^{a 0}| < 1`.
    have hbd : ∀ᶠ m in atTop, ∀ w, |(-1 : ℝ) ^ (q : ℕ) * G (a 0) m w *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1)| ≤
        (|vt (a 0) w| + 1) * |fderiv ℝ φ w (EuclideanSpace.single (b q) 1)| := by
      filter_upwards [Metric.tendstoUniformly_iff.1 (hGu (a 0)) 1 one_pos] with m hm w
      have hd := hm w
      rw [Real.dist_eq, abs_sub_comm] at hd
      have h1 : |G (a 0) m w| ≤ |vt (a 0) w| + 1 := by
        linarith [abs_sub_abs_le_abs_sub (G (a 0) m w) (vt (a 0) w)]
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have key := Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det (Eucl k) volume r C
      (fun m t s w => fderiv ℝ (G (a t.succ) m) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      (fun t s w => fderiv ℝ (vt (a t.succ)) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      (fun m w => (-1 : ℝ) ^ (q : ℕ) * G (a 0) m w *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1))
      (fun w => (-1 : ℝ) ^ (q : ℕ) * vt (a 0) w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1))
      _ (fun m t s => (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable)
      (fun m => ((continuous_const.mul (hGs (a 0) m).continuous).mul hdφ).aestronglyMeasurable)
      hH (fun m t s w => hent _ (hGl _ m) _ w) hbd
      (ae_of_all _ fun w => (tendsto_const_nhds.mul ((hGu (a 0)).tendsto_at w)).mul
        tendsto_const_nhds)
      (hconv.mono fun w hw t s => hw _ _)
    convert key using 2 with m <;>
      exact integral_congr_ae (Eventually.of_forall fun w => by beta_reduce; ring)
  -- `(S)`: by uniqueness of limits, `(S_m)` passes to the limit `m → ∞`.
  have hlim := tendsto_nhds_unique hL
    (((tendsto_finsetSum _ fun q _ => hR q).neg).congr fun m => (hS m).symm)
  -- Step 6: back to `v` on `Ω`.  For a.e. `w ∈ Ω`, `Dṽ^c(w) = proj_c ∘ Dv(w)`.
  have hae : ∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → ∀ (c : Fin Q) (x : Eucl k),
      fderiv ℝ (vt c) w x = EuclideanSpace.proj c (fderiv ℝ v w x) := by
    filter_upwards [ae_all_iff.2 fun c => Submission.deformation_ipl_mwc_mil_ae_fderiv_eq_proj
      k Q Ω C v c (vt c) hΩ hv (hvteq c).symm] with w hw hwΩ c x
    exact hw c hwΩ x
  -- `φ` and `Dφ` vanish off `tsupport φ ⊆ Ω`, so the integrals over `ℝ^k` are over `Ω`.
  have hφ0 : ∀ w, w ∉ Ω → φ w = 0 := fun w hw =>
    image_eq_zero_of_notMem_tsupport fun h => hw (hφΩ h)
  have hdφ0 : ∀ w, w ∉ Ω → fderiv ℝ φ w = 0 := fun w hw =>
    fderiv_of_notMem_tsupport ℝ fun h => hw (hφΩ h)
  have hΩint : ∀ F F' : Eucl k → ℝ, (∀ w, w ∉ Ω → F' w = 0) →
      (∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → F w = F' w) → ∫ w in Ω, F w = ∫ w, F' w :=
    fun F F' h0 hFF' => (setIntegral_congr_ae hΩ.measurableSet hFF').trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero h0)
  refine (hΩint _ _ (fun w hw => ?_) ?_).trans (hlim.trans ?_)
  · simp [hφ0 w hw]
  · filter_upwards [hae] with w hw hwΩ
    simp only [hw hwΩ]
  · congr 1
    refine Finset.sum_congr rfl fun q _ => (hΩint _ _ (fun w hw => ?_) ?_).symm
    · simp [hdφ0 w hw]
    · filter_upwards [hae] with w hw hwΩ
      have h0 : vt (a 0) w = EuclideanSpace.proj (a 0) (v w) := (hvteq (a 0) hwΩ).symm
      simp only [hw hwΩ, h0]

/-- Smooth test functions suffice (step (3.0) of the proof of `minor_weak_continuity`): if
`Ω ⊆ ℝᵏ` is open, `|f_j|, |f₀| ≤ B` on `Ω` and `∫_Ω φ f_j → ∫_Ω φ f₀` for every `φ ∈ C¹_c(Ω)`, then
`∫_Ω η f_j → ∫_Ω η f₀` for every `η ∈ L¹(Ω)`.  Given `δ > 0`, choose `ε > 0` with
`2 |B| ε ≤ δ / 2` and, by `scalar_smooth_dense`, `φ ∈ C_c^∞(Ω)` with `∫_Ω |η − φ| < ε`.  Then
`|∫_Ω η g − ∫_Ω φ g| ≤ |B| ∫_Ω |η − φ| ≤ |B| ε` for `g = f_j, f₀`, so for large `j`
`|∫_Ω η f_j − ∫_Ω η f₀| ≤ |B| ε + |∫_Ω φ f_j − ∫_Ω φ f₀| + |B| ε < δ`. -/
theorem Submission.deformation_ipl_mwc_test_density : ∀ (k : ℕ) (Ω : Set (Eucl k)) (B : ℝ) (f : ℕ → Eucl k → ℝ) (f₀ : Eucl k → ℝ), IsOpen Ω → (∀ j, AEStronglyMeasurable (f j) ((volume : Measure (Eucl k)).restrict Ω)) → AEStronglyMeasurable f₀ ((volume : Measure (Eucl k)).restrict Ω) → (∀ j, ∀ w ∈ Ω, |f j w| ≤ B) → (∀ w ∈ Ω, |f₀ w| ≤ B) → (∀ φ : Eucl k → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → Tendsto (fun j => ∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k))))) → ∀ η : Eucl k → ℝ, IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k)))) := by
  intro k Ω B f f₀ hΩ hfm hf₀m hfB hf₀B hφ η hη
  -- Step 2: `ζ g ∈ L¹(Ω)` for `ζ ∈ L¹(Ω)` and `g` bounded by `B` (hence by `|B|`) on `Ω`.
  have hint : ∀ ζ g : Eucl k → ℝ, IntegrableOn ζ Ω (volume : Measure (Eucl k)) →
      AEStronglyMeasurable g ((volume : Measure (Eucl k)).restrict Ω) → (∀ w ∈ Ω, |g w| ≤ B) →
      IntegrableOn (fun w => ζ w * g w) Ω (volume : Measure (Eucl k)) := fun ζ g hζ hg hgB =>
    Integrable.mul_bdd hζ hg (ae_restrict_of_forall_mem hΩ.measurableSet fun w hw =>
      (hgB w hw).trans (le_abs_self B))
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Step 3: `ε > 0` with `2 |B| ε ≤ δ / 2` (`|B|` avoids the case split `Ω = ∅`).
  obtain ⟨ε, hε0, hBε⟩ : ∃ ε : ℝ, 0 < ε ∧ |B| * ε ≤ δ / 4 := by
    refine ⟨δ / (4 * (|B| + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg B]
  -- Step 1 (the sibling `scalar_smooth_dense`): `φ ∈ C_c^∞(Ω)` with `∫_Ω |η − φ| < ε`.
  obtain ⟨φ, hφs, hφc, hφΩ, hηφ⟩ :=
    Submission.deformation_ipl_mwc_td_scalar_smooth_dense k Ω η hΩ hη ε hε0
  have hφi : IntegrableOn φ Ω (volume : Measure (Eucl k)) :=
    (hφs.continuous.integrable_of_hasCompactSupport hφc).integrableOn
  -- `|∫_Ω η g − ∫_Ω φ g| ≤ |B| ∫_Ω |η − φ| ≤ |B| ε` for `g` bounded by `B` on `Ω`.
  have happrox : ∀ g : Eucl k → ℝ,
      AEStronglyMeasurable g ((volume : Measure (Eucl k)).restrict Ω) → (∀ w ∈ Ω, |g w| ≤ B) →
      dist (∫ w in Ω, η w * g w ∂(volume : Measure (Eucl k)))
        (∫ w in Ω, φ w * g w ∂(volume : Measure (Eucl k))) ≤ |B| * ε := by
    intro g hg hgB
    rw [dist_eq_norm, ← integral_sub (hint η g hη hg hgB) (hint φ g hφi hg hgB)]
    calc ‖∫ w in Ω, η w * g w - φ w * g w ∂(volume : Measure (Eucl k))‖
        ≤ ∫ w in Ω, |B| * |η w - φ w| ∂(volume : Measure (Eucl k)) := by
          refine norm_integral_le_of_norm_le ((hη.sub hφi).abs.const_mul |B|)
            (ae_restrict_of_forall_mem hΩ.measurableSet fun w hw => ?_)
          rw [← sub_mul, Real.norm_eq_abs, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right ((hgB w hw).trans (le_abs_self B)) (abs_nonneg _)
      _ = |B| * ∫ w in Ω, |η w - φ w| ∂(volume : Measure (Eucl k)) := integral_const_mul _ _
      _ ≤ |B| * ε := mul_le_mul_of_nonneg_left hηφ.le (abs_nonneg B)
  -- The hypothesis for `φ ∈ C¹_c(Ω)`, then the `ε/3` estimate.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (hφ φ (hφs.of_le (WithTop.coe_le_coe.2 le_top)) hφc hφΩ) (δ / 2) (half_pos hδ)
  refine ⟨N, fun j hj => ?_⟩
  have h₁ := happrox (f j) (hfm j) (hfB j)
  have h₂ := hN j hj
  have h₃ := happrox f₀ hf₀m hf₀B
  rw [dist_comm] at h₃
  linarith [dist_triangle4 (∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k)))
    (∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k)))
    (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k)))
    (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k)))]

/-- Weak-* continuity of the Jacobian minors (step 3 of the proof of `minor_weak_continuity`;
J. M. Ball, ARMA 63 (1977); Fonseca–Leoni–Malý, ARMA 178 (2005)).  Let `v_j, v₀` be
`C`-Lipschitz on the open set `Ω` with `v_j → v₀` uniformly on `Ω`, and let
`M_{a,b}(u) = det (⟨e_{a t}, Du (e_{b s})⟩)_{t,s}` be the `r × r` minor with rows `a` and
columns `b`.  Then `∫_Ω η M_{a,b}(v_j) → ∫_Ω η M_{a,b}(v₀)` for every `η ∈ L¹(Ω)`.

Induction on `r`; for `r = 0` both sides equal `∫_Ω η`.  For `r + 1`, `‖Du‖ ≤ C` on `Ω` gives
`|M_{a,b}(u)| ≤ (r+1)! C^{r+1}` there, so by `test_density` it suffices to test against
`φ ∈ C¹_c(Ω)`.  By `minor_ibp_lipschitz`,
`∫_Ω φ M_{a,b}(u) = -∑_q ∫_Ω u^{a 0} (-1)^q M_{a',b^{(q)}}(u) ∂_{b q} φ` with `a' = a ∘ succ`,
`b^{(q)} = b ∘ q.succAbove`.  In each term the part carrying `v_j^{a 0} - v₀^{a 0} → 0`
(uniformly on `Ω`, while `|M_{a',b^{(q)}}| ≤ r! C^r`) tends to `0`, and the induction hypothesis
applies to the rest, tested against `η_q = v₀^{a 0} ∂_{b q} φ ∈ L¹(Ω)`. -/
theorem Submission.deformation_ipl_mwc_minor_weak_star :
    ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q),
      IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω →
      TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k)
      (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) →
      Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k))) atTop
        (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k)))) := by
  intro k Q Ω C v v₀ hΩ hv hv₀ hconv r
  /- Step 0: bounds and measurability.  Leibniz formula: `|det A| ≤ n! c^n` if all
  `|A t s| ≤ c` (`Matrix.det_le` is not imported). -/
  have abs_det_le : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
      (∀ t s, |A t s| ≤ c) → |A.det| ≤ (Nat.factorial n : ℝ) * c ^ n := by
    intro n A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
          gcongr with σ
          have hσ : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [hσ, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ n := by simp
      _ = (Nat.factorial n : ℝ) * c ^ n := by simp [Fintype.card_perm]
  -- If `u` is `C`-Lipschitz on `Ω`, then `‖Du‖ ≤ C` on `Ω`, so every entry of a minor is
  -- bounded by `C` and `|M_{a,b}(u)| ≤ n! C^n` on `Ω`; every minor is Borel measurable.
  have minor_facts : ∀ {n : ℕ} (a : Fin n → Fin Q) (b : Fin n → Fin k) (u : Eucl k → Eucl Q),
      LipschitzOnWith C u Ω →
      (∀ w ∈ Ω, |Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))| ≤ (Nat.factorial n : ℝ) * (C : ℝ) ^ n) ∧
      Measurable (fun w => Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))) := by
    intro n a b u hu
    constructor
    · intro w hw
      refine abs_det_le _ C fun t s => ?_
      have hDu : ‖fderiv ℝ u w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hu
      calc |EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1))|
          = ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1) (a t)‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖fderiv ℝ u w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ :=
          (fderiv ℝ u w).le_opNorm _
        _ ≤ C := by simpa using hDu
    · have hdet : Continuous fun A : Fin n → Fin n → ℝ => (Matrix.of A).det :=
        Continuous.matrix_det continuous_id
      have hent : ∀ t s : Fin n, Measurable fun w =>
          EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)) := fun t s =>
        (EuclideanSpace.proj (a t)).continuous.measurable.comp
          (measurable_fderiv_apply_const ℝ u _)
      exact hdet.measurable.comp
        (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => hent t s)
  induction r with
  | zero =>
    -- Step 1: a `0 × 0` determinant is `1`, so the sequence is constant.
    intro a b η hη
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro a b η hη
    -- `M u = M_{a,b}(u)`, the `(r + 1) × (r + 1)` minor.
    let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w =>
      Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
        EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))
    -- Step 2: by `test_density` (bound `(r+1)! C^{r+1}`) it suffices to test against
    -- `φ ∈ C¹_c(Ω)`.
    refine Submission.deformation_ipl_mwc_test_density k Ω
      ((Nat.factorial (r + 1) : ℝ) * (C : ℝ) ^ (r + 1)) (fun j => M (v j)) (M v₀) hΩ
      (fun j => (minor_facts a b (v j) (hv j)).2.aestronglyMeasurable)
      (minor_facts a b v₀ hv₀).2.aestronglyMeasurable
      (fun j => (minor_facts a b (v j) (hv j)).1) (minor_facts a b v₀ hv₀).1 ?_ η hη
    intro φ hφ hφc hφΩ
    -- `M' q u = M_{a',b^{(q)}}(u)`, `dφ q = ∂_{b q} φ` and `p u = u^{a 0}`.
    let M' : Fin (r + 1) → (Eucl k → Eucl Q) → Eucl k → ℝ := fun q u w =>
      Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ)
        (fderiv ℝ u w (EuclideanSpace.single (b (q.succAbove s)) 1)))
    let dφ : Fin (r + 1) → Eucl k → ℝ := fun q w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1)
    let p : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w => EuclideanSpace.proj (a 0) (u w)
    -- Step 3: integration by parts (`minor_ibp_lipschitz`) for `u = v_j` and `u = v₀`.
    have hDu : ∀ u, LipschitzOnWith C u Ω →
        ∫ w in Ω, φ w * M u w ∂(volume : Measure (Eucl k)) =
          -∑ q : Fin (r + 1), ∫ w in Ω, p u w * ((-1 : ℝ) ^ (q : ℕ) * M' q u w) * dφ q w
            ∂(volume : Measure (Eucl k)) := fun u hu =>
      Submission.deformation_ipl_mwc_minor_ibp_lipschitz k Q r Ω C a b u φ hΩ hu hφ hφc hφΩ
    have hfun : (fun j => ∫ w in Ω, φ w * M (v j) w ∂(volume : Measure (Eucl k))) = fun j =>
        -∑ q : Fin (r + 1), ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
          ∂(volume : Measure (Eucl k)) := funext fun j => hDu _ (hv j)
    rw [hfun, hDu v₀ hv₀]
    refine (tendsto_finsetSum _ fun q _ => ?_).neg
    -- `dφ q` is continuous, vanishes off the compact `K = tsupport φ ⊆ Ω` and is integrable.
    set K := tsupport φ with hK
    have hKc : IsCompact K := hφc
    have hdφc : Continuous (dφ q) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdφ0 : ∀ w, w ∉ K → dφ q w = 0 := by
      intro w hw
      have : fderiv ℝ φ w = 0 := by
        by_contra h
        exact hw (support_fderiv_subset ℝ (Function.mem_support.2 h))
      simp [dφ, this]
    have hdφsupp : HasCompactSupport (dφ q) :=
      HasCompactSupport.of_support_subset_isCompact hKc fun w hw => by
        by_contra h; exact hw (hdφ0 w h)
    have hdφint : Integrable (dφ q) (volume : Measure (Eucl k)) :=
      hdφc.integrable_of_hasCompactSupport hdφsupp
    -- `p u` is bounded on `K` and measurable on `Ω`; `|M' q u| ≤ B' = r! C^r` on `Ω`.
    have hpbd : ∀ u, LipschitzOnWith C u Ω → ∃ P : ℝ, 0 ≤ P ∧ ∀ w ∈ K, |p u w| ≤ P := by
      intro u hu
      obtain ⟨P, hP⟩ := hKc.exists_bound_of_continuousOn
        (((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn hu.continuousOn).mono hφΩ)
      refine ⟨max P 0, le_max_right _ _, fun w hw => le_trans ?_ (le_max_left _ _)⟩
      have := hP w hw
      simp only [Function.comp_apply, Real.norm_eq_abs] at this
      exact this
    have hpm : ∀ u, LipschitzOnWith C u Ω →
        AEStronglyMeasurable (p u) ((volume : Measure (Eucl k)).restrict Ω) := fun u hu =>
      ((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn
        hu.continuousOn).aestronglyMeasurable hΩ.measurableSet
    have hM'b : ∀ u, LipschitzOnWith C u Ω →
        ∀ w ∈ Ω, |M' q u w| ≤ (Nat.factorial r : ℝ) * (C : ℝ) ^ r :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).1
    have hM'm : ∀ u, LipschitzOnWith C u Ω → Measurable (M' q u) :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).2
    set B' : ℝ := (Nat.factorial r : ℝ) * (C : ℝ) ^ r with hB'
    have hB'0 : 0 ≤ B' := by positivity
    -- Step 4: anything a.e.-measurable on `Ω` and bounded by `c |dφ q|` there is integrable.
    have hint : ∀ (F : Eucl k → ℝ) (c : ℝ),
        AEStronglyMeasurable F ((volume : Measure (Eucl k)).restrict Ω) →
        (∀ w ∈ Ω, |F w| ≤ c * |dφ q w|) → IntegrableOn F Ω (volume : Measure (Eucl k)) := by
      intro F c hFm hFb
      refine Integrable.mono' ((hdφint.abs.const_mul c).integrableOn) hFm ?_
      exact (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
        simpa [Real.norm_eq_abs] using hFb w hw)
    let ηq : Eucl k → ℝ := fun w => p v₀ w * dφ q w
    obtain ⟨P0, hP00, hP0⟩ := hpbd v₀ hv₀
    have hηq : IntegrableOn ηq Ω (volume : Measure (Eucl k)) := by
      refine hint ηq P0 ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict) fun w hw => ?_
      by_cases hwK : w ∈ K
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hP0 w hwK) (abs_nonneg _)
      · simp [ηq, hdφ0 w hwK]
    have hI1 : ∀ j, IntegrableOn (fun w => (p (v j) w - p v₀ w) *
        ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w) Ω (volume : Measure (Eucl k)) := by
      intro j
      obtain ⟨Pj, hPj0, hPj⟩ := hpbd (v j) (hv j)
      refine hint _ ((Pj + P0) * B') ((((hpm _ (hv j)).sub (hpm _ hv₀)).mul
        ((hM'm _ (hv j)).aestronglyMeasurable.const_mul _)).mul
          hdφc.aestronglyMeasurable.restrict) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        gcongr
        · exact (abs_sub _ _).trans (add_le_add (hPj w hwK) (hP0 w hwK))
        · exact hM'b _ (hv j) w hw
      · simp [hdφ0 w hwK]
    have hI2 : ∀ u, LipschitzOnWith C u Ω →
        IntegrableOn (fun w => ηq w * M' q u w) Ω (volume : Measure (Eucl k)) := by
      intro u hu
      refine hint _ (P0 * B') ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict
        |>.mul (hM'm _ hu).aestronglyMeasurable) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · simp only [ηq, abs_mul]
        calc |p v₀ w| * |dφ q w| * |M' q u w| ≤ P0 * |dφ q w| * B' := by
              gcongr
              · exact hP0 w hwK
              · exact hM'b _ hu w hw
          _ = P0 * B' * |dφ q w| := by ring
      · simp [ηq, hdφ0 w hwK]
    -- Step 5: `I_j = ∫_Ω (v_j^{a 0} - v₀^{a 0}) (-1)^q M'_j dφ + (-1)^q ∫_Ω η_q M'_j`.
    have hsplit : ∀ j, ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
        ∂(volume : Measure (Eucl k)) =
        (∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
          ∂(volume : Measure (Eucl k))) +
          (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q (v j) w ∂(volume : Measure (Eucl k)) := by
      intro j
      rw [← integral_const_mul, ← integral_add (hI1 j) ((hI2 _ (hv j)).const_mul _)]
      congr 1; funext w; simp only [ηq]; ring
    have hlim : ∫ w in Ω, p v₀ w * ((-1 : ℝ) ^ (q : ℕ) * M' q v₀ w) * dφ q w
        ∂(volume : Measure (Eucl k)) =
        0 + (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q v₀ w ∂(volume : Measure (Eucl k)) := by
      rw [zero_add, ← integral_const_mul]
      congr 1; funext w; simp only [ηq]; ring
    -- Step 6: the first term tends to `0`, as `p (v j) → p v₀` uniformly on `Ω`.
    have h1 : Tendsto (fun j => ∫ w in Ω, (p (v j) w - p v₀ w) *
        ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k))) atTop
        (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set I := ∫ w, |dφ q w| ∂(volume : Measure (Eucl k)) with hI
      have hI0 : 0 ≤ I := integral_nonneg fun w => abs_nonneg _
      set δ := ε / (2 * (B' * I + 1)) with hδ
      have hδ0 : 0 < δ := by positivity
      obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv δ hδ0)
      refine ⟨N, fun j hj => ?_⟩
      rw [dist_zero_right]
      have hbound : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict Ω),
          ‖(p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w‖ ≤
            δ * B' * |dφ q w| := by
        refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
        have e1 : |p (v j) w - p v₀ w| ≤ δ := by
          have h' := (hN j hj w hw).le
          rw [dist_comm, dist_eq_norm] at h'
          calc |p (v j) w - p v₀ w| = |EuclideanSpace.proj (a 0) (v j w - v₀ w)| := by
                simp [p]
            _ = ‖(v j w - v₀ w) (a 0)‖ := by simp [Real.norm_eq_abs]
            _ ≤ ‖v j w - v₀ w‖ := PiLp.norm_apply_le _ _
            _ ≤ δ := h'
        have e2 := hM'b _ (hv j) w hw
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          one_mul]
        gcongr
      calc ‖∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
            ∂(volume : Measure (Eucl k))‖
          ≤ ∫ w in Ω, δ * B' * |dφ q w| ∂(volume : Measure (Eucl k)) :=
            norm_integral_le_of_norm_le ((hdφint.abs.const_mul _).integrableOn) hbound
        _ ≤ ∫ w, δ * B' * |dφ q w| ∂(volume : Measure (Eucl k)) :=
            setIntegral_le_integral (hdφint.abs.const_mul _) (ae_of_all _ fun w => by positivity)
        _ = δ * (B' * I) := by rw [integral_const_mul, hI]; ring
        _ < ε := by
            rw [hδ]
            have : 0 < B' * I + 1 := by positivity
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
    -- Steps 7–8: the induction hypothesis, tested against `η_q ∈ L¹(Ω)`, handles the second
    -- term; multiplying by `(-1)^q` and adding the first term gives `I_j → I_0`.
    have hih := ih (fun t => a t.succ) (fun s => b (q.succAbove s)) ηq hηq
    rw [hlim]
    exact (h1.add (hih.const_mul _)).congr fun j => (hsplit j).symm

/-- Weak continuity of the Jacobian minors `M_{a,b}(u) = det (⟨e_{a t}, Du (e_{b s})⟩)_{t,s}`
against a coefficient `ψ (g ∘ u)`, `ψ ∈ L¹(Ω)`, `g ∈ C_c(ℝ^Q)` (step 2 of the proof of
`minor_weak_continuity`).  With `η = ψ (g ∘ u₀) ∈ L¹(Ω)`,
`∫_Ω ψ (g ∘ u_j) M_{a,b}(u_j) = ∫_Ω ψ (g ∘ u_j - g ∘ u₀) M_{a,b}(u_j) + ∫_Ω η M_{a,b}(u_j)`; the
first term tends to `0` because `|M_{a,b}(u_j)| ≤ r! C^r` on `Ω` and `g ∘ u_j → g ∘ u₀`
uniformly on `Ω`, the second tends to `∫_Ω η M_{a,b}(u₀)` by `minor_weak_star`. -/
theorem Submission.deformation_ipl_mwc_coeff_minor_continuity :
    ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (ψ : Eucl k → ℝ) (g : Eucl Q → ℝ) (C : ℝ≥0)
      (u : ℕ → Eucl k → Eucl Q) (u₀ : Eucl k → Eucl Q) (r : ℕ) (a : Fin r → Fin Q)
      (b : Fin r → Fin k), IsOpen Ω → IntegrableOn ψ Ω (volume : Measure (Eucl k)) →
      Continuous g → HasCompactSupport g → (∀ j, LipschitzOnWith C (u j) Ω) →
      LipschitzOnWith C u₀ Ω → TendstoUniformlyOn u u₀ atTop Ω →
      Tendsto (fun j => ∫ w in Ω, ψ w * g (u j w) * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ (u j) w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k))) atTop
        (𝓝 (∫ w in Ω, ψ w * g (u₀ w) * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ u₀ w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k)))) := by
  intro k Q Ω ψ g C u u₀ r a b hΩ hψ hg hgc hu hu₀ hconv
  -- `M v w = M_{a,b}(v)(w)`, the `(a, b)` minor of `Dv(w)`.
  let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun v w => Matrix.det (Matrix.of fun t s : Fin r =>
    EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1)))
  /- Step 1: bounds and measurability.  Leibniz formula: `|det A| ≤ r! c^r` if all
  `|A t s| ≤ c` (`Matrix.det_le` is not imported). -/
  have abs_det_le : ∀ (A : Matrix (Fin r) (Fin r) ℝ) (c : ℝ), (∀ t s, |A t s| ≤ c) →
      |A.det| ≤ (Nat.factorial r : ℝ) * c ^ r := by
    intro A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin r), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), c ^ r := by
          gcongr with σ
          have hσ : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [hσ, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin r, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ r := by simp
      _ = (Nat.factorial r : ℝ) * c ^ r := by simp [Fintype.card_perm]
  -- On `Ω`, `‖Dv‖ ≤ C` for `v` `C`-Lipschitz on `Ω`, so every entry of the minor is `≤ C`.
  obtain ⟨B, hB0, hMb⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ v, LipschitzOnWith C v Ω → ∀ w ∈ Ω, |M v w| ≤ B := by
    refine ⟨(Nat.factorial r : ℝ) * (C : ℝ) ^ r, by positivity, fun v hv w hw => ?_⟩
    refine abs_det_le _ C fun t s => ?_
    have hD : ‖fderiv ℝ v w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hv
    calc |EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1))|
        = ‖fderiv ℝ v w (EuclideanSpace.single (b s) 1) (a t)‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ v w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ v w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ := (fderiv ℝ v w).le_opNorm _
      _ ≤ C := by simpa using hD
  have hMm : ∀ v, Measurable (M v) := by
    intro v
    have hdet : Continuous fun A : Fin r → Fin r → ℝ => (Matrix.of A).det :=
      Continuous.matrix_det continuous_id
    have hent : ∀ t s : Fin r, Measurable fun w =>
        EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1)) := fun t s =>
      (EuclideanSpace.proj (a t)).continuous.measurable.comp (measurable_fderiv_apply_const ℝ v _)
    exact hdet.measurable.comp (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => hent t s)
  have hMbd : ∀ j, ∀ᵐ w ∂(volume : Measure (Eucl k)).restrict Ω, ‖M (u j) w‖ ≤ B := fun j =>
    (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
      simpa [Real.norm_eq_abs] using hMb _ (hu j) w hw)
  obtain ⟨G, hG⟩ := hg.bounded_above_of_compact_support hgc
  have hgm : ∀ v, LipschitzOnWith C v Ω →
      AEStronglyMeasurable (fun w => g (v w)) ((volume : Measure (Eucl k)).restrict Ω) :=
    fun v hv => (hg.comp_continuousOn hv.continuousOn).aestronglyMeasurable hΩ.measurableSet
  -- Step 2: integrability.
  let η : Eucl k → ℝ := fun w => ψ w * g (u₀ w)
  have hη : IntegrableOn η Ω (volume : Measure (Eucl k)) :=
    Integrable.mul_bdd hψ (hgm u₀ hu₀) (ae_of_all _ fun w => hG _)
  have hint₁ : ∀ j, IntegrableOn (fun w => ψ w * (g (u j w) - g (u₀ w)) * M (u j) w) Ω
      (volume : Measure (Eucl k)) := fun j =>
    Integrable.mul_bdd (Integrable.mul_bdd (c := G + G) hψ ((hgm _ (hu j)).sub (hgm _ hu₀))
      (ae_of_all _ fun w => (norm_sub_le _ _).trans (add_le_add (hG _) (hG _))))
      (hMm _).aestronglyMeasurable (hMbd j)
  have hint₂ : ∀ j, IntegrableOn (fun w => η w * M (u j) w) Ω (volume : Measure (Eucl k)) :=
    fun j => Integrable.mul_bdd hη (hMm _).aestronglyMeasurable (hMbd j)
  -- Step 3: `∫_Ω ψ (g ∘ u_j) M_j = D₁(j) + ∫_Ω η M_j`.
  have hsplit : ∀ j, ∫ w in Ω, ψ w * g (u j w) * M (u j) w ∂(volume : Measure (Eucl k)) =
      (∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w ∂(volume : Measure (Eucl k))) +
        ∫ w in Ω, η w * M (u j) w ∂(volume : Measure (Eucl k)) := by
    intro j
    rw [← integral_add (hint₁ j) (hint₂ j)]
    congr 1
    funext w
    simp only [η]
    ring
  -- Step 4: `D₁(j) → 0`, as `g ∘ u_j → g ∘ u₀` uniformly on `Ω` and `|M_j| ≤ B` there.
  have hunif : TendstoUniformlyOn (fun j w => g (u j w)) (fun w => g (u₀ w)) atTop Ω :=
    (hgc.uniformContinuous_of_continuous hg).comp_tendstoUniformlyOn hconv
  obtain ⟨I, hI0, hI⟩ : ∃ I : ℝ, 0 ≤ I ∧ ∫ w in Ω, |ψ w| ∂(volume : Measure (Eucl k)) = I :=
    ⟨_, integral_nonneg fun w => abs_nonneg _, rfl⟩
  have hD₁ : Tendsto (fun j => ∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w
      ∂(volume : Measure (Eucl k))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hBI : 0 < B * I + 1 := by positivity
    obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * (B * I + 1) = ε :=
      ⟨ε / (B * I + 1), div_pos hε hBI, div_mul_cancel₀ ε hBI.ne'⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif δ hδ0)
    refine ⟨N, fun j hj => ?_⟩
    have hbound : ∀ᵐ w ∂(volume : Measure (Eucl k)).restrict Ω,
        ‖ψ w * (g (u j w) - g (u₀ w)) * M (u j) w‖ ≤ δ * B * |ψ w| := by
      refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
      have e₁ : |g (u j w) - g (u₀ w)| ≤ δ := by
        rw [← Real.dist_eq, dist_comm]
        exact (hN j hj w hw).le
      have e₂ := hMb _ (hu j) w hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |ψ w| * |g (u j w) - g (u₀ w)| * |M (u j) w| ≤ |ψ w| * δ * B := by gcongr
        _ = δ * B * |ψ w| := by ring
    rw [dist_zero_right]
    calc ‖∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w ∂(volume : Measure (Eucl k))‖
        ≤ ∫ w in Ω, δ * B * |ψ w| ∂(volume : Measure (Eucl k)) :=
          norm_integral_le_of_norm_le (hψ.abs.const_mul _) hbound
      _ = δ * (B * I) := by rw [integral_const_mul, hI]; ring
      _ < δ * (B * I + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ0
      _ = ε := hδε
  -- Step 5: the sibling `minor_weak_star` tested against `η ∈ L¹(Ω)`.
  have hη₂ :=
    Submission.deformation_ipl_mwc_minor_weak_star k Q Ω C u u₀ hΩ hu hu₀ hconv r a b η hη
  -- Step 6: conclusion.
  have hlim := hD₁.add hη₂
  rw [zero_add] at hlim
  exact hlim.congr fun j => (hsplit j).symm

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
