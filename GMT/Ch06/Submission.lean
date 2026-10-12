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

/-- Unit simple `n`-vectors orienting the same `n`-plane agree up to sign (the orientations
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of Simon Ch. 6, 3.1), given the simple `n`-vector algebra
`‖v₁ ∧ ⋯ ∧ vₙ‖² = det(⟨vᵢ, vⱼ⟩)` and `(∑ⱼ B₁ⱼ τⱼ) ∧ ⋯ ∧ (∑ⱼ Bₙⱼ τⱼ) = det B · τ₁ ∧ ⋯ ∧ τₙ`.
An orthonormal `σ` has Gram matrix `1`, so `‖σ₁ ∧ ⋯ ∧ σₙ‖ = 1`.  If `σ, σ'` span the same
plane, then `σ'ᵢ = ∑ⱼ Bᵢⱼ σⱼ`, so `σ'₁ ∧ ⋯ ∧ σ'ₙ = det B · σ₁ ∧ ⋯ ∧ σₙ`, and taking norms
gives `|det B| = 1`. -/
theorem Submission.lpf_pi_simple_unit_facts :
    ((∀ (P n : ℕ) (v : Fin n → Eucl P),
        ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧
      ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
        simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) →
    (∀ (Q n : ℕ) (σ : Fin n → Eucl Q), Orthonormal ℝ σ → ‖simpleNVector σ‖ = 1) ∧
      ∀ (Q n : ℕ) (σ σ' : Fin n → Eucl Q), Orthonormal ℝ σ → Orthonormal ℝ σ' →
        Submodule.span ℝ (range σ) = Submodule.span ℝ (range σ') →
          simpleNVector σ' = simpleNVector σ ∨ simpleNVector σ' = -simpleNVector σ := by
  rintro ⟨hgram, hdet⟩
  -- An orthonormal family has Gram matrix `1`, so `‖σ₁ ∧ ⋯ ∧ σₙ‖² = det 1 = 1`.
  have hunit : ∀ (Q n : ℕ) (σ : Fin n → Eucl Q), Orthonormal ℝ σ → ‖simpleNVector σ‖ = 1 := by
    intro Q n σ hσ
    have hG : (Matrix.of fun i j => inner ℝ (σ i) (σ j)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hσ i j]
    have h := hgram Q n σ
    rw [hG, Matrix.det_one] at h
    exact (pow_eq_one_iff_of_nonneg (ContinuousLinearMap.opNorm_nonneg _) two_ne_zero).mp h
  refine ⟨hunit, fun Q n σ σ' hσ hσ' hspan => ?_⟩
  -- `‖c • w‖ = |c| ‖w‖` for `n`-vectors, from `opNorm_smul_le` for `c` and `c⁻¹`
  -- (instance search does not find `NormSMulClass ℝ (NVector _ n)`, so no `norm_smul`).
  have hnorm_smul : ∀ (c : ℝ) (w : NVector (Eucl Q) n), ‖c • w‖ = |c| * ‖w‖ := by
    intro c w
    apply le_antisymm
    · simpa [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c w
    · rcases eq_or_ne c 0 with rfl | hc
      · rw [abs_zero, zero_mul]
        exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • w)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv, Real.norm_eq_abs] at h
        exact (le_inv_mul_iff₀ (abs_pos.mpr hc)).mp h
  -- Expand `σ'ᵢ = ∑ⱼ Bᵢⱼ σⱼ` in the common span: `σ'₁ ∧ ⋯ ∧ σ'ₙ = det B · σ₁ ∧ ⋯ ∧ σₙ`.
  have hmem : ∀ i, σ' i ∈ Submodule.span ℝ (range σ) := fun i => by
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose B hB using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem i)
  have hexp : (fun i => ∑ j, B i j • σ j) = σ' := funext hB
  have key : simpleNVector σ' = Matrix.det B • simpleNVector σ := by
    rw [← hexp]
    exact hdet Q n B σ
  -- Taking norms, `|det B| = 1`, so `det B = ±1`.
  have habs : |Matrix.det B| = 1 :=
    calc |Matrix.det B| = |Matrix.det B| * ‖simpleNVector σ‖ := by rw [hunit Q n σ hσ, mul_one]
      _ = ‖simpleNVector σ'‖ := by rw [key, hnorm_smul]
      _ = 1 := hunit Q n σ' hσ'
  rcases (abs_eq zero_le_one).mp habs with h | h
  · left
    rw [key, h, one_smul]
  · right
    rw [key, h]
    exact neg_one_smul ℝ (simpleNVector σ)

/-- The orientation induced by a linear map (Simon Ch. 6, 3.4–3.5, p. 147, at a single point):
if `τ` is orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₙ` and `A_# w ≠ 0`, then `Aτ₁, …, Aτₙ` are linearly
independent, and for their Gram–Schmidt orthonormalization `σ` (same span)
`A_# w = ±|A_# w| σ₁ ∧ ⋯ ∧ σₙ`.  Writing `Aτᵢ = ∑ⱼ Bᵢⱼ σⱼ`, the determinant identity of the
hypothesis gives `A_# w = ±det B σ₁ ∧ ⋯ ∧ σₙ`, and `|σ₁ ∧ ⋯ ∧ σₙ| = 1`
(`Submission.lpf_pi_simple_unit_facts`), so `|A_# w| = |det B|`. -/
theorem Submission.lpf_pi_induced_orientation :
    ((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 =
        (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧
      ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
        simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) →
    ∀ (P Q n : ℕ) (τ : Fin n → Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (w : NVector (Eucl P) n),
      Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) →
      nVectorPushforward n A w ≠ 0 →
      LinearIndependent ℝ (fun i => A (τ i)) ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧
        Submodule.span ℝ (range σ) = Submodule.span ℝ (range (fun i => A (τ i))) ∧
        (nVectorPushforward n A w = ‖nVectorPushforward n A w‖ • simpleNVector σ ∨
          nVectorPushforward n A w = -(‖nVectorPushforward n A w‖ • simpleNVector σ)) := by
  intro hsna P Q n τ A w _hτ hw hne
  -- `‖c • s‖ = |c| ‖s‖` for the operator norm on `n`-vectors (`NormSMulClass` is not inferred).
  have hnorm_smul : ∀ (c : ℝ) (s : NVector (Eucl Q) n), ‖c • s‖ = |c| * ‖s‖ := by
    intro c s
    apply le_antisymm
    · simpa [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c s
    · rcases eq_or_ne c 0 with rfl | hc
      · simp only [abs_zero, zero_mul]
        exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • s)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv, Real.norm_eq_abs] at h
        have hc' : 0 < |c| := abs_pos.mpr hc
        calc |c| * ‖s‖ ≤ |c| * (|c|⁻¹ * ‖c • s‖) := by gcongr
          _ = ‖c • s‖ := by rw [← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]
  set v : Fin n → Eucl Q := fun i => A (τ i)
  -- `A_# w = ε • (Aτ₁ ∧ ⋯ ∧ Aτₙ)` with `ε = ±1`.
  have hsimple : nVectorPushforward n A (simpleNVector τ) = simpleNVector v :=
    nVectorPushforward_simple A τ
  obtain ⟨ε, hpush⟩ : ∃ ε : ℝ, nVectorPushforward n A w = ε • simpleNVector v := by
    rcases hw with rfl | rfl
    · exact ⟨1, by rw [hsimple, one_smul]⟩
    · refine ⟨-1, ?_⟩
      ext α
      show -(α (fun i => A (τ i))) = (-1 : ℝ) * α (fun i => A (τ i))
      ring
  -- (i): covectors vanish on linearly dependent families, so `Aτ₁ ∧ ⋯ ∧ Aτₙ` would be `0`.
  have hli : LinearIndependent ℝ v := by
    by_contra h
    apply hne
    have h0 : simpleNVector v = 0 := by
      ext α
      simp only [simpleNVector_apply]
      exact α.toAlternatingMap.map_linearDependent v h
    rw [hpush, h0, smul_zero]
  refine ⟨hli, ?_⟩
  -- (ii): the Gram–Schmidt orthonormalization `σ` of `Aτ` spans the same space.
  set σ := InnerProductSpace.gramSchmidtNormed ℝ v
  have hσ : Orthonormal ℝ σ := InnerProductSpace.gramSchmidtNormed_orthonormal hli
  have hspan : Submodule.span ℝ (range σ) = Submodule.span ℝ (range v) :=
    (InnerProductSpace.span_gramSchmidtNormed_range v).trans
      (InnerProductSpace.span_gramSchmidt ℝ v)
  refine ⟨σ, hσ, hspan, ?_⟩
  -- `Aτᵢ = ∑ⱼ Bᵢⱼ σⱼ`, so `Aτ₁ ∧ ⋯ ∧ Aτₙ = det B • σ₁ ∧ ⋯ ∧ σₙ`.
  have hmem : ∀ i, v i ∈ Submodule.span ℝ (range σ) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, ∀ i, ∑ j, B i j • σ j = v i := by
    choose B hB using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem i)
    exact ⟨B, hB⟩
  have hdet := hsna.2 Q n B σ
  rw [show (fun i => ∑ j, B i j • σ j) = v from funext hB] at hdet
  have hpush' : nVectorPushforward n A w = (ε * B.det) • simpleNVector σ := by
    rw [hpush, hdet, smul_smul]
  -- `‖σ₁ ∧ ⋯ ∧ σₙ‖ = 1`, so `‖A_# w‖ = |ε det B|`; the sign of `ε det B` decides the case.
  have hnorm : ‖nVectorPushforward n A w‖ = |ε * B.det| := by
    rw [hpush', hnorm_smul, (Submission.lpf_pi_simple_unit_facts hsna).1 Q n σ hσ, mul_one]
  rcases le_or_gt 0 (ε * B.det) with h | h
  · left
    rw [hnorm, abs_of_nonneg h]
    exact hpush'
  · right
    rw [hnorm, abs_of_neg h, hpush']
    ext α
    show (ε * B.det) * simpleNVector σ α = -(-(ε * B.det) * simpleNVector σ α)
    ring

/-- Source charts for Simon Ch. 6, Lemma 3.9 (p. 148): under (SNA), (CRC), (CCR) and (LCIP),
countably many `C¹` maps `G k`, antilipschitz on open `O k`, carry the push-forward orientation:
for `Hⁿ`-a.e. `x ∈ M` with `L(x)_# ξ(x) ≠ 0` there are `k` and `w ∈ O k` with `G k w = f x` and
`L(x)_# ξ(x) = ±‖L(x)_# ξ(x)‖ σ₁ ∧ ⋯ ∧ σₙ` for an orthonormal basis `σ` of `range DG_k(w)`. -/
theorem Submission.lpf_pi_source_charts : ((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → (∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0) → (∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), HasWeightedApproximateTangentSpaceAt n M θ (Φ w) (LinearMap.range (fderiv ℝ Φ w).toLinearMap) ∧ HasFDerivAt (f ∘ Φ) ((L (Φ w)).comp (fderiv ℝ Φ w)) w) → (∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → ∃ (G : ℕ → Eucl n → Eucl Q) (O E : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ (∀ k, MeasurableSet (E k)) ∧ (∀ k, E k ⊆ O k ∩ Ω) ∧ Pairwise (Function.onFun Disjoint E) ∧ (∀ k, ∀ w ∈ E k, u w = G k w ∧ HasFDerivAt u (fderiv ℝ (G k) w) w) ∧ ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω → (∃ D : Eucl n →L[ℝ] Eucl Q, HasFDerivAt u D w ∧ Function.Injective D) → w ∈ ⋃ k, E k) → ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → ∃ (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), nVectorPushforward n (L x) (ξ x) ≠ 0 → ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧ (nVectorPushforward n (L x) (ξ x) = ‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ ∨ nVectorPushforward n (L x) (ξ x) = -(‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ)) := by
  intro hsna CRC CCR LCIP P Q n U M θ ξ f L hU htri hf hderiv
  -- antilipschitz chart preimage of an Hⁿ-null set is Lⁿ-null
  have hnull : ∀ (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c →
      (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ (Z : Set (Eucl P)),
      (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
    intro Φ Ω c hc hanti Z hZ
    classical
    have hinj : InjOn Φ Ω := by
      intro w hw w' hw' h
      have h1 := hanti w hw w' hw'
      rw [h, sub_self, norm_zero] at h1
      have h2 : ‖w - w'‖ ≤ 0 := by
        by_contra hcon
        linarith [mul_pos hc (not_le.mp hcon)]
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
    have hΨlip : LipschitzOnWith (Real.toNNReal c⁻¹) (Function.invFunOn Φ Ω) (Φ '' Ω) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      rw [hinj.leftInvOn_invFunOn hw, hinj.leftInvOn_invFunOn hw', dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hanti w hw w' hw'
    have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω) := by
      rintro w ⟨hw, hwZ⟩
      exact ⟨Φ w, ⟨hwZ, w, hw, rfl⟩, hinj.leftInvOn_invFunOn hw⟩
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    apply measure_mono_null hsub
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl n)) (Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω))
        ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) ^ n * μHE[n] (Z ∩ Φ '' Ω) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hΨlip.mono inter_subset_right)
      _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
  -- linear algebra of step 6(iv)-(v)
  have hlinalg : ∀ (D : Eucl n →L[ℝ] Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (τ : Fin n → Eucl P),
      LinearMap.range D.toLinearMap = Submodule.span ℝ (range τ) →
      LinearIndependent ℝ (fun i => A (τ i)) →
      Function.Injective (A.comp D) ∧
        LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
    intro D A τ hD hAτ
    have hrange : LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
      rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, hD, Submodule.map_span, ← range_comp]
      rfl
    refine ⟨?_, hrange⟩
    have hfr : Module.finrank ℝ (LinearMap.range (A.comp D).toLinearMap) = n := by
      rw [hrange, finrank_span_eq_card hAτ, Fintype.card_fin]
    have hker := LinearMap.finrank_range_add_finrank_ker (A.comp D).toLinearMap
    rw [hfr, finrank_euclideanSpace_fin] at hker
    have hker0 : Module.finrank ℝ (LinearMap.ker (A.comp D).toLinearMap) = 0 := by omega
    have : LinearMap.ker (A.comp D).toLinearMap = ⊥ := Submodule.finrank_eq_zero.mp hker0
    exact LinearMap.ker_eq_bot.mp this
  -- covering argument of steps 1, 4, 7
  have hcover_null : ∀ (Φ : ℕ → Eucl n → Eucl P) (Ω Ω' : ℕ → Set (Eucl n)), (∀ j, Ω' j ⊆ Ω j) →
      (∀ j, ∀ w ∈ Ω j, Φ j w ∈ M → w ∈ Ω' j) →
      (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) →
      (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 →
      ∀ (good : Eucl P → Prop),
      (∀ j, (volume : Measure (Eucl n)) {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} = 0) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), good x := by
    intro Φ Ω Ω' hΩ'sub hΩ'cov hΦlip hcover good hbad
    rw [ae_iff, Measure.restrict_apply₀' htri.nullMeasurableSet]
    have hsub : {x | ¬ good x} ∩ M ⊆
        (M \ ⋃ j, Φ j '' Ω j) ∪ ⋃ j, Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} := by
      rintro x ⟨hx, hxM⟩
      by_cases hc : x ∈ ⋃ j, Φ j '' Ω j
      · right
        obtain ⟨j, hj⟩ := mem_iUnion.mp hc
        obtain ⟨w, hw, rfl⟩ := hj
        exact mem_iUnion.mpr ⟨j, w, ⟨hΩ'cov j w hw hxM, hxM, hx⟩, rfl⟩
      · left; exact ⟨hxM, hc⟩
    refine measure_mono_null hsub (measure_union_null hcover (measure_iUnion_null fun j => ?_))
    obtain ⟨K, hK⟩ := hΦlip j
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl P)) (Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hK.mono fun w hw => hΩ'sub j hw.1)
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbad j, mul_zero]
  have hio := Submission.lpf_pi_induced_orientation hsna
  obtain ⟨Φ, Ω, hΩo, hΦc, hΦlip, hΦanti, hcover⟩ := CRC P n M htri.countablyRectifiable
  have hΩ'o : ∀ j, IsOpen (Ω j ∩ Φ j ⁻¹' U) := fun j =>
    (hΩo j).inter ((hΦc j).continuous.isOpen_preimage U hU)
  have hΦanti' : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j ∩ Φ j ⁻¹' U, ∀ w' ∈ Ω j ∩ Φ j ⁻¹' U,
      c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖ := by
    intro j
    obtain ⟨c, hc, h⟩ := hΦanti j
    exact ⟨c, hc, fun w hw w' hw' => h w hw.1 w' hw'.1⟩
  have hloc : ∀ j, LocallyLipschitzOn (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) := by
    intro j w hw
    obtain ⟨K, hK⟩ := hΦlip j
    obtain ⟨Λ, t, ht, hft⟩ := hf hw.2
    rw [hU.nhdsWithin_eq hw.2] at ht
    refine ⟨Λ * K, (Ω j ∩ Φ j ⁻¹' U) ∩ Φ j ⁻¹' t,
      inter_mem_nhdsWithin _ ((hΦc j).continuous.continuousAt.preimage_mem_nhds ht), ?_⟩
    exact hft.comp (hK.mono fun w hw => hw.1.1) fun w hw => hw.2
  choose G O E hOo hGc hGanti hEm hEsub hEdisj hEeq hEcov using
    fun j => LCIP n Q (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) (hΩ'o j) (hloc j)
  refine ⟨fun m => G m.unpair.1 m.unpair.2, fun m => O m.unpair.1 m.unpair.2,
    fun m => hOo _ _, fun m => hGc _ _, fun m => hGanti _ _, ?_⟩
  have hR : (μHE[n] : Measure (Eucl P)) ({x | ¬ ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
      (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp htri.orients).le) zero_le
  apply hcover_null Φ Ω (fun j => Ω j ∩ Φ j ⁻¹' U)
    (fun j => inter_subset_left) (fun j w hw hwM => ⟨hw, htri.subset hwM⟩) hΦlip hcover
  intro j
  have hCCR := CCR P Q n U M θ ξ f L (Φ j) (Ω j ∩ Φ j ⁻¹' U) hU htri hf hderiv (hΩ'o j) (hΦc j)
    (hΦanti' j)
  have hZa := le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp hCCR).le) zero_le
  obtain ⟨c, hc, hanti⟩ := hΦanti' j
  have hZb := hnull (Φ j) (Ω j ∩ Φ j ⁻¹' U) c hc hanti _ hR
  have hZc := ae_iff.mp (hEcov j)
  refine measure_mono_null ?_ (measure_union_null (measure_union_null hZa hZb) hZc)
  rintro w ⟨hw, hxM, hng⟩
  obtain ⟨hΞ, hngood⟩ := not_imp.mp hng
  by_cases ha : HasWeightedApproximateTangentSpaceAt n M θ (Φ j w)
      (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
      HasFDerivAt (f ∘ Φ j) ((L (Φ j w)).comp (fderiv ℝ (Φ j) w)) w
  swap
  · exact Or.inl (Or.inl ⟨ha, hw, hxM⟩)
  by_cases hb : ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ (Φ j w) (Submodule.span ℝ (range τ)) ∧
      (ξ (Φ j w) = simpleNVector τ ∨ ξ (Φ j w) = -simpleNVector τ)
  swap
  · exact Or.inl (Or.inr ⟨hw, hb, hxM⟩)
  refine Or.inr ?_
  show ¬ _
  intro hc'
  apply hngood
  obtain ⟨τ, hτ, htan, hξ⟩ := hb
  obtain ⟨htanΦ, hfd⟩ := ha
  have huniq : LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap = Submodule.span ℝ (range τ) :=
    htanΦ.unique (htri.pos _ hxM).ne' htan
  obtain ⟨hli, σ, hσ, hσspan, hσeq⟩ := hio P Q n τ (L (Φ j w)) (ξ (Φ j w)) hτ hξ hΞ
  obtain ⟨hinj, hrange⟩ := hlinalg (fderiv ℝ (Φ j) w) (L (Φ j w)) τ huniq hli
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hc' hw ⟨_, hfd, hinj⟩)
  obtain ⟨hueq, hufd⟩ := hEeq j k w hk
  have hDeq : fderiv ℝ (G j k) w = (L (Φ j w)).comp (fderiv ℝ (Φ j) w) := hufd.unique hfd
  refine ⟨Nat.pair j k, w, ?_, ?_, σ, hσ, ?_, hσeq⟩
  · simp only [Nat.unpair_pair]; exact (hEsub j k hk).1
  · simp only [Nat.unpair_pair]; exact hueq.symm
  · simp only [Nat.unpair_pair]; rw [hDeq, hrange, hσspan]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
