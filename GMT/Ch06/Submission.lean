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

/-- A translation estimate `∫ |u(x + h) − u(x)| dx ≤ ‖h‖ Λ` bounds the double integral over
`r`-balls: `∫_x ∫_{closedBall(x, r)} |u(x) − u(y)| dy dx ≤ r Λ |closedBall(0, r)|`.
Substituting `y = x + h` turns the inner integral into `∫ 1_B(h) |u(x + h) − u(x)| dh` with
`B = closedBall(0, r)`; Tonelli swaps the integrals, and on `B` the hypothesis and `‖h‖ ≤ r`
bound the inner `x`-integral by `r Λ`. -/
theorem Submission.fiw_tb_tda_ps_translation_ball :
    ∀ (n : ℕ) (u : Eucl n → ℝ) (Λ : ℝ≥0∞) (r : ℝ), Measurable u →
      (∀ h : Eucl n, ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| ≤
        ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r) := by
  intro n u Λ r hu hΛ
  set B : Set (Eucl n) := closedBall 0 r
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- `x + h ∈ closedBall x r ↔ h ∈ closedBall 0 r`.
  have hmem : ∀ x h : Eucl n, x + h ∈ closedBall x r ↔ h ∈ B := by
    intro x h
    simp [B, mem_closedBall, dist_eq_norm]
  -- Substituting `y = x + h` in the inner integral.
  have hsub : ∀ x : Eucl n, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| =
      ∫⁻ h, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| := by
    intro x
    rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_left_eq_self
      ((closedBall x r).indicator fun y => ENNReal.ofReal |u x - u y|) x]
    refine lintegral_congr fun h => ?_
    by_cases hh : h ∈ B
    · rw [indicator_of_mem ((hmem x h).2 hh), indicator_of_mem hh, Pi.one_apply, one_mul,
        abs_sub_comm]
    · rw [indicator_of_notMem (fun h' => hh ((hmem x h).1 h')), indicator_of_notMem hh, zero_mul]
  -- The integrand is jointly measurable.
  have hk : Measurable fun p : Eucl n × Eucl n =>
      B.indicator 1 p.2 * ENNReal.ofReal |u (p.1 + p.2) - u p.1| :=
    ((measurable_one.indicator hBm).comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp ((hu.comp measurable_add).sub (hu.comp measurable_fst))))
  calc ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y|
      = ∫⁻ x, ∫⁻ h, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_congr fun x => hsub x
    _ = ∫⁻ h, ∫⁻ x, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_lintegral_swap hk.aemeasurable
    _ = ∫⁻ h, B.indicator 1 h * ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_congr fun h => lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp ((hu.comp (measurable_add_const h)).sub hu)))
    _ ≤ ∫⁻ h, B.indicator (fun _ => ENNReal.ofReal r * Λ) h := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ B
        · rw [indicator_of_mem hh, indicator_of_mem hh, Pi.one_apply, one_mul]
          refine (hΛ h).trans ?_
          gcongr
          exact mem_closedBall_zero_iff.1 hh
        · rw [indicator_of_notMem hh, indicator_of_notMem hh, zero_mul]
    _ = ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r) :=
        lintegral_indicator_const hBm _
/-- Box bound for the volume of a Euclidean ball, used in `fiw_tb_tda_poincare_sum`:
`closedBall(0, r) ⊆ [-r, r]ⁿ`, hence `Lⁿ(closedBall(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_ps_ball_volume_le : ∀ (n : ℕ) (r : ℝ), 0 ≤ r → volume (closedBall (0 : Eucl n) r) ≤ ENNReal.ofReal ((2 * r) ^ n) := by
  intro n r hr
  -- Steps 1–2: `|xᵢ| ≤ ‖x‖ ≤ r`, so `closedBall(0, r) ⊆ ofLp⁻¹(Icc(-r, r))`.
  have hsub : closedBall (0 : Eucl n) r ⊆
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => -r) (fun _ : Fin n => r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    have hcoord : ∀ i, |x i| ≤ r := fun i => by
      have h := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h
      exact h.trans hx
    exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
  -- Steps 3–4: `ofLp` preserves volume, and the box has volume `ofReal (2r) ^ n = ofReal ((2r)ⁿ)`.
  calc volume (closedBall (0 : Eucl n) r)
      ≤ volume (WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => -r) (fun _ : Fin n => r)) :=
        measure_mono hsub
    _ = volume (Icc (fun _ : Fin n => -r) (fun _ : Fin n => r)) :=
        (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ENNReal.ofReal ((2 * r) ^ n) := by
        rw [Real.volume_Icc_pi, ENNReal.ofReal_pow (by linarith)]
        simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, two_mul]
/-- Top-dimensional lattice cubes in `ℝⁿ`, `n = m + 1`, `ρ > 0`.  The only order embedding
`Fin n ↪o Fin n` is the identity, so `latticeFace ρ F` is the closed cube `ρ (F.1 + [0, 1]ⁿ)`:
it is closed, has volume `ρⁿ` and diameter at most `√n ρ`.  The hyperplanes `{xᵢ = ρ k}` are
null, the cubes cover `ℝⁿ` and two distinct cubes only meet inside these hyperplanes, so
lower integrals and integrals of integrable functions split as sums over the cubes. -/
theorem Submission.fiw_tb_tda_lattice_cubes :
    ∀ (m : ℕ) (ρ : ℝ), 0 < ρ →
      (∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
        {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)}) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F)) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1),
        volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1))) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F, ∀ y ∈ latticeFace ρ F,
        dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) ∧
      (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) ∧
      (∀ g : Eucl (m + 1) → ℝ≥0∞, ∫⁻ x, g x =
        ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x) ∧
      ∀ f : Eucl (m + 1) → ℝ, Integrable f →
        ∫ x, f x = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x := by
  intro m ρ hρ
  -- (a) A strictly monotone self-map of the finite chain `Fin (m + 1)` is the identity.
  have ha : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j :=
    fun F _ => F.2.strictMono.apply_eq
  -- (b) Every coordinate lies in `range F.2`, so the face is the closed cube.
  have hb : ∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
      {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)} := by
    intro F
    have hr : ∀ i, i ∈ range F.2 := fun i => ⟨i, ha F i⟩
    ext x
    simp only [latticeFace, mem_ofPred_eq, hr, not_true_eq_false, true_implies, false_implies,
      and_true]
  -- The cube is the preimage of a box under the volume-preserving `WithLp.ofLp`.
  have hbox : ∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
      WithLp.ofLp ⁻¹' Icc (fun i => ρ * (F.1 i : ℝ)) (fun i => ρ * ((F.1 i : ℝ) + 1)) := by
    intro F
    rw [hb F]
    ext x
    simp [Pi.le_def, forall_and]
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  -- (c) The cube is measurable.
  have hc : ∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F) := by
    intro F
    rw [hbox F]
    exact hvol.measurable measurableSet_Icc
  -- (d) Its volume is `∏ᵢ ρ = ρ^(m + 1)`.
  have hd : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1)) := by
    intro F
    rw [hbox F, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    have hside : ∀ i : Fin (m + 1), ρ * ((F.1 i : ℝ) + 1) - ρ * (F.1 i : ℝ) = ρ := fun i => by
      ring
    simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hρ.le]
  -- (e) Coordinates of two points of the cube differ by at most `ρ`.
  have he : ∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F,
      ∀ y ∈ latticeFace ρ F, dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ := by
    intro F x hx y hy
    rw [hb F] at hx hy
    have hcoord : ∀ i, dist (x i) (y i) ^ 2 ≤ ρ ^ 2 := by
      intro i
      refine pow_le_pow_left₀ dist_nonneg ?_ 2
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * ρ ^ 2 := by
      calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin (m + 1), ρ ^ 2 :=
            Finset.sum_le_sum fun i _ => hcoord i
        _ = ((m + 1 : ℕ) : ℝ) * ρ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [EuclideanSpace.dist_eq]
    calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * ρ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hρ.le]
  -- (f) Each hyperplane `{xᵢ = ρ k}` is the `WithLp.ofLp`-preimage of a null hyperplane.
  have hf : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro k
    have hnull : (volume : Measure (Eucl (m + 1))) {x | x i = ρ * k} = 0 :=
      hvol.quasiMeasurePreserving.preimage_null
        (Measure.pi_hyperplane (fun _ : Fin (m + 1) => (volume : Measure ℝ)) i (ρ * k))
    rw [ae_iff]
    simpa using hnull
  -- A point of a cube off the hyperplanes determines the lattice point: `⌊xᵢ / ρ⌋ = F.1 i`.
  have hfloor : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (x : Eucl (m + 1)),
      x ∈ latticeFace ρ F → (∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) →
        ∀ i, ⌊x i / ρ⌋ = F.1 i := by
    intro F x hx hgood i
    rw [hb F] at hx
    obtain ⟨h1, h2⟩ := hx i
    have h3 : x i ≠ ρ * ((F.1 i + 1 : ℤ) : ℝ) := hgood i (F.1 i + 1)
    push_cast at h3
    have h4 : x i < ρ * ((F.1 i : ℝ) + 1) := lt_of_le_of_ne h2 h3
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hρ]
      linarith
    · rw [div_lt_iff₀ hρ]
      linarith
  -- The cubes cover `ℝ^(m + 1)`: `x` lies in the cube at `(⌊xᵢ / ρ⌋)ᵢ`.
  have hU : (⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    refine ⟨(fun i => ⌊x i / ρ⌋, OrderEmbedding.ofStrictMono id strictMono_id), ?_⟩
    rw [hb]
    intro i
    constructor
    · have h := Int.floor_le (x i / ρ)
      rw [le_div_iff₀ hρ] at h
      linarith
    · have h := Int.lt_floor_add_one (x i / ρ)
      rw [div_lt_iff₀ hρ] at h
      linarith
  -- Distinct cubes have distinct lattice points, so they only meet in the null hyperplanes.
  have hbad : (volume : Measure (Eucl (m + 1)))
      {x | ¬ ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k} = 0 := ae_iff.1 hf
  have hdisj : Pairwise (Function.onFun (AEDisjoint (volume : Measure (Eucl (m + 1))))
      fun F : LatticeFaceIndex (m + 1) (m + 1) => latticeFace ρ F) := by
    intro F G hFG
    refine measure_mono_null (fun x hx => ?_) hbad
    intro hgood
    have h2 : F.2 = G.2 := DFunLike.ext _ _ fun j => (ha F j).trans (ha G j).symm
    have h1 : F.1 ≠ G.1 := fun h => hFG (Prod.ext h h2)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact hi ((hfloor F x hx.1 hgood i).symm.trans (hfloor G x hx.2 hgood i))
  refine ⟨ha, hb, hc, hd, he, hf, ?_, ?_⟩
  -- (g) Lower integrals split over the countable, a.e. disjoint cover.
  · intro g
    calc ∫⁻ x, g x = ∫⁻ x in ⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F, g x := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x :=
          lintegral_iUnion₀ (fun F => (hc F).nullMeasurableSet) hdisj g
  -- (h) So do integrals of integrable functions.
  · intro f hfi
    calc ∫ x, f x = ∫ x in ⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F, f x := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x :=
          integral_iUnion_ae (fun F => (hc F).nullMeasurableSet) hdisj (by
            rw [hU]
            exact hfi.integrableOn)

/-- Summed Poincaré bound over the top-dimensional lattice cubes of `ℝⁿ`, `n = m + 1`, with
`c = (2√n)ⁿ √n`.  A cube lies in the closed ball of radius `√n ρ` about any of its points, so
summing over the a.e. partition into cubes bounds the left side by
`ρ⁻ⁿ ∫⁻ₓ ∫⁻_{B(x, √n ρ)} |u x - u y|`.  The translation estimate bounds this double integral by
`√n ρ Λ L(B(0, √n ρ))`, and `L(B(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_poincare_sum :
    ∀ m : ℕ, ∃ c : ℝ≥0, ∀ (ρ : ℝ), 0 < ρ → ∀ (u : Eucl (m + 1) → ℝ) (Λ : ℝ≥0∞), Measurable u →
      (∀ h : Eucl (m + 1), ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        c * ENNReal.ofReal ρ * Λ := by
  intro m
  -- `s = √n` and `c = (2s)ⁿ s`.
  obtain ⟨s, hs, hs_def⟩ : ∃ s : ℝ, 0 ≤ s ∧ Real.sqrt ((m + 1 : ℕ) : ℝ) = s :=
    ⟨_, Real.sqrt_nonneg _, rfl⟩
  have hC : 0 ≤ (2 * s) ^ (m + 1) * s := by positivity
  refine ⟨NNReal.mk ((2 * s) ^ (m + 1) * s) hC, fun ρ hρ u Λ hu hΛ => ?_⟩
  obtain ⟨-, -, hc, -, he, -, hg, -⟩ := Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  rw [hs_def] at he
  have hr : 0 ≤ s * ρ := mul_nonneg hs hρ.le
  -- Step 1: a cube lies in the closed ball of radius `s ρ` about any of its points.
  have hcube : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
    fun F => setLIntegral_mono' (hc F) fun x hx =>
      lintegral_mono_set fun y hy => mem_closedBall.2 (he F y hy x hx)
  -- Step 6 (arithmetic): `(ρⁿ)⁻¹ (s ρ) (2 s ρ)ⁿ = (2s)ⁿ s ρ`.
  have hinv : 0 ≤ (ρ ^ (m + 1))⁻¹ := by positivity
  have hconst : (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1) =
      (2 * s) ^ (m + 1) * s * ρ := by
    calc (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)
        = (2 * s) ^ (m + 1) * s * ρ * ((ρ ^ (m + 1))⁻¹ * ρ ^ (m + 1)) := by ring
      _ = (2 * s) ^ (m + 1) * s * ρ := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), mul_one]
  calc ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y|
      ≤ ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
        ENNReal.tsum_le_tsum fun F => by gcongr _ * ?_; exact hcube F
    -- Step 2: the cubes form an a.e. partition of `ℝⁿ`.
    _ = ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| := by
        rw [ENNReal.tsum_mul_left, hg]
    -- Steps 3–5: the translation estimate and the volume of the ball.
    _ ≤ ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          (ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1))) := by
        gcongr _ * ?_
        calc ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y|
            ≤ ENNReal.ofReal (s * ρ) * Λ * volume (closedBall (0 : Eucl (m + 1)) (s * ρ)) :=
              Submission.fiw_tb_tda_ps_translation_ball (m + 1) u Λ (s * ρ) hu hΛ
          _ ≤ ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1)) := by
              gcongr _ * ?_
              exact Submission.fiw_tb_tda_ps_ball_volume_le (m + 1) (s * ρ) hr
    -- Step 6: collect the constants.
    _ = ENNReal.ofReal ((ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)) * Λ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hinv hr), ENNReal.ofReal_mul hinv]
        ring
    _ = ENNReal.ofReal ((2 * s) ^ (m + 1) * s) * ENNReal.ofReal ρ * Λ := by
        rw [hconst, ENNReal.ofReal_mul hC]
    _ = _ := by rw [ENNReal.ofReal_eq_coe_nnreal hC]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
