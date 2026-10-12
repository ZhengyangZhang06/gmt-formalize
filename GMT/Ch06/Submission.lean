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

/-- The exhaustion function of Simon Ch. 6, 6.2 (p. 169, proof): for open `U ⊆ ℝ^P` there is a
1-Lipschitz `φ` whose superlevel sets `{φ ≥ t}`, `t > 0`, are compact subsets of `U`, and which has
a positive lower bound on every compact `K ⊆ U`.  With `g(x) = 1/(1 + |x|)`, take `φ = g` if
`U = ℝ^P` and `φ = min(dist(·, ℝ^P ∖ U), g)` otherwise. -/
theorem Submission.polyhedral_approx_exhaustion_function : ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ φ : Eucl P → ℝ, LipschitzWith 1 φ ∧ (∀ t : ℝ, 0 < t → IsCompact {x | t ≤ φ x} ∧ {x | t ≤ φ x} ⊆ U) ∧ ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ φ x := by
  intro P U hU
  -- Step 1: `g(x) = 1/(1 + |x|)` is positive and 1-Lipschitz, and `{g ≥ t} ⊆ B̄(0, 1/t)`.
  let g : Eucl P → ℝ := fun x => 1 / (1 + ‖x‖)
  have hg_pos : ∀ x, 0 < g x := fun x => by positivity
  have hg_lip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hx : 0 < 1 + ‖x‖ := by positivity
    have hy : 0 < 1 + ‖y‖ := by positivity
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm,
      div_sub_div _ _ hx.ne' hy.ne', abs_div, abs_of_pos (mul_pos hx hy), div_le_iff₀ (mul_pos hx hy)]
    calc |1 * (1 + ‖y‖) - (1 + ‖x‖) * 1| = |‖y‖ - ‖x‖| := by ring_nf
      _ ≤ ‖y - x‖ := abs_norm_sub_norm_le y x
      _ = ‖x - y‖ := norm_sub_rev y x
      _ ≤ ‖x - y‖ * ((1 + ‖x‖) * (1 + ‖y‖)) :=
        le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [norm_nonneg x, norm_nonneg y])
  have hg_ball : ∀ t : ℝ, 0 < t → ∀ x, t ≤ g x → x ∈ closedBall (0 : Eucl P) (1 / t) := by
    intro t ht x hx
    have h1 : 0 < 1 + ‖x‖ := by positivity
    have h2 : t * (1 + ‖x‖) ≤ 1 := (le_div_iff₀ h1).mp hx
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ ht]
    nlinarith
  -- Steps 2–3 share one argument: a 1-Lipschitz `φ ≤ g`, positive on `U` and `≤ 0` off `U`,
  -- has compact superlevel sets `{φ ≥ t} ⊆ U` and a positive minimum on compact `K ⊆ U`.
  suffices key : ∀ φ : Eucl P → ℝ, LipschitzWith 1 φ → (∀ x, φ x ≤ g x) → (∀ x ∈ U, 0 < φ x) →
      (∀ x, x ∉ U → φ x ≤ 0) → LipschitzWith 1 φ ∧
        (∀ t : ℝ, 0 < t → IsCompact {x | t ≤ φ x} ∧ {x | t ≤ φ x} ⊆ U) ∧
        ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ φ x by
    by_cases hUc : U = univ
    · -- Step 2: `U = ℝ^P`, `φ = g`.
      exact ⟨g, key g hg_lip (fun x => le_rfl) (fun x _ => hg_pos x)
        (fun x hx => absurd (hUc ▸ mem_univ x) hx)⟩
    · -- Step 3: `F = ℝ^P ∖ U` is closed and nonempty, `φ = min(dist(·, F), g)`.
      have hne : (Uᶜ).Nonempty := nonempty_compl.mpr hUc
      have hcl : IsClosed Uᶜ := hU.isClosed_compl
      refine ⟨fun x => min (infDist x Uᶜ) (g x), key _ ?_ (fun x => min_le_right _ _)
        (fun x hx => ?_) (fun x hx => ?_)⟩
      · have h := (lipschitz_infDist_pt Uᶜ).min hg_lip
        rwa [max_self] at h
      · exact lt_min ((hcl.notMem_iff_infDist_pos hne).mp fun h => h hx) (hg_pos x)
      · exact (min_le_left _ _).trans (infDist_zero_of_mem hx).le
  intro φ hφ hφg hφpos hφneg
  refine ⟨hφ, fun t ht => ⟨?_, fun x hx => ?_⟩, fun K hK hKU => ?_⟩
  · -- `{φ ≥ t}` is closed and lies in `B̄(0, 1/t)`.
    exact (isCompact_closedBall (0 : Eucl P) (1 / t)).of_isClosed_subset
      (isClosed_le continuous_const hφ.continuous) fun x hx => hg_ball t ht x (hx.trans (hφg x))
  · -- `φ ≤ 0 < t` off `U`.
    by_contra hxU
    exact absurd (ht.trans_le hx) (not_lt.mpr (hφneg x hxU))
  · -- A positive minimum on `K` (`δ = 1` if `K = ∅`).
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne hφ.continuous.continuousOn
      exact ⟨φ x₀, hφpos x₀ (hKU hx₀K), fun x hx => hmin hx⟩
/-- Boundary mass transfer through a smooth cut-off (Simon Ch. 6, 6.2, proof): if `X` and `A`
agree on any two test forms that coincide on `V`, where `closure V` is a compact subset of the
open set `W ⊆ U₂`, then `M(∂X) ≤ M_W(∂A)`.  For `ψ` admissible for `M(∂X)` and a smooth cut-off
`χ`, `0 ≤ χ ≤ 1`, `χ = 1` near `closure V` with compact support in `W`, the form `χψ` is
admissible for `M_W(∂A)`, and `d(χψ) = dψ` on `V` gives `∂X(ψ) = X(dψ) = A(d(χψ)) = ∂A(χψ)`. -/
theorem Submission.polyhedral_approx_boundary_mass_cutoff : ∀ (P m : ℕ) (U₁ U₂ W V : Set (Eucl P)) (X : GeometricCurrentOn U₁ (m + 1)) (A : GeometricCurrentOn U₂ (m + 1)), IsOpen W → W ⊆ U₂ → IsCompact (closure V) → closure V ⊆ W → (∀ (η : TestFormOn U₁ (m + 1)) (η' : TestFormOn U₂ (m + 1)), (∀ x ∈ V, (η : DifferentialForm (Eucl P) (m + 1)) x = (η' : DifferentialForm (Eucl P) (m + 1)) x) → X η = A η') → X.boundary.mass ≤ A.boundary.massOn W := by
  intro P m U₁ U₂ W V X A hW hWU hV hVW hXA
  -- Step 1: a compact `C = cthickening δ (closure V) ⊆ W` with `closure V ⊆ interior C`.
  obtain ⟨δ, hδ, hCW⟩ := hV.exists_cthickening_subset_open hW hVW
  have hCc : IsCompact (cthickening δ (closure V)) := hV.cthickening
  have hVC : closure V ⊆ interior (cthickening δ (closure V)) :=
    (self_subset_thickening hδ _).trans
      (interior_maximal (thickening_subset_cthickening δ _) isOpen_thickening)
  -- Step 2: smooth Urysohn: `0 ≤ χ ≤ 1`, `χ = 1` near `closure V`, `χ = 0` off `C`.
  obtain ⟨χ, hχ1, hχ0, hχI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Eucl P)) (n := ⊤) isClosed_closure hVC
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : Eucl P → ℝ) :=
    contMDiff_iff_contDiff.mp χ.contMDiff
  -- Step 3: homogeneity of the Euclidean coefficient norm.
  have hhom : ∀ (c : ℝ) (α : Covector (Eucl P) m),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- Step 7: it suffices to bound each admissible evaluation of `∂X`.
  refine sSup_le ?_
  rintro _ ⟨ψ, hψ, rfl⟩
  -- Step 4: the cut-off form `ψ' = χψ` is admissible for `M_W(∂A)`.
  set ψf : DifferentialForm (Eucl P) m := (ψ : DifferentialForm (Eucl P) m)
  let ψ'f : DifferentialForm (Eucl P) m := fun x => χ x • ψf x
  have hψ'0 : ∀ x ∉ cthickening δ (closure V), ψ'f x = 0 := fun x hx => by
    simp only [ψ'f, hχ0 x hx, zero_smul]
  have hψ'C : tsupport ψ'f ⊆ cthickening δ (closure V) :=
    closure_minimal (Function.support_subset_iff'.mpr hψ'0) isClosed_cthickening
  let ψ' : TestFormOn U₂ m :=
    ⟨ψ'f, ⟨⟨hχs.smul ψ.property.1.1, HasCompactSupport.intro hCc hψ'0⟩, hψ'C.trans (hCW.trans hWU)⟩⟩
  have hψ'adm : ψ' ∈ massAdmissibleOn U₂ m W := by
    refine ⟨hψ'C.trans hCW, fun x => ?_⟩
    change covectorEuclideanNorm (χ x • ψf x) ≤ 1
    rw [hhom, abs_of_nonneg (hχI x).1]
    calc χ x * covectorEuclideanNorm (ψf x) ≤ 1 * 1 :=
          mul_le_mul (hχI x).2 (hψ.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- Step 5: `dψ' = dψ` on `V`, since `ψ' = ψ` near every point of `closure V`.
  have hloc : ∀ x ∈ V, extDeriv ψf x = extDeriv ψ'f x := by
    intro x hx
    apply Filter.EventuallyEq.extDeriv_eq
    filter_upwards [nhds_le_nhdsSet (subset_closure hx) hχ1] with y hy
    simp only [ψ'f, hy, one_smul]
  -- Step 6: `∂X(ψ) = X(dψ) = A(dψ') = ∂A(ψ') ≤ M_W(∂A)`.
  have key : X.boundary ψ = A.boundary ψ' := by
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply]
    exact hXA _ _ hloc
  calc ENNReal.ofReal (X.boundary ψ) = ENNReal.ofReal (A.boundary ψ') := by rw [key]
    _ ≤ A.boundary.massOn W := A.boundary.le_massOn hψ'adm
/-- **Kronecker duality of coordinate wedges (Simon Ch. 6, 1.1–1.2).**  For an increasing
multi-index `I`, `dx^I = dx^{I₁} ∧ ⋯ ∧ dx^{Iₙ}` has coordinate `1` at `I` and `0` at every
increasing `J ≠ I`: by (1.1), `dx^I(e_{J₁}, …, e_{Jₙ}) = det [I i = J j]`.  For `J = I` this matrix
is the identity, as `I` is injective.  For `J ≠ I` some `I i ∉ range J` (otherwise the finite
ranges, of equal cardinality, coincide, and increasing enumerations with equal ranges are equal),
so row `i` vanishes. -/
theorem Submission.polyhedral_approx_pairing_wedge_kronecker : ∀ (P n : ℕ) (I : SimonMultiIndex n P), euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) I = 1 ∧ ∀ J : SimonMultiIndex n P, J ≠ I → euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J = 0 := by
  intro P n I
  -- (1)–(2) The coordinate at `J` is the determinant of the matrix `[I i = J j]`.
  have hdet : ∀ J : SimonMultiIndex n P,
      euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        Matrix.det (Matrix.of fun i j => if I i = J j then (1 : ℝ) else 0) := by
    intro J
    rw [euclideanCovectorCoordinate, wedgeCovectors_apply_det]
    congr 1
    ext i j
    simp [PiLp.single_apply]
  refine ⟨?_, fun J hJ => ?_⟩
  · -- (3) For `J = I` the matrix is the identity, as `I` is injective.
    have hone : (Matrix.of fun i j => if I i = I j then (1 : ℝ) else 0) = 1 := by
      ext i j
      simp [Matrix.one_apply, I.injective.eq_iff]
    rw [hdet, hone, Matrix.det_one]
  · -- (4) Some `I i` lies outside `range J`: otherwise `range I = range J` and `I = J`.
    obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
      by_contra h
      have hsub : range I ⊆ range J := by
        rintro _ ⟨i, rfl⟩
        by_contra hi
        exact h ⟨i, fun j hj => hi ⟨j, hj.symm⟩⟩
      have hrange : range I = range J :=
        Set.eq_of_subset_of_ncard_le hsub (by
          rw [Set.ncard_range_of_injective I.injective, Set.ncard_range_of_injective J.injective])
      exact hJ (OrderEmbedding.range_inj_of_wellFoundedLT.mp hrange).symm
    -- (5) Row `i` of the matrix vanishes, so the determinant is `0`.
    rw [hdet]
    exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [hi j]
/-- An `n`-covector on `ℝ^P` is determined by its coordinates on increasing multi-indices
(Simon Ch. 6, 1.2): if `α(e_{I(0)}, …, e_{I(n-1)}) = β(e_{I(0)}, …, e_{I(n-1)})` for every
increasing `I`, then `α = β`.  Alternating maps agreeing on injective tuples of basis vectors are
equal; sorting an injective tuple `v` by `σ = Tuple.sort v` gives the increasing `I = v ∘ σ`, and
`e_v = e_I ∘ σ⁻¹` gives `γ(e_v) = sign(σ⁻¹) γ(e_I)` for `γ = α, β`. -/
theorem Submission.polyhedral_approx_pairing_covector_ext : ∀ (P n : ℕ) (α β : Covector (Eucl P) n), (∀ I : SimonMultiIndex n P, euclideanCovectorCoordinate α I = euclideanCovectorCoordinate β I) → α = β := by
  intro P n α β h
  -- Reduce to the underlying alternating maps on injective tuples of standard basis vectors.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  -- Sorting `v` by `σ = Tuple.sort v` gives the increasing multi-index `I = v ∘ σ`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  let I : SimonMultiIndex n P := OrderEmbedding.ofStrictMono _ hsm
  -- `e_v = e_I ∘ σ⁻¹`.
  have he : (fun i => EuclideanSpace.single (v i) (1 : ℝ)) =
      (fun j => EuclideanSpace.single (I j) (1 : ℝ)) ∘ ⇑(Tuple.sort v)⁻¹ := by
    funext i
    simp [I]
  -- `γ(e_v) = sign(σ⁻¹) • γ(e_I)` for `γ = α, β`, and `α(e_I) = β(e_I)`.
  rw [he, AlternatingMap.map_perm, AlternatingMap.map_perm]
  congr 1
  exact h I
/-- **Coordinate bound** (for the pairing expansion in the proof of Simon Ch. 6, 6.2, p. 169).
Each increasing coordinate `c_I = c(e_{I(1)}, …, e_{I(n)})` of an `n`-covector `c` is bounded in
absolute value by the Euclidean coefficient norm `|c|` of Remark 2.6.  Here `|c|² = ∑_J t_J`, with
`t_J = c(e_{J(1)}, …, e_{J(n)})²` for strictly increasing `J : Fin n → Fin P` and `t_J = 0`
otherwise.  Every `t_J ≥ 0` and `t_I = c_I²`, so `c_I² ≤ |c|²`. -/
theorem Submission.polyhedral_approx_pairing_coordinate_bound : ∀ (P n : ℕ) (c : Covector (Eucl P) n) (I : SimonMultiIndex n P), |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c := by
  intro P n c I
  -- `|c| = √(∑_J t_J)`, the sum over all `J : Fin n → Fin P`.
  set t : (Fin n → Fin P) → ℝ := fun J =>
    if StrictMono J then (c fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) ^ 2 else 0 with ht
  -- Each `t_J` is a square or `0`.
  have ht0 : ∀ J ∈ Finset.univ, 0 ≤ t J := fun J _ => by
    simp only [ht]
    split_ifs <;> positivity
  -- `⇑I` is strictly increasing and `basisFun (I i) = e_{I(i)}`, so `t_I = c_I²`.
  have htI : t I = euclideanCovectorCoordinate c I ^ 2 := by
    simp only [ht, I.strictMono, ite_true, EuclideanSpace.basisFun_apply, euclideanCovectorCoordinate]
  -- `|c_I| = √(c_I²) = √(t_I) ≤ √(∑_J t_J) = |c|`.
  calc |euclideanCovectorCoordinate c I| = √(euclideanCovectorCoordinate c I ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(∑ J, t J) := by
        rw [← htI]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum ht0 (Finset.mem_univ _))
    _ = covectorEuclideanNorm c := rfl

/-- **Pairing expansion** (Simon Ch. 6, 1.2 and 1.7, pp. 132–133; used for 6.2, p. 169).  For an
`n`-vector `w` and an `n`-covector `c` on `ℝ^P`, `w(c) = ∑_I c_I · w(dx^I)`, the sum over the
increasing multi-indices `I`, where `c_I = c(e_{I(1)}, …, e_{I(n)})` and
`dx^I = dx^{I(1)} ∧ ⋯ ∧ dx^{I(n)}`; moreover `|c_I| ≤ |c|`.  Since `dx^I(e_J) = δ_{IJ}` on
increasing multi-indices, `c` and `∑_I c_I dx^I` have the same increasing coordinates, hence are
equal (1.2), and `w` is linear. -/
theorem Submission.polyhedral_approx_pairing_expansion : ∀ (P n : ℕ) (w : NVector (Eucl P) n) (c : Covector (Eucl P) n), w c = ∑ I : SimonMultiIndex n P, euclideanCovectorCoordinate c I * w (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) ∧ ∀ I : SimonMultiIndex n P, |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c := by
  intro P n w c
  refine ⟨?_, Submission.polyhedral_approx_pairing_coordinate_bound P n c⟩
  -- `c = ∑_I c_I • dx^I`: both sides have the same increasing coordinates.
  have hc : c = ∑ I : SimonMultiIndex n P,
      euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) := by
    refine Submission.polyhedral_approx_pairing_covector_ext P n _ _ fun J => ?_
    -- The `J`-th coordinate of the sum is `∑_I c_I · dx^I(e_J)`.
    have hsum : euclideanCovectorCoordinate (∑ I : SimonMultiIndex n P,
          euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        ∑ I : SimonMultiIndex n P, euclideanCovectorCoordinate c I *
          euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J := by
      simp only [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    -- Only `I = J` contributes, since `dx^I(e_J) = δ_{IJ}`.
    rw [hsum, Finset.sum_eq_single J]
    · rw [(Submission.polyhedral_approx_pairing_wedge_kronecker P n J).1, mul_one]
    · intro I _ hIJ
      rw [(Submission.polyhedral_approx_pairing_wedge_kronecker P n I).2 J (Ne.symm hIJ), mul_zero]
    · intro hJ
      exact absurd (Finset.mem_univ J) hJ
  -- `w(∑_I c_I • dx^I) = ∑_I c_I · w(dx^I)` by linearity.
  calc w c = w (∑ I : SimonMultiIndex n P,
        euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) :=
        congrArg w hc
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- **Simon Ch. 6, (2.9) (p. 136).**  Restrictions `T ⌞ A` exist for every measure representation
`(μ, v)` of `T` and Borel `A`, and every restriction has locally finite mass.  For compact
`K ⊆ U`, testing `T` with `χ_K dx^I` (`χ_K` a smooth cut-off equal to `1` on `K`) shows that the
coordinates `v(·)(dx^I)` are `μ`-integrable on `K`; by `polyhedral_approx_pairing_expansion`,
`|⟨α, v(x)⟩| ≤ b ∑_I |v(x)(dx^I)|` whenever every coefficient satisfies `|α_I| ≤ b`.  Taking
`b = ‖α‖` gives the sequential continuity of `ω ↦ ∫_A ⟨ω, v⟩ dμ`; taking `b = 1` bounds `S(ω)` by
`∫_{closure W} ∑_I |v(·)(dx^I)| dμ` for every `ω` admissible for `M_W`. -/
theorem Submission.polyhedral_approx_restriction_exists : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U n, (∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → ∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U n, IsRestriction T A S) ∧ ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U n), IsRestriction T A S → ∀ W : Set (Eucl P), CompactlyContainedOpen W U → S.massOn W < ∞ := by
  intro P n U hU T
  -- `|α_I| = |α(e_{I 0}, …, e_{I (n-1)})| ≤ ‖α‖`.
  have coord_le : ∀ (α : Covector (Eucl P) n) (I : SimonMultiIndex n P),
      |euclideanCovectorCoordinate α I| ≤ ‖α‖ := by
    intro α I
    calc |euclideanCovectorCoordinate α I|
        = ‖α (fun j => EuclideanSpace.single (I j) (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖α‖ * ∏ j, ‖EuclideanSpace.single (I j) (1 : ℝ)‖ := α.le_opNorm _
      _ = ‖α‖ := by simp
  -- For a representation `(μ, v)` and a compact `K ⊆ U`, the coordinates `v(·)(dx^I)` are
  -- `μ`-integrable on `K`, and `G = ∑_I |v(·)(dx^I)|` dominates the pairing.
  have key : ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
      IsMeasureRepresentation T μ v → ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      ∃ G : Eucl P → ℝ, (∀ x, 0 ≤ G x) ∧ IntegrableOn G K μ ∧
        ∀ (x : Eucl P) (α : Covector (Eucl P) n) (b : ℝ),
          (∀ I : SimonMultiIndex n P, |euclideanCovectorCoordinate α I| ≤ b) →
            |v x α| ≤ b * G x := by
    intro μ v hrep K hK hKU
    -- A smooth cut-off `χ`, equal to `1` on `K`, with `tsupport χ ⊆ cthickening r K ⊆ U`.
    obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
    obtain ⟨χ, hχ, -, hχs, hχK⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := r) (E := K)) hK.isClosed (self_subset_thickening hr K)
    have hχt : tsupport χ ⊆ cthickening r K := by
      rw [tsupport, hχs]
      exact closure_thickening_subset_cthickening r K
    have hcoord : ∀ I : SimonMultiIndex n P, IntegrableOn
        (fun x => v x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j)))) K μ := by
      intro I
      have hmem : (fun x => χ x • wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) :
          DifferentialForm (Eucl P) n) ∈ testFormOnSubmodule (E := Eucl P) U n :=
        ⟨⟨hχ.smul contDiff_const, hK.cthickening.of_isClosed_subset (isClosed_tsupport _)
            ((tsupport_smul_subset_left _ _).trans hχt)⟩,
          (tsupport_smul_subset_left _ _).trans (hχt.trans hrU)⟩
      refine (hrep ⟨_, hmem⟩).1.integrableOn.congr_fun (fun x hx => ?_)
        hK.isClosed.measurableSet
      show v x (χ x • _) = v x _
      rw [(hχK x).1 hx, one_smul]
    refine ⟨fun x => ∑ I : SimonMultiIndex n P,
        |v x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j)))|,
      fun x => Finset.sum_nonneg fun I _ => abs_nonneg _,
      integrable_finsetSum _ fun I _ => (hcoord I).abs, ?_⟩
    intro x α b hb
    beta_reduce
    rw [(Submission.polyhedral_approx_pairing_expansion P n (v x) α).1, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb I) (abs_nonneg _)
  refine ⟨fun μ v hrep A hA => ?_, fun A S hS W hW => ?_⟩
  · -- (a) `S(ω) = ∫_A ⟨ω, v⟩ dμ` is linear and sequentially continuous.
    let L : TestFormOn U n →ₗ[ℝ] ℝ :=
      { toFun := fun ω => ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ
        map_add' := fun ω η => by
          simp only [Submodule.coe_add, Pi.add_apply, map_add]
          exact integral_add (hrep ω).1.integrableOn (hrep η).1.integrableOn
        map_smul' := fun c ω => by
          simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
          exact integral_const_mul c _ }
    refine ⟨⟨L, fun ωs hconv => ?_⟩, hA, μ, v, hrep, fun ω => rfl⟩
    obtain ⟨K, hK, hKU, hsupp, -, hder⟩ := hconv
    obtain ⟨G, hG0, hGint, hGb⟩ := key μ v hrep K hK hKU
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hC0 : 0 ≤ ∫ x in K, G x ∂μ := setIntegral_nonneg hKm fun x _ => hG0 x
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ : 0 < ε / ((∫ x in K, G x ∂μ) + 1) := div_pos hε (by linarith)
    -- Eventually `‖ω_j(x)‖ < δ` on `K`, and `ω_j = 0` off `K`.
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hder 0) _ hδ] with j hj
    have hbound : ∀ x, ‖v x ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
        ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x := by
      intro x
      by_cases hx : x ∈ K
      · have hjx := hj x hx
        rw [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
          norm_iteratedFDeriv_zero] at hjx
        rw [indicator_of_mem hx, Real.norm_eq_abs]
        exact (hGb x _ _ fun I => coord_le _ I).trans
          (mul_le_mul_of_nonneg_right hjx.le (hG0 x))
      · have h0 : (ωs j : DifferentialForm (Eucl P) n) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h)
        rw [h0, map_zero, norm_zero, indicator_of_notMem hx, mul_zero]
    have hint : Integrable (fun x => ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x) μ :=
      (IntegrableOn.integrable_indicator hGint hKm).const_mul _
    rw [dist_zero_right]
    calc ‖∫ x in A, v x ((ωs j : DifferentialForm (Eucl P) n) x) ∂μ‖
        ≤ ∫ x in A, ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x ∂μ :=
          norm_integral_le_of_norm_le hint.integrableOn (ae_of_all _ hbound)
      _ ≤ ∫ x, ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x ∂μ :=
          integral_mono_measure Measure.restrict_le_self
            (ae_of_all _ fun x => mul_nonneg hδ.le (indicator_nonneg (fun y _ => hG0 y) x)) hint
      _ = ε / ((∫ x in K, G x ∂μ) + 1) * ∫ x in K, G x ∂μ := by
          rw [integral_const_mul, integral_indicator hKm]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  · -- (b) For `ω` admissible for `M_W`, `S(ω) ≤ ∫_{closure W} G dμ`.
    obtain ⟨-, μ, v, hrep, hSω⟩ := hS
    obtain ⟨-, hWc, hWU⟩ := hW
    obtain ⟨G, hG0, hGint, hGb⟩ := key μ v hrep (closure W) hWc hWU
    have hKm : MeasurableSet (closure W) := isClosed_closure.measurableSet
    have hint : Integrable ((closure W).indicator G) μ :=
      IntegrableOn.integrable_indicator hGint hKm
    refine lt_of_le_of_lt (sSup_le ?_) (ENNReal.ofReal_lt_top (r := ∫ x in closure W, G x ∂μ))
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have hbound : ∀ x, ‖v x ((ω : DifferentialForm (Eucl P) n) x)‖ ≤
        (closure W).indicator G x := by
      intro x
      by_cases hx : x ∈ closure W
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        have h := hGb x ((ω : DifferentialForm (Eucl P) n) x) 1
          fun I => ((Submission.polyhedral_approx_pairing_expansion P n (v x) _).2 I).trans (hω1 x)
        rwa [one_mul] at h
      · have h0 : (ω : DifferentialForm (Eucl P) n) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hωW h))
        rw [h0, map_zero, norm_zero, indicator_of_notMem hx]
    rw [hSω ω]
    calc ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ
        ≤ ‖∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ‖ := Real.le_norm_self _
      _ ≤ ∫ x in A, (closure W).indicator G x ∂μ :=
          norm_integral_le_of_norm_le hint.integrableOn (ae_of_all _ hbound)
      _ ≤ ∫ x, (closure W).indicator G x ∂μ :=
          integral_mono_measure Measure.restrict_le_self
            (ae_of_all _ (indicator_nonneg fun y _ => hG0 y)) hint
      _ = ∫ x in closure W, G x ∂μ := integral_indicator hKm

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
