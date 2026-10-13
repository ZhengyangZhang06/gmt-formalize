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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
