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

/-- Whitney's `C¹` extension theorem (Simon Ch. 2, Theorem 1.6), with derivatives as continuous
linear maps: if `A ⊆ ℝⁿ` is closed and `f`, `τ` are continuous on `A` with the compact-uniform
Taylor condition, then some `C¹` function `h` agrees with `f` on `A` and has derivative `τ a` at
every `a ∈ A`.  Standard construction (Evans–Gariepy §6.5): Whitney radius
`r = min(1, dist(·, A)) / 100`, a Vitali family of disjoint balls `B(c, r c)` whose fourfold
enlargements cover `ℝⁿ ∖ A`, uniformly bounded overlap, rescaled bumps normalized to a partition
of unity `w_c` with `∑ ‖Dw_c(x)‖ ≤ M / r x`, and `h = ∑ w_c P_{q c}` off `A`, where
`P_b(y) = f b + τ b (y - b)` and `q c ∈ A` is a nearest point.  The steps follow the pinned
SimonGMT proof `Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney` (whose
module is not imported here), inlined. -/
theorem Submission.lpf_c1r_whitney_extension :
    ∀ (n : ℕ) (A : Set (Eucl n)) (f : Eucl n → ℝ) (τ : Eucl n → (Eucl n →L[ℝ] ℝ)),
      IsClosed A → ContinuousOn f A → ContinuousOn τ A →
      (∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧
        ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - τ x (y - x)‖ ≤ δ * ‖y - x‖) →
      ∃ h : Eucl n → ℝ, ContDiff ℝ 1 h ∧ ∀ a ∈ A, h a = f a ∧ HasFDerivAt h (τ a) a := by
  intro n A f τ hA _hf hτ hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, fun a ha => absurd ha (notMem_empty a)⟩
  -- Step 1: local uniform Taylor estimate near each point of `A`.
  have hloc : ∀ a ∈ A, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖τ b - τ a‖ ≤ ε) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖f c - f b - τ b (c - b)‖ ≤ ε * ‖c - b‖ := by
    intro a ha ε hε
    obtain ⟨ρ, hρ, hρrem⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left ε hε
    obtain ⟨η, hη, hD⟩ := Metric.continuousWithinAt_iff.mp (hτ a ha) ε hε
    have hδ1 : min 1 (min η (ρ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η (ρ / 3)) ≤ η := (min_le_right _ _).trans (min_le_left _ _)
    have hδρ : min 1 (min η (ρ / 3)) ≤ ρ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η (ρ / 3)), lt_min one_pos (lt_min hη (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      have h1 := hD hb (hba.trans_le hδη)
      rw [dist_eq_norm] at h1
      exact h1.le
    · intro b hb hba c hc hca
      refine hρrem b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc ?_
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- Affine jets `P b y = f b + τ b (y - b)`.
  obtain ⟨P, hPdef⟩ : ∃ P : Eucl n → Eucl n → ℝ, ∀ b y, P b y = f b + τ b (y - b) :=
    ⟨fun b y => f b + τ b (y - b), fun _ _ => rfl⟩
  have P_sub : ∀ a b y, ‖P b y - P a y‖ ≤
      ‖f b - f a - τ a (b - a)‖ + ‖τ b - τ a‖ * ‖y - b‖ := by
    intro a b y
    have hid : P b y - P a y = (f b - f a - τ a (b - a)) + (τ b - τ a) (y - b) := by
      have hy : y - a = (y - b) + (b - a) := by abel
      simp only [hPdef, hy, map_add, sub_apply]
      ring
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((τ b - τ a).le_opNorm (y - b)))
  have P_deriv : ∀ b y, HasFDerivAt (P b) (τ b) y := by
    intro b y
    have e : P b = fun y => f b + (τ b y - τ b b) := by
      funext y
      rw [hPdef, map_sub]
    rw [e]
    exact ((τ b).hasFDerivAt.sub_const (τ b b)).const_add (f b)
  have P_cd : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    have e : P b = fun y => f b + τ b (y - b) := funext (hPdef b)
    rw [e]
    exact contDiff_const.add ((τ b).contDiff.comp (contDiff_id.sub contDiff_const))
  -- Step 2: the Whitney radius `r x = min 1 (dist x A) / 100`.
  obtain ⟨r, hr⟩ : ∃ r : Eucl n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨fun x => min 1 (infDist x A) / 100, fun _ => rfl⟩
  have r_nonneg : ∀ x, 0 ≤ r x := by
    intro x
    rw [hr]
    exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have r_le : ∀ x, r x ≤ 1 / 100 := by
    intro x
    rw [hr]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have r_le_inf : ∀ x, 100 * r x ≤ infDist x A := by
    intro x
    rw [hr]
    linarith [min_le_right (1 : ℝ) (infDist x A)]
  have r_pos : ∀ x, x ∉ A → 0 < r x := by
    intro x hx
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have r_le_add : ∀ x y, r x ≤ r y + dist x y / 100 := by
    intro x y
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [hr, hr]
    linarith
  have r_near : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := r_le_add x c
    have h₂ := r_le_add c x
    rw [dist_comm c x] at h₂
    have hx := r_nonneg x
    have hc := r_nonneg c
    exact ⟨by linarith, by linarith, by linarith⟩
  have r_scale : ∀ x, infDist x A ≤ 1 → infDist x A = 100 * r x := by
    intro x hx
    rw [hr, min_eq_right hx]
    ring
  have notMem_of_near : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA
    have hi := infDist_le_dist_of_mem (x := x) hyA
    rw [dist_comm x y] at hi
    linarith [r_le_inf x, r_nonneg x]
  -- Step 3: Vitali selection of disjoint Whitney balls covering `Aᶜ` fourfold.
  obtain ⟨Z, hZA, hZd, hZc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    Aᶜ (fun x : Eucl n => x) r (1 / 100) (fun x _ => r_le x) 4 (by norm_num)
  have Z_cov : ∀ x, x ∉ A → ∃ c ∈ Z, dist x c < 4 * r c := by
    intro x hx
    obtain ⟨c, hcZ, hxc⟩ := hZc x hx
    exact ⟨c, hcZ, hxc (mem_ball_self (r_pos x hx))⟩
  have Z_sep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      rw [mem_ball, dist_comm]
      exact lt_of_not_ge hlt
    have hdd : d ∈ ball d (r d) := mem_ball_self (r_pos d (hZA hd))
    exact Set.disjoint_left.mp (hZd hc hd hcd) hdc hdd
  -- Step 4: bounded overlap, via a uniform packing bound in `closedBall 0 21`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Eucl n), s ⊆ closedBall 0 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Eucl n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hsep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Eucl n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Function.Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Eucl n) ≠ (y : Eucl n) := fun h => hxy' (Subtype.ext h)
      have hd := hsep x.property y.property hne'
      have htri := dist_triangle (x : Eucl n) (c x : Eucl n) (y : Eucl n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Eucl n) (c x : Eucl n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  have hover : ∀ x, x ∉ A →
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
        {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := r_pos x hx
    let sc : Eucl n → Eucl n := fun c => (r x)⁻¹ • (c - x)
    have hsc : Function.Injective sc := by
      intro c d hcd
      have h := congrArg (fun z : Eucl n => r x • z) hcd
      simpa [sc, smul_smul, hrx.ne'] using h
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖sc c‖ ≤ 21 := by
      intro c hc
      have hd := (r_near x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      dsimp [sc]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep : (sc '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun h => hcd (congrArg sc h)
      have hdist := Z_sep c hc.1 d hd.1 hcd'
      have hrad := (r_near x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        rw [← dist_eq_norm]
        exact hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      dsimp [sc]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : sc '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Eucl n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      exact hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep
    exact ⟨hfin.of_finite_image hsc.injOn, by rwa [Set.ncard_image_of_injective _ hsc] at hcard⟩
  -- The finite sets `S x` of centres near `x`.
  have hSex : ∀ x : Eucl n, ∃ s : Finset Z, x ∉ A →
      (∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun h => absurd hx h⟩
    · obtain ⟨hT, hTN⟩ := hover x hx
      have hU : {c : Z | dist x c ≤ r x + 10 * r c}.Finite :=
        (hT.preimage Subtype.val_injective.injOn).subset (fun c hc => ⟨c.2, hc⟩)
      refine ⟨hU.toFinset, fun _ => ⟨fun c => by simp, ?_⟩⟩
      rw [← Set.ncard_eq_toFinset_card _ hU,
        ← Set.ncard_image_of_injective _ Subtype.val_injective]
      refine le_trans (Set.ncard_le_ncard ?_ hT) hTN
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
  choose S hS using hSex
  -- Step 5: rescaled bumps `bp c y = b0 ((y - c) / r c)`, with `b0 = 1` on `B̄(0, 4)` and
  -- `b0 = 0` off `B(0, 8)`.
  obtain ⟨b0, hb0in, hb0out⟩ : ∃ b0 : ContDiffBump (0 : Eucl n), b0.rIn = 4 ∧ b0.rOut = 8 :=
    ⟨⟨4, 8, by norm_num, by norm_num⟩, rfl, rfl⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b0.hasCompactSupport
    (b0.contDiff (n := 1)) (by simp)
  obtain ⟨bp, hbp⟩ : ∃ bp : Z → Eucl n → ℝ, ∀ c y, bp c y = b0 ((r c)⁻¹ • (y - c)) :=
    ⟨fun c y => b0 ((r c)⁻¹ • (y - c)), fun _ _ => rfl⟩
  have bp_cd : ∀ c, ContDiff ℝ 1 (bp c) := by
    intro c
    have e : bp c = fun y => b0 ((r c)⁻¹ • (y - c)) := funext (hbp c)
    rw [e]
    exact (b0.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).const_smul _)
  have bp_nonneg : ∀ c y, 0 ≤ bp c y := by
    intro c y
    rw [hbp]
    exact b0.nonneg
  have bp_le_one : ∀ c y, bp c y ≤ 1 := by
    intro c y
    rw [hbp]
    exact b0.le_one
  have bp_one : ∀ (c : Z) (y : Eucl n), dist y c ≤ 4 * r c → bp c y = 1 := by
    intro c y hy
    have hc : 0 < r c := r_pos c (hZA c.2)
    rw [hbp]
    apply b0.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le),
      hb0in]
    rw [dist_eq_norm] at hy
    calc (r c)⁻¹ * ‖y - c‖ ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have bp_zero : ∀ (c : Z) (y : Eucl n), 8 * r c ≤ dist y c → bp c y = 0 := by
    intro c y hy
    have hc : 0 < r c := r_pos c (hZA c.2)
    rw [hbp]
    apply Function.notMem_support.mp
    rw [b0.support_eq, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hc.le), hb0out, not_lt]
    rw [dist_eq_norm] at hy
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * ‖y - c‖ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, bp_der⟩ : ∃ B : ℝ, 0 < B ∧
      ∀ (c : Z) (y : Eucl n), ‖fderiv ℝ (bp c) y‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c y => ?_⟩
    have hc : 0 < r c := r_pos c (hZA c.2)
    let ρ : ℝ≥0 := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Eucl n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (bp c) := by
      have e : bp c = b0 ∘ (fun y : Eucl n => (r c)⁻¹ • (y - c)) := funext (hbp c)
      rw [e]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := y)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (bp c) y‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- Step 6: the partition of unity `w c = bp c / sm`, `sm = ∑ᶠ c, bp c`, on `Aᶜ`.
  have bp_far : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c : Z, c ∉ S x → bp c y = 0 := by
    intro x hx y hy c hc
    apply bp_zero c y
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun h => hc (((hS x hx).1 c).mpr h)
    have ht := dist_triangle x y (c : Eucl n)
    rw [dist_comm x y] at ht
    have := r_nonneg c
    linarith
  obtain ⟨sm, hsm⟩ : ∃ sm : Eucl n → ℝ, ∀ y, sm y = ∑ᶠ c : Z, bp c y :=
    ⟨fun y => ∑ᶠ c : Z, bp c y, fun _ => rfl⟩
  have sm_eq : ∀ x, x ∉ A → ∀ y, dist y x < r x → sm y = ∑ c ∈ S x, bp c y := by
    intro x hx y hy
    rw [hsm]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra h
    exact hc (bp_far x hx y hy c h)
  have sm_ge : ∀ x, x ∉ A → 1 ≤ sm x := by
    intro x hx
    have hrx := r_pos x hx
    rw [sm_eq x hx x (by rw [dist_self]; exact hrx)]
    obtain ⟨c, hcZ, hxc⟩ := Z_cov x hx
    have hi : (⟨c, hcZ⟩ : Z) ∈ S x := by
      rw [(hS x hx).1]
      have := r_nonneg c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = bp ⟨c, hcZ⟩ x := (bp_one ⟨c, hcZ⟩ x hxc.le).symm
      _ ≤ ∑ c ∈ S x, bp c x :=
          Finset.single_le_sum (f := fun c : Z => bp c x) (fun c _ => bp_nonneg c x) hi
  have sm_cd : ∀ x, x ∉ A → ContDiffAt ℝ 1 sm x := by
    intro x hx
    have hs : ContDiff ℝ 1 (fun y => ∑ c ∈ S x, bp c y) := ContDiff.sum (fun c _ => bp_cd c)
    apply hs.contDiffAt.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
    exact sm_eq x hx y hy
  have sm_fderiv : ∀ x, x ∉ A → fderiv ℝ sm x = ∑ c ∈ S x, fderiv ℝ (bp c) x := by
    intro x hx
    have heq : sm =ᶠ[𝓝 x] (fun y => ∑ c ∈ S x, bp c y) := by
      filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
      exact sm_eq x hx y hy
    rw [heq.fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (bp_cd c).differentiable one_ne_zero x)
  obtain ⟨w, hw⟩ : ∃ w : Z → Eucl n → ℝ, ∀ c y, w c y = bp c y / sm y :=
    ⟨fun c y => bp c y / sm y, fun _ _ => rfl⟩
  have w_cd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    have e : w c = bp c / sm := funext (hw c)
    rw [e]
    exact (bp_cd c).contDiffAt.div (sm_cd x hx) (ne_of_gt (lt_of_lt_of_le one_pos (sm_ge x hx)))
  have w_nonneg : ∀ c x, x ∉ A → 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (bp_nonneg c x) (zero_le_one.trans (sm_ge x hx))
  have w_zero : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c : Z, c ∉ S x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, bp_far x hx y hy c hc, zero_div]
  have w_sum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ S x, w c y = 1 := by
    intro x hx y hy
    have hyA := notMem_of_near x hx y hy
    simp only [hw, ← Finset.sum_div, ← sm_eq x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (sm_ge y hyA)))
  have w_dsum : ∀ x, x ∉ A → ∑ c ∈ S x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ S x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
      exact w_sum x hx y hy
    have hh := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh
    rw [fderiv_fun_sum (fun c _ => (w_cd c x hx).differentiableAt one_ne_zero)] at hh
    exact hh
  -- Step 7: `‖D w_c‖ ≤ ‖D bp_c‖ + ‖D sm‖` and the summed bound `M / r x`.
  have w_der : ∀ c x, x ∉ A →
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (bp c) x‖ + ‖fderiv ℝ sm x‖ := by
    intro c x hx
    have hS1 : 1 ≤ sm x := sm_ge x hx
    have hSpos : 0 < sm x := lt_of_lt_of_le one_pos hS1
    have hSi : (sm x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1
    have hSi2 : (sm x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ sm x ^ 2 by nlinarith)
    have hb := ((bp_cd c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((sm_cd x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x) + (sm x)⁻¹ • fderiv ℝ (bp c) x := by
      have e : w c = fun y => bp c y * ((fun t : ℝ => t⁻¹) ∘ sm) y := by
        funext y
        rw [hw, div_eq_mul_inv]
        rfl
      rw [e]
      exact hprod.fderiv
    rw [hder]
    have hb0 := bp_nonneg c x
    have hb1 := bp_le_one c x
    calc ‖bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x) + (sm x)⁻¹ • fderiv ℝ (bp c) x‖
        ≤ ‖bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x)‖ + ‖(sm x)⁻¹ • fderiv ℝ (bp c) x‖ :=
          norm_add_le _ _
      _ = bp c x * ((sm x ^ 2)⁻¹ * ‖fderiv ℝ sm x‖) + (sm x)⁻¹ * ‖fderiv ℝ (bp c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (sm x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (bp c) x‖ + ‖fderiv ℝ sm x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (bp c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ sm x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (sm x))) (norm_nonneg (fderiv ℝ sm x)))
          linarith
  obtain ⟨M, hM, w_dbound⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x, x ∉ A →
      ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := r_pos x hx
    have hT : 0 ≤ 2 * B / r x := by positivity
    have hb' : ∀ c ∈ S x, ‖fderiv ℝ (bp c) x‖ ≤ 2 * B / r x := by
      intro c hc
      have hlow := (r_near x c (((hS x hx).1 c).mp hc)).1
      refine (bp_der c x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = 2 * B / r x := by ring
    have hcard : ((S x).card : ℝ) ≤ N := by exact_mod_cast (hS x hx).2
    have hsum : ‖fderiv ℝ sm x‖ ≤ (N : ℝ) * (2 * B / r x) := by
      rw [sm_fderiv x hx]
      calc ‖∑ c ∈ S x, fderiv ℝ (bp c) x‖ ≤ ∑ c ∈ S x, ‖fderiv ℝ (bp c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ S x, 2 * B / r x := Finset.sum_le_sum hb'
        _ = ((S x).card : ℝ) * (2 * B / r x) := by simp
        _ ≤ (N : ℝ) * (2 * B / r x) := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ S x, ‖fderiv ℝ (w c) x‖ ≤ 2 * B / r x + (N : ℝ) * (2 * B / r x) :=
      fun c hc => (w_der c x hx).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖
        ≤ ∑ _c ∈ S x, (2 * B / r x + (N : ℝ) * (2 * B / r x)) := Finset.sum_le_sum hw'
      _ = ((S x).card : ℝ) * (2 * B / r x + (N : ℝ) * (2 * B / r x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * B / r x + (N : ℝ) * (2 * B / r x)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * (2 * B / r x) := by
          nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by ring
  -- Step 8: nearest-point anchors.
  choose q hqA hqd using fun x => hA.exists_infDist_eq_dist hne x
  have q_le : ∀ x a, a ∈ A → dist x (q x) ≤ dist x a := by
    intro x a ha
    rw [← hqd]
    exact infDist_le_dist_of_mem ha
  have q_pt : ∀ x a, a ∈ A → dist (q x) a ≤ 2 * dist x a := by
    intro x a ha
    have h1 := dist_triangle (q x) x a
    rw [dist_comm (q x) x] at h1
    linarith [q_le x a ha]
  have anchor1 : ∀ x, x ∉ A → ∀ c ∈ S x, dist x (q c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hc' := ((hS x hx).1 c).mp hc
    have hd := (r_near x c hc').2.2
    have hr' := r_le_inf x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Eucl n)) (y := x)
    have ht := dist_triangle x (c : Eucl n) (q c)
    rw [dist_comm (c : Eucl n) x] at hi
    rw [← hqd (c : Eucl n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have anchor2 : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ S x, dist (q c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := anchor1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (q c) x a
    rw [dist_comm (q c) x] at ht
    linarith
  -- Convex combinations of vectors of norm `≤ b` have norm `≤ b`.
  have convex_le : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Finset Z)
      (u : Z → ℝ) (v : Z → F) (b : ℝ), (∀ i ∈ s, 0 ≤ u i) → ∑ i ∈ s, u i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, u i • v i‖ ≤ b := by
    intro F _ _ s u v b hu hs hv
    calc ‖∑ i ∈ s, u i • v i‖ ≤ ∑ i ∈ s, ‖u i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, u i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (hu i hi)]
      _ ≤ ∑ i ∈ s, u i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (hu i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- Step 9: the extension.
  obtain ⟨g, hg⟩ : ∃ g : Eucl n → ℝ,
      ∀ y, g y = if y ∈ A then f y else ∑ᶠ c : Z, w c y * P (q c) y :=
    ⟨fun y => if y ∈ A then f y else ∑ᶠ c : Z, w c y * P (q c) y, fun _ => rfl⟩
  have g_on : ∀ a ∈ A, g a = f a := by
    intro a ha
    rw [hg, ite_eq_left ha]
  have g_near : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ S x, w c y * P (q c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (notMem_of_near x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (q c) y = 0
    rw [w_zero x hx y hy c hc', zero_mul]
  have g_ev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] (fun y => ∑ c ∈ S x, w c y * P (q c) y) := by
    intro x hx
    filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
    exact g_near x hx y hy
  have g_cd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ S x, w c y * P (q c) y) x :=
      ContDiffAt.sum (fun c _ => (w_cd c x hx).mul (P_cd _).contDiffAt)
    exact hs.congr_of_eventuallyEq (g_ev x hx)
  have g_fderiv : ∀ x, x ∉ A → fderiv ℝ g x =
      ∑ c ∈ S x, (w c x • τ (q c) + P (q c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(g_ev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((w_cd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (P_deriv _ x)
  have g_sub : ∀ a x, x ∉ A → g x - P a x = ∑ c ∈ S x, w c x * (P (q c) x - P a x) := by
    intro a x hx
    have hx' : dist x x < r x := by
      rw [dist_self]
      exact r_pos x hx
    rw [g_near x hx x hx']
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, w_sum x hx x hx', one_mul]
  -- Step 10: `g` has derivative `τ a` at every `a ∈ A`.
  have g_deriv : ∀ a ∈ A, HasFDerivAt g (τ a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, _hδ1, hD, hR⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by
      rw [dist_self]
      exact hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [g_on a ha]
    by_cases hxA : x ∈ A
    · rw [g_on x hxA]
      have hr' := hR a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hid : g x - f a - τ a (x - a) = g x - P a x := by
        rw [hPdef a x]
        ring
      rw [hid, g_sub a x hxA]
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact r_pos x hxA
      have key := convex_le ℝ (S x) (fun c => w c x) (fun c => P (q c) x - P a x) (ε * ‖x - a‖)
        (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') ?_
      · simpa only [smul_eq_mul] using key
      intro c hc
      have hbA : q c ∈ A := hqA c
      have hba : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
      have hxb : dist x (q c) ≤ 2 * dist x a :=
        (anchor1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (q c) a < δ := by linarith
      have hDb := hD (q c) hbA hbaδ
      have hr' := hR a ha haa (q c) hbA hbaδ
      have hba' : ‖q c - a‖ ≤ 3 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hba
      have hxb' : ‖x - q c‖ ≤ 2 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hxb
      calc ‖P (q c) x - P a x‖
          ≤ ‖f (q c) - f a - τ a (q c - a)‖ + ‖τ (q c) - τ a‖ * ‖x - q c‖ := P_sub a (q c) x
        _ ≤ (ε / 5) * ‖q c - a‖ + (ε / 5) * ‖x - q c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  have g_fderiv_on : ∀ a ∈ A, fderiv ℝ g a = τ a := fun a ha => (g_deriv a ha).fderiv
  -- Step 11: `Dg` is continuous at every `a ∈ A`.
  have g_cont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    have hK : (0 : ℝ) < 1 + 700 * M := by positivity
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by
      rw [hηdef]
      field_simp
    have hηε : η ≤ ε / 2 := by nlinarith
    obtain ⟨δ, hδ, hδ1, hD, hR⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [g_fderiv_on a ha, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [g_fderiv_on x hxA]
      exact (hD x hxA (by linarith)).trans hηε
    · have hrx := r_pos x hxA
      have hbA : q x ∈ A := hqA x
      have hba : dist (q x) a ≤ 2 * dist x a := q_pt x a ha
      have hbaδ : dist (q x) a < δ := by linarith
      have hDb := hD (q x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := r_scale x hdx
      have hD' : ∀ c ∈ S x, ‖τ (q c) - τ a‖ ≤ η := by
        intro c hc
        apply hD _ (hqA c)
        have hi := anchor2 x hxA a ha c hc
        linarith
      have hP' : ∀ c ∈ S x, ‖P (q c) x - P (q x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA : q c ∈ A := hqA c
        have hda : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
        have hdaδ : dist (q c) a < δ := by linarith
        have hxd : dist x (q c) ≤ 2 * infDist x A := anchor1 x hxA c hc
        have hxb : dist x (q x) = infDist x A := (hqd x).symm
        have hdb : dist (q c) (q x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (q c) x (q x)
          rw [dist_comm (q c) x, hxb] at ht
          linarith
        have hDd : ‖τ (q c) - τ (q x)‖ ≤ 2 * η := by
          calc ‖τ (q c) - τ (q x)‖ = ‖(τ (q c) - τ a) - (τ (q x) - τ a)‖ := by
                congr 1
                abel
            _ ≤ ‖τ (q c) - τ a‖ + ‖τ (q x) - τ a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hR (q x) hbA hbaδ (q c) hdA hdaδ
        have hdb' : ‖q c - q x‖ ≤ 3 * infDist x A := by
          rw [← dist_eq_norm]
          exact hdb
        have hxd' : ‖x - q c‖ ≤ 2 * infDist x A := by
          rw [← dist_eq_norm]
          exact hxd
        calc ‖P (q c) x - P (q x) x‖
            ≤ ‖f (q c) - f (q x) - τ (q x) (q c - q x)‖ + ‖τ (q c) - τ (q x)‖ * ‖x - q c‖ :=
              P_sub (q x) (q c) x
          _ ≤ η * ‖q c - q x‖ + (2 * η) * ‖x - q c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by
              rw [hscale]
              ring
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact hrx
      have hdecomp : fderiv ℝ g x - τ a =
          (∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x := by
        rw [g_fderiv x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, w_sum x hxA x hx', w_dsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hdecomp]
      calc ‖(∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ S x, w c x • (τ (q c) - τ a)‖ +
            ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact convex_le _ (S x) (fun c => w c x) (fun c => τ (q c) - τ a) η
                (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') hD'
            · calc ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ S x, ‖(P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_sum_le _ _
                _ ≤ ∑ c ∈ S x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (w_dbound x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by
            field_simp
        _ = ε / 2 := heq
  -- Step 12: conclusion.
  refine ⟨g, ?_, fun a ha => ⟨g_on a ha, g_deriv a ha⟩⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (g_deriv x hx).differentiableAt
    · exact (g_cd x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact g_cont x hx
    · exact (g_cd x hx).continuousAt_fderiv one_ne_zero

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
