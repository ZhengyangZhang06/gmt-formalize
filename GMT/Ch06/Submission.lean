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

/-- The straight-line homotopy `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`, `t(y) = y₀`,
`tl(y) = (y₁, …, yₘ)`, is built from the continuous linear maps `t`, `tl` and the smooth `F₀`, `F₁`,
hence smooth.  By the chain and product rules
`DG(y)(w) = DF₀(tl y)(tl w) + t(y) • (DF₁(tl y)(tl w) - DF₀(tl y)(tl w)) + t(w) • (F₁ - F₀)(tl y)`,
so at `y = (s, x)` the derivative maps `e₀ ↦ F₁(x) - F₀(x)` and `ι(v) = (0, v) ↦
DF₀(x)(v) + s • (DF₁(x)(v) - DF₀(x)(v)) = (1 - s) • DF₀(x)(v) + s • DF₁(x)(v)`. -/
theorem Submission.dph_sh_ae_affine_homotopy_contDiff_fderiv :
    ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ∧ ∀ (s : ℝ) (x : Eucl m), fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (EuclideanSpace.single 0 1) = F₁ x - F₀ x ∧ ∀ v : Eucl m, fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v))) = (1 - s) • fderiv ℝ F₀ x v + s • fderiv ℝ F₁ x v := by
  intro m m' F₀ F₁ hF₀ hF₁
  -- `t(y) = y₀` and `tl(y) = (y₁, …, yₘ)` are continuous linear maps, and
  -- `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`.
  let tL : Eucl (m + 1) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj 0 ∘L (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  let tlL : Eucl (m + 1) →L[ℝ] Eucl m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j : Fin m => ContinuousLinearMap.proj j.succ) ∘L
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  have hG : (fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) =
      fun y => F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)) := rfl
  -- Values: `t(cons(τ, z)) = τ`, `tl(cons(τ, z)) = z`, `t(e₀) = 1` and `tl(e₀) = 0`.
  have htL : ∀ (τ : ℝ) (z : Eucl m), tL ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons τ (EuclideanSpace.equiv (Fin m) ℝ z))) = τ := fun τ z => rfl
  have htlL : ∀ (τ : ℝ) (z : Eucl m), tlL ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons τ (EuclideanSpace.equiv (Fin m) ℝ z))) = z := fun τ z => rfl
  have htL₀ : tL (EuclideanSpace.single 0 1) = 1 := by simp [tL]
  have htlL₀ : tlL (EuclideanSpace.single 0 1) = 0 := by
    ext j
    simp [tlL, Fin.succ_ne_zero]
  clear_value tL tlL
  -- Chain and product rules: `DG(y) = DF₀(tl y) ∘ tl + t(y) • (DF₁(tl y) ∘ tl - DF₀(tl y) ∘ tl)
  -- + t.smulRight ((F₁ - F₀)(tl y))`.
  have hD : ∀ y : Eucl (m + 1), HasFDerivAt (fun y => F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)))
      ((fderiv ℝ F₀ (tlL y)).comp tlL + (tL y • ((fderiv ℝ F₁ (tlL y)).comp tlL -
        (fderiv ℝ F₀ (tlL y)).comp tlL) + tL.smulRight (F₁ (tlL y) - F₀ (tlL y)))) y := by
    intro y
    have h₀ : HasFDerivAt (fun y => F₀ (tlL y)) ((fderiv ℝ F₀ (tlL y)).comp tlL) y :=
      ((hF₀.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y tlL.hasFDerivAt
    have h₁ : HasFDerivAt (fun y => F₁ (tlL y)) ((fderiv ℝ F₁ (tlL y)).comp tlL) y :=
      ((hF₁.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y tlL.hasFDerivAt
    exact h₀.add (tL.hasFDerivAt.smul (h₁.sub h₀))
  refine ⟨?_, fun s x => ⟨?_, fun v => ?_⟩⟩
  · rw [hG]
    exact (hF₀.comp tlL.contDiff).add
      (tL.contDiff.smul ((hF₁.comp tlL.contDiff).sub (hF₀.comp tlL.contDiff)))
  · -- `DG(cons(s, x)) e₀ = DF₀(x) 0 + s • (DF₁(x) 0 - DF₀(x) 0) + 1 • (F₁(x) - F₀(x))`.
    rw [hG, (hD _).fderiv, htlL, htL, add_apply, add_apply, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, htL₀, htlL₀, map_zero, map_zero, sub_zero, smul_zero,
      one_smul, zero_add, zero_add]
  · -- `DG(cons(s, x)) (ι v) = DF₀(x) v + s • (DF₁(x) v - DF₀(x) v) + 0 • (F₁(x) - F₀(x))`.
    rw [hG, (hD _).fderiv, htlL, htL, add_apply, add_apply, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, htlL, htL, zero_smul, add_zero, smul_sub, sub_smul,
      one_smul]
    abel
/-- The straight-line homotopy `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`, `t(y) = y₀`,
`tl(y) = (y₁, …, yₘ)`, is proper on the cylinder `cyl(S) = {t ∈ [0,1], tl ∈ S}`.  `G` is continuous
and `cyl(S)` is closed, so `G⁻¹(K) ∩ cyl(S)` is closed.  For `y` in it,
`dist(F₀(tl y), G y) = t(y) · dist(F₁(tl y), F₀(tl y)) ≤ s`, so `F₀(tl y) ∈ cthickening s K` and
`y = (t y, tl y)` lies in the compact image of `[0,1] × (F₀⁻¹(cthickening s K) ∩ S)`. -/
theorem Submission.dph_sh_ae_affine_homotopy_isCompact_preimage_cyl :
    ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m') (S : Set (Eucl m)) (s : ℝ), Continuous F₀ → Continuous F₁ → IsClosed S → (∀ x ∈ S, dist (F₁ x) (F₀ x) ≤ s) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ S)) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ S}) := by
  intro m m' F₀ F₁ S s hF₀ hF₁ hS hs hprop K hK
  -- `t(y) = y₀` and `tl(y) = (y₁, …, yₘ)` are continuous linear maps.
  let tL : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  let tlL : Eucl (m + 1) →L[ℝ] Eucl m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j : Fin m => ContinuousLinearMap.proj j.succ) ∘L
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  -- `Φ(τ, x) = (τ, x)` is continuous, so `Q = Φ([0,1] × (F₀⁻¹(cthickening s K) ∩ S))` is compact.
  let Φ : ℝ × Eucl m → Eucl (m + 1) := fun p =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin m) ℝ p.2))
  have hΦ : Continuous Φ :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin m) ℝ).continuous.comp continuous_snd))
  have hQ : IsCompact (Φ '' (Icc (0 : ℝ) 1 ×ˢ (F₀ ⁻¹' cthickening s K ∩ S))) :=
    (isCompact_Icc.prod (hprop _ (hK.cthickening (r := s)))).image hΦ
  refine hQ.of_isClosed_subset ?_ ?_
  · -- `G` is continuous and `cyl(S) = t⁻¹[0,1] ∩ tl⁻¹(S)` is closed.
    have hG : Continuous fun y => F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)) :=
      (hF₀.comp tlL.continuous).add (tL.continuous.smul
        ((hF₁.comp tlL.continuous).sub (hF₀.comp tlL.continuous)))
    exact (hK.isClosed.preimage hG).inter
      ((isClosed_Icc.preimage tL.continuous).inter (hS.preimage tlL.continuous))
  · rintro y ⟨hyK, hy01, hyS⟩
    have hGy : F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)) ∈ K := hyK
    have hτ : tL y ∈ Icc (0 : ℝ) 1 := hy01
    have hx : tlL y ∈ S := hyS
    -- `dist(F₀(tl y), G y) = t(y) · dist(F₁(tl y), F₀(tl y)) ≤ s`.
    have hdist : dist (F₀ (tlL y)) (F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y))) ≤ s := by
      rw [dist_self_add_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1, ← dist_eq_norm]
      exact (mul_le_of_le_one_left dist_nonneg hτ.2).trans (hs _ hx)
    -- `Φ(t y, tl y) = y`.
    have hΦy : Φ (tL y, tlL y) = y := by
      change (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin m) ℝ ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) = y
      rw [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
        ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨(tL y, tlL y), ⟨hτ, mem_cthickening_of_dist_le _ _ s K hGy hdist, hx⟩, hΦy⟩
/-- Mass estimate: if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ C` everywhere
(Euclidean covector norm), then `|T(ω)| ≤ B · C`. -/
theorem Submission.cmb_abs_apply_le_of_massOn_le :
    ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B C : ℝ),
      0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      |T ω| ≤ B * C := by
  intro P n U W T ω B C hB hM hW hC
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- `C ≥ 0`, by evaluating the pointwise bound at `0`.
  have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
  -- For every `c > C`, both `±c⁻¹ ω` are mass-admissible for `W`, hence `|T ω| ≤ B c`.
  have key : ∀ c, C < c → |T ω| ≤ B * c := by
    intro c hc
    have hc0 : 0 < c := hC0.trans_lt hc
    have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * T ω ≤ B := by
      intro s hs
      have hadm : s • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hW, fun x => ?_⟩
        change covectorEuclideanNorm (s • (ω : DifferentialForm (Eucl P) n) x) ≤ 1
        rw [hsmul, hs, inv_mul_le_iff₀ hc0, mul_one]
        exact (hC x).trans hc.le
      have hle := (T.le_massOn hadm).trans hM
      rw [ENNReal.ofReal_le_ofReal_iff hB] at hle
      have hlin : T (s • ω) = s * T ω := by
        rw [map_smul, smul_eq_mul]
      rwa [hlin] at hle
    have h1 := hbound c⁻¹ (abs_of_pos (inv_pos.mpr hc0))
    have h2 := hbound (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc0)])
    have e1 : c * (c⁻¹ * T ω) = T ω := by field_simp
    have e2 : c * (-c⁻¹ * T ω) = -T ω := by field_simp
    rw [abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left h2 hc0.le
      rw [e2] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h1 hc0.le
      rw [e1] at this
      linarith
  -- Let `c ↓ C`: take `c = C + ε / (B + 1)`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < ε / (B + 1) := div_pos hε hB1
  have hBδ : B * (ε / (B + 1)) ≤ ε := by
    calc B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := by field_simp
  have := key (C + ε / (B + 1)) (by linarith)
  calc |T ω| ≤ B * (C + ε / (B + 1)) := this
    _ = B * C + B * (ε / (B + 1)) := by ring
    _ ≤ B * C + ε := by linarith
/-- Simon Ch. 6, 2.23 (p. 139), cut-off construction: if `f` is `C^∞` and proper on `A ⊆ U`, every
`ω ∈ 𝒟ʲ(V)` has a pull-back `η = ζ f^#ω ∈ 𝒟ʲ(U)` with `0 ≤ ζ ≤ 1`, `η = f^#ω` on an open
`N ⊇ A`, and `spt η ⊆ f⁻¹(spt ω)`. -/
theorem Submission.iwl_sp_exists_compatible_testForm :
    ∀ (P Q j : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (A : Set (Eucl P)) (f : Eucl P → Eucl Q),
      IsOpen U → A ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ A)) →
      ∀ ω : TestFormOn V j, ∃ (η : TestFormOn U j) (ζ : Eucl P → ℝ) (N : Set (Eucl P)),
        IsOpen N ∧ A ⊆ N ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
        (∀ x, (η : DifferentialForm (Eucl P) j) x =
          ζ x • ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap
            (fderiv ℝ f x)) ∧
        (∀ x ∈ N, (η : DifferentialForm (Eucl P) j) x =
          ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∧
        tsupport (η : DifferentialForm (Eucl P) j) ⊆
          f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) := by
  intro P Q j U V A f hU hAU hf hprop ω
  obtain ⟨⟨hωs, hωc⟩, hωV⟩ := ω.property
  have hωs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl Q) j) := hωs
  -- 1. `K = f⁻¹(spt ω) ∩ A` is compact, by properness.
  have hK : IsCompact (f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) ∩ A) :=
    hprop _ hωc.isCompact hωV
  set K := f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) ∩ A
  -- 2. A closed `δ`-thickening of `K` lies in `U`.
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU fun x hx => hAU hx.2
  -- 3. Smooth Urysohn: `support ζ = thickening δ K`, and `ζ = 1` exactly on `cthickening (δ/2) K`.
  obtain ⟨ζ, hζs, hζr, hζsupp, hζone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  have hζt : tsupport ζ ⊆ cthickening δ K := by
    rw [tsupport, hζsupp]
    exact closure_thickening_subset_cthickening δ K
  -- 4. The pull-back `p = f^# ω` is smooth, since `B ↦ B^#` is analytic.
  set p : DifferentialForm (Eucl P) j := fun x =>
    ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p := by
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin j) (F := ℝ)
          (fderiv ℝ f x)) :=
      (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff.comp hD
    exact hC.clm_apply (hωs'.comp hf)
  -- `p` vanishes wherever `ω ∘ f` does.
  have hp0 : ∀ x, f x ∉ tsupport (ω : DifferentialForm (Eucl Q) j) → p x = 0 := by
    intro x hx
    show ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x) = 0
    rw [image_eq_zero_of_notMem_tsupport hx,
      ← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, map_zero]
  -- 5. The test form `η = ζ p`.
  have hηs : IsSmoothForm (fun x => ζ x • p x) := hζs.smul hp
  have hηt : tsupport (fun x => ζ x • p x) ⊆ U :=
    (tsupport_smul_subset_left ζ p).trans (hζt.trans hδU)
  have hηc : HasCompactSupport (fun x => ζ x • p x) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_smul_subset_left ζ p).trans hζt)
  let η : TestFormOn U j := ⟨fun x => ζ x • p x, ⟨hηs, hηc⟩, hηt⟩
  refine ⟨η, ζ, thickening (δ / 2) K ∪ f ⁻¹' (tsupport (ω : DifferentialForm (Eucl Q) j))ᶜ,
    isOpen_thickening.union ((isClosed_tsupport _).isOpen_compl.preimage hf.continuous), ?_,
    fun x => hζr (mem_range_self x), fun x => rfl, ?_, ?_⟩
  · -- 7. `A ⊆ N`.
    intro x hx
    by_cases hfx : f x ∈ tsupport (ω : DifferentialForm (Eucl Q) j)
    · exact Or.inl (self_subset_thickening (half_pos hδ) K ⟨hfx, hx⟩)
    · exact Or.inr hfx
  · -- 8. `η = p` on `N`.
    rintro x (hx | hx)
    · have h1 : ζ x = 1 := (hζone x).1 (thickening_subset_cthickening _ _ hx)
      show ζ x • p x = p x
      rw [h1, one_smul]
    · show ζ x • p x = p x
      rw [hp0 x hx, smul_zero]
  · -- 6. `spt η ⊆ f⁻¹(spt ω)`, a closed set.
    refine closure_minimal ?_ ((isClosed_tsupport _).preimage hf.continuous)
    intro x hx
    by_contra hfx
    exact hx (show ζ x • p x = 0 by rw [hp0 x hfx, smul_zero])
/-- Slices of a test form `η` on `ℝ^{P+1} = ℝ × ℝ^P` across the first coordinate: with
`e₀ = (1, 0)` and `ι w = (0, w)`, the form `φ s x = η(s, x)(e₀, ι ·)` is the continuous linear
contraction `α ↦ α(e₀, ι ·)` applied to `η` along the affine map `x ↦ (s, x) = s • e₀ + ι x`, hence
smooth; it vanishes off the preimage of `tsupport η`, which is compact as `‖x‖ ≤ ‖(s, x)‖`; and it
depends jointly continuously on `(s, x)`. -/
theorem Submission.iwl_cr_ci_slice_testForm :
    ∀ (P m : ℕ) (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)),
      ∃ φ : ℝ → TestFormOn (univ : Set (Eucl P)) m,
        Continuous (fun p : ℝ × Eucl P => (φ p.1 : DifferentialForm (Eucl P) m) p.2) ∧
        ∀ (s : ℝ) (x : Eucl P) (v : Fin m → Eucl P),
          (φ s : DifferentialForm (Eucl P) m) x v =
            (η : DifferentialForm (Eucl (P + 1)) (m + 1))
              ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) := by
  intro P m η
  -- The linear inclusion `ι w = (0, w)`, the splitting `(s, x) = s • e₀ + ι x`, and
  -- `‖x‖ ≤ ‖(s, x)‖`.
  obtain ⟨ι, hι⟩ : ∃ ι : Eucl P →L[ℝ] Eucl (P + 1), ∀ w : Eucl P,
      ι w = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ w)) := by
    let ιₗ : Eucl P →ₗ[ℝ] Eucl (P + 1) :=
      { toFun := fun w => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ w))
        map_add' := fun a b => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun c a => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    exact ⟨LinearMap.toContinuousLinearMap ιₗ, fun w => rfl⟩
  have hΦ : ∀ (s : ℝ) (x : Eucl P),
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))
        = s • (EuclideanSpace.single 0 1 : Eucl (P + 1)) + ι x := by
    intro s x
    rw [hι]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  have hnorm : ∀ (s : ℝ) (x : Eucl P),
      ‖x‖ ≤ ‖s • (EuclideanSpace.single 0 1 : Eucl (P + 1)) + ι x‖ := by
    intro s x
    rw [← hΦ, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    apply Real.sqrt_le_sqrt
    simp only [PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply, Fin.cons_zero,
      Fin.cons_succ, PiLp.continuousLinearEquiv_apply]
    exact le_add_of_nonneg_left (sq_nonneg _)
  set e₀ : Eucl (P + 1) := EuclideanSpace.single 0 1
  -- The continuous linear contraction `L α = α(e₀, ι ·)` of covectors.
  obtain ⟨L, hL⟩ : ∃ L : Covector (Eucl (P + 1)) (m + 1) →L[ℝ] Covector (Eucl P) m,
      ∀ (α : Covector (Eucl (P + 1)) (m + 1)) (v : Fin m → Eucl P),
        L α v = α (Fin.cons e₀ fun i => ι (v i)) := by
    refine ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM ι).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Eucl (P + 1)) m) e₀).comp
        (ContinuousAlternatingMap.curryLeftLI :
          Covector (Eucl (P + 1)) (m + 1) →ₗᵢ[ℝ] _).toContinuousLinearMap), ?_⟩
    intro α v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, ContinuousAlternatingMap.curryLeftLI_apply,
      ContinuousLinearMap.apply_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    rfl
  have hηs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (η : DifferentialForm (Eucl (P + 1)) (m + 1)) :=
    η.2.1.1
  have hηc : HasCompactSupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)) := η.2.1.2
  have hΦc : ∀ s : ℝ, Continuous fun x : Eucl P => s • e₀ + ι x := fun s =>
    continuous_const.add ι.continuous
  -- Each slice `x ↦ L (η (s • e₀ + ι x))` is a test form on `ℝ^P`.
  have htest : ∀ s : ℝ, (fun x : Eucl P => L ((η : DifferentialForm (Eucl (P + 1)) (m + 1))
      (s • e₀ + ι x))) ∈ TestFormOn (univ : Set (Eucl P)) m := by
    intro s
    refine ⟨⟨?_, ?_⟩, subset_univ _⟩
    · exact L.contDiff.comp (hηs.comp (contDiff_const.add ι.contDiff))
    · obtain ⟨ρ, hρ⟩ := hηc.isCompact.isBounded.subset_closedBall 0
      have hK : IsCompact ((fun x : Eucl P => s • e₀ + ι x) ⁻¹'
          tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1))) := by
        refine (isCompact_closedBall (0 : Eucl P) ρ).of_isClosed_subset
          ((isClosed_tsupport _).preimage (hΦc s)) ?_
        intro x hx
        have hx' := hρ hx
        rw [mem_closedBall, dist_zero_right] at hx' ⊢
        exact (hnorm s x).trans hx'
      refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
      exact (tsupport_comp_subset (g := L) (map_zero L) _).trans
        (tsupport_comp_subset_preimage _ (hΦc s))
  refine ⟨fun s => ⟨_, htest s⟩, ?_, ?_⟩
  · change Continuous fun p : ℝ × Eucl P =>
      L ((η : DifferentialForm (Eucl (P + 1)) (m + 1)) (p.1 • e₀ + ι p.2))
    exact L.continuous.comp (hηs.continuous.comp
      ((continuous_fst.smul continuous_const).add (ι.continuous.comp continuous_snd)))
  · intro s x v
    change L ((η : DifferentialForm (Eucl (P + 1)) (m + 1)) (s • e₀ + ι x)) v = _
    rw [hL, hΦ s x]
    simp only [hι]
/-- A current kills every test form whose support misses `spt T`: `tsupport ω` is a compact subset
of the zero region, so finitely many open `W ⊂⊂ U` on which `T` vanishes cover it, and a smooth
partition of unity `ψᵢ` on `tsupport ω` subordinate to them splits `ω = ∑ᵢ ψᵢ ω` into test forms
supported in those `W`. -/
theorem Submission.isoperimetric_apply_eq_zero_of_disjoint_support :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) n)) T.support → T ω = 0 := by
  intro P n U T ω hdisj
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) n)) := ω.property.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) n) ⊆ U := ω.property.2
  -- `tsupport ω` lies in the zero region: the union of the open `W ⊂⊂ U` on which `T` vanishes.
  have hKZ : tsupport (ω : DifferentialForm (Eucl P) n) ⊆
      ⋃ W : {W : Set (Eucl P) // IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧
        T.VanishesOn W}, (W : Set (Eucl P)) := by
    intro x hx
    have hxZ : x ∈ T.zeroRegion := by
      by_contra h
      exact Set.disjoint_left.1 hdisj hx ⟨hKU hx, h⟩
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 hxZ
    exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
  -- A finite subcover, indexed by the finset `t`.
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover _ (fun W => W.2.1) hKZ
  have hcov : tsupport (ω : DifferentialForm (Eucl P) n) ⊆
      ⋃ i : t, ((i : {W : Set (Eucl P) // IsOpen W ∧ IsCompact (closure W) ∧
        closure W ⊆ U ∧ T.VanishesOn W}) : Set (Eucl P)) := by
    intro x hx
    obtain ⟨W, hWt, hxW⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨⟨W, hWt⟩, hxW⟩
  -- A smooth partition of unity `f i` on `tsupport ω` with `tsupport (f i) ⊆ W i`.
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Eucl P)) hKc.isClosed _ (fun i => i.1.2.1) hcov
  -- `η i = f i • ω` is a test form in `U` supported in `W i`, hence `T (η i) = 0`.
  have hfs : ∀ i, ContDiff ℝ _ (f i : Eucl P → ℝ) :=
    fun i => contMDiff_iff_contDiff.1 (f i).contMDiff
  have hsm : ∀ i, ContDiff ℝ _ (fun x => f i x • (ω : DifferentialForm (Eucl P) n) x) :=
    fun i => (hfs i).smul ω.property.1.1
  have hcs : ∀ i, HasCompactSupport (fun x => f i x • (ω : DifferentialForm (Eucl P) n) x) :=
    fun i => hKc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_right (fun x => f i x) _)
  have hsU : ∀ i, tsupport (fun x => f i x • (ω : DifferentialForm (Eucl P) n) x) ⊆ U :=
    fun i => (tsupport_smul_subset_right (fun x => f i x) _).trans hKU
  let η : t → TestFormOn U n := fun i =>
    ⟨fun x => f i x • (ω : DifferentialForm (Eucl P) n) x, ⟨⟨hsm i, hcs i⟩, hsU i⟩⟩
  have hη : ∀ i, T (η i) = 0 := fun i =>
    i.1.2.2.2.2 (η i) ((tsupport_smul_subset_left (fun x => f i x) _).trans (hf i))
  -- `ω = ∑ i, η i`: `∑ i, f i = 1` on `tsupport ω`, and `ω = 0` off it.
  have hsum : ω = ∑ i, η i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Eucl P) n) x =
      ∑ i, f i x • (ω : DifferentialForm (Eucl P) n) x
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ tsupport (ω : DifferentialForm (Eucl P) n)
    · rw [← finsum_eq_sum_of_fintype, f.sum_eq_one hx, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  change T.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => hη i

/-- Locality of currents: test forms that agree on an open neighbourhood `N` of `spt T` have the
same value, since `ψ - φ` vanishes on `N`, so its support lies in the closed set `Nᶜ`, which misses
`spt T`. -/
theorem Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ψ φ : TestFormOn U n)
      (N : Set (Eucl P)), IsOpen N → T.support ⊆ N →
      (∀ x ∈ N, (ψ : DifferentialForm (Eucl P) n) x = (φ : DifferentialForm (Eucl P) n) x) →
      T ψ = T φ := by
  intro P n U T ψ φ N hN hTN hψφ
  -- `ψ - φ` vanishes on the open set `N`, so `tsupport (ψ - φ) ⊆ Nᶜ`.
  have hsupp : tsupport ((ψ - φ : TestFormOn U n) : DifferentialForm (Eucl P) n) ⊆ Nᶜ := by
    refine closure_minimal ?_ hN.isClosed_compl
    intro x hx hxN
    apply hx
    rw [Submodule.coe_sub, Pi.sub_apply, hψφ x hxN, sub_self]
  -- `Nᶜ` misses `spt T ⊆ N`, so `T (ψ - φ) = 0`.
  have hzero : T (ψ - φ) = 0 :=
    Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U T (ψ - φ)
      (Set.disjoint_of_subset_left hsupp (Set.disjoint_compl_left_iff_subset.2 hTN))
  have hsub : T.toCurrent (ψ - φ) = T.toCurrent ψ - T.toCurrent φ := map_sub T.toCurrent ψ φ
  change T.toCurrent ψ = T.toCurrent φ
  rw [← sub_eq_zero, ← hsub]
  exact hzero

/-- Locality of an interval product: if `Z η = ∫₀¹ X (φ s) ds` for the slices
`φ s x = η(s, x)(e₀, ι ·)` of every `η`, then `Z η = Z η'` whenever `η = η'` on an open
`N ⊇ [0, 1] × spt X`, since for `s ∈ [0, 1]` the slices of `η` and `η'` agree on the open
neighbourhood `j_s⁻¹ N` of `spt X`, where `j_s x = (s, x)`, so locality of `X` makes the two
integrands agree on `[0, 1]`. -/
theorem Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl :
    ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q)
      (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (q + 1)),
      (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (q + 1))
        (φ : ℝ → TestFormOn (univ : Set (Eucl m)) q),
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin q → Eucl m),
          (φ s : DifferentialForm (Eucl m) q) x v =
            (η : DifferentialForm (Eucl (m + 1)) (q + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
      ∀ (η η' : TestFormOn (univ : Set (Eucl (m + 1))) (q + 1)) (N : Set (Eucl (m + 1))),
        IsOpen N →
        {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
          (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N →
        (∀ y ∈ N, (η : DifferentialForm (Eucl (m + 1)) (q + 1)) y =
          (η' : DifferentialForm (Eucl (m + 1)) (q + 1)) y) →
        Z η = Z η' := by
  intro m q X Z hZ η η' N hN hcyl hηη'
  -- Slice families `φ s x = η(s, x)(e₀, ι ·)` and `φ' s x = η'(s, x)(e₀, ι ·)`, and the
  -- product characterization of `Z`.
  obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm m q η
  obtain ⟨φ', -, hφ'⟩ := Submission.iwl_cr_ci_slice_testForm m q η'
  rw [hZ η φ fun s _ => hφ s, hZ η' φ' fun s _ => hφ' s]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  -- The slice map `j_s x = (s, x)` is continuous and sends `spt X` into the cylinder, so
  -- `j_s⁻¹ N` is an open neighbourhood of `spt X` on which `φ s = φ' s`.
  have hj : Continuous fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
      (continuous_const.finCons (EuclideanSpace.equiv (Fin m) ℝ).continuous)
  refine Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support m q univ X (φ s) (φ' s) _
    (hN.preimage hj) (fun x hx => hcyl ?_) fun x hx => ?_
  · simp only [mem_ofPred_eq, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero,
      Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨hs, hx⟩
  · ext v
    rw [hφ, hφ', hηη' _ hx]
/-- Horizontal slices of a compatible form: for `j_s(x) = (s, x)`, the slice `θ_s = j_s^# θ` is a
test form on `ℝ^m` with `θ_s(x)(v) = θ(s, x)((0, v₁), …, (0, v_q))`, and `θ_s = (G ∘ j_s)^# ω`
at every `x` with `(s, x) ∈ N` whenever `θ = G^# ω` on `N` (chain rule). -/
theorem Submission.dph_sh_slice_compatible_testForm :
    ∀ (m m' q : ℕ) (G : Eucl (m + 1) → Eucl m') (ω : DifferentialForm (Eucl m') q)
      (θ : TestFormOn (univ : Set (Eucl (m + 1))) q) (N : Set (Eucl (m + 1))) (s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G →
      (∀ y ∈ N, (θ : DifferentialForm (Eucl (m + 1)) q) y =
        (ω (G y)).compContinuousLinearMap (fderiv ℝ G y)) →
      ∃ θs : TestFormOn (univ : Set (Eucl m)) q,
        (∀ (x : Eucl m) (v : Fin q → Eucl m), (θs : DifferentialForm (Eucl m) q) x v =
          (θ : DifferentialForm (Eucl (m + 1)) q)
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
        ∀ x : Eucl m, (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ N →
          (θs : DifferentialForm (Eucl m) q) x =
            (ω ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap
              (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x) := by
  intro m m' q G ω θ N s hG hθN
  -- 1. `j_s x = (s, x)` has derivative `L v = (0, v)` everywhere, so it is `C^∞`.
  let L : Eucl m →L[ℝ] Eucl (m + 1) :=
    ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm : (Fin (m + 1) → ℝ) →L[ℝ] Eucl (m + 1)).comp
      ((0 : Eucl m →L[ℝ] ℝ).finCons
        (EuclideanSpace.equiv (Fin m) ℝ : Eucl m →L[ℝ] (Fin m → ℝ)))
  let j : Eucl m → Eucl (m + 1) := fun x =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))
  have hjd : ∀ x, HasFDerivAt j L x := fun x =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.hasFDerivAt.comp x
      ((hasFDerivAt_const s x).finCons (EuclideanSpace.equiv (Fin m) ℝ).hasFDerivAt)
  have hjs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) j := by
    refine contDiff_infty_iff_fderiv.2 ⟨fun x => (hjd x).differentiableAt, ?_⟩
    rw [show fderiv ℝ j = fun _ => L from funext fun x => (hjd x).fderiv]
    exact contDiff_const
  -- 2. `j_s` is proper: the continuous map `tl (y₀, y') = y'` is a left inverse.
  let tl : Eucl (m + 1) → Eucl m := fun y =>
    (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))
  have htl : Continuous tl :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp <| continuous_pi fun i : Fin m =>
      (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).continuous
  have htlj : ∀ x, tl (j x) = x := fun x => by
    simp only [tl, j, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  have hprop : ∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ univ →
      IsCompact (j ⁻¹' K ∩ univ) := fun K hK _ => by
    rw [inter_univ]
    exact (hK.image htl).of_isClosed_subset (hK.isClosed.preimage hjs.continuous)
      fun x hx => ⟨j x, hx, htlj x⟩
  -- 3. The slice `θ_s = j_s^# θ ∈ 𝒟^q(ℝ^m)`; it equals `θ(j_s x) ∘ L` everywhere.
  obtain ⟨θs, -, N₀, -, hN₀, -, -, hθsN, -⟩ :=
    Submission.iwl_sp_exists_compatible_testForm m (m + 1) q univ univ univ j isOpen_univ
      subset_rfl hjs hprop θ
  have hθs : ∀ x, (θs : DifferentialForm (Eucl m) q) x =
      ((θ : DifferentialForm (Eucl (m + 1)) q) (j x)).compContinuousLinearMap L := fun x => by
    rw [hθsN x (hN₀ (mem_univ x)), (hjd x).fderiv]
  refine ⟨θs, fun x v => by rw [hθs x]; rfl, fun x hx => ?_⟩
  -- 4. Chain rule `D(G ∘ j_s)(x) = DG(j_s x) ∘ L`, and `θ = G^# ω` at `j_s x ∈ N`.
  have hGj : HasFDerivAt (fun x : Eucl m => G (j x)) ((fderiv ℝ G (j x)).comp L) x :=
    ((hG.differentiable (by simp)) (j x)).hasFDerivAt.comp x (hjd x)
  rw [hθs x, hGj.fderiv, hθN (j x) hx]
  ext v
  rfl
/-- Exterior differentiation commutes with pull-back, locally (Simon Ch. 6, §1, (1.14)): if `θ`
agrees with the pull-back `G^#ω` of a `C^∞` form `ω` by a `C^∞` map `G` on an open set `N`, then
`dθ = G^#(dω)` on `N`.  `dθ(x)` only depends on the germ of `θ` at `x`. -/
theorem Submission.dph_sh_extDeriv_compatible : ∀ (P Q j : ℕ) (G : Eucl P → Eucl Q) (ω : DifferentialForm (Eucl Q) j) (θ : DifferentialForm (Eucl P) j) (N : Set (Eucl P)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → IsOpen N → (∀ x ∈ N, θ x = (ω (G x)).compContinuousLinearMap (fderiv ℝ G x)) → ∀ x ∈ N, exteriorDerivative θ x = ((exteriorDerivative ω) (G x)).compContinuousLinearMap (fderiv ℝ G x) := by
  intro P Q j G ω θ N hG hω hN hθ x hx
  -- `θ` agrees with the pull-back `G^#ω` on the open neighbourhood `N` of `x`.
  have hloc : θ =ᶠ[𝓝 x] fun y => (ω (G y)).compContinuousLinearMap (fderiv ℝ G y) :=
    Filter.eventually_of_mem (hN.mem_nhds hx) hθ
  -- Locality of `d`, then `d` commutes with pull-back by the `C^∞` map `G`.
  exact hloc.extDeriv_eq.trans
    (extDeriv_pullback ((hω.differentiable (by simp)).differentiableAt) hG.contDiffAt (by simp))
/-- Homogeneity of the Euclidean coefficient norm (Simon Ch. 6, 1.15, 2.4–2.5):
`|c α| = |c| |α|`.  Every coefficient of `c • α` on an increasing tuple of basis vectors is
`c` times that of `α`, so each squared coefficient gains the factor `c²`; pull `c²` out of the
finite sum and use `√(c² s) = √(c²) √s = |c| √s`. -/
theorem Submission.fiw_tb_ext_covectorNorm_smul : ∀ (P q : ℕ) (c : ℝ) (α : Covector (Eucl P) q), covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
  intro P q c α
  unfold covectorEuclideanNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs
  · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
  · simp
/-- Counting identity: for any family `u` of vectors of `ℝ^P` and any `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = k! ∑_{I strictly increasing} φ(u_{I 0}, …, u_{I (k-1)})²`,
where `I` ranges over all maps `Fin k → Fin P`. -/
theorem Submission.slicing_mb_wn_sq_sum_eq_factorial_mul :
    ∀ (P k : ℕ) (u : Fin P → Eucl P) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        (k.factorial : ℝ) * ∑ I : Fin k → Fin P,
          if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  classical
  set g : (Fin k → Fin P) → ℝ := fun I => (φ (fun i => u (I i))) ^ 2
  -- A non-injective `I` repeats a vector of `u ∘ I`, so `φ (u ∘ I) = 0`.
  have h0 : ∀ I : Fin k → Fin P, ¬Function.Injective I → g I = 0 := by
    intro I hI
    have hv : ¬Function.Injective (fun i => u (I i)) :=
      fun h => hI fun a b hab => h (by simp only [hab])
    simp only [g, φ.map_eq_zero_of_not_injective _ hv, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  -- `φ (u ∘ I ∘ σ) = sign σ • φ (u ∘ I)`, so the square is invariant under permutations.
  have hperm : ∀ (I : Fin k → Fin P) (σ : Equiv.Perm (Fin k)), g (I ∘ σ) = g I := by
    intro I σ
    have h : φ (fun i => u ((I ∘ σ) i)) = Equiv.Perm.sign σ • φ (fun i => u (I i)) :=
      φ.toAlternatingMap.map_perm (fun i => u (I i)) σ
    simp only [g, h]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h' <;> simp [h']
  -- Write both sides as sums over the injective, resp. strictly increasing, maps.
  have hL : ∑ I, g I = ∑ I ∈ Finset.univ.filter Function.Injective, g I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · exact h0 I h
  have hR : (∑ I : Fin k → Fin P, if StrictMono I then g I else 0) =
      ∑ I ∈ Finset.univ.filter StrictMono, g I := (Finset.sum_filter _ _).symm
  -- `(σ, β) ↦ β ∘ σ` is a bijection from permutations × strictly increasing maps onto the
  -- injective maps, with inverse `I ↦ ((sort I)⁻¹, I ∘ sort I)`.
  have hbij : ∑ I ∈ Finset.univ.filter Function.Injective, g I =
      ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))) ×ˢ Finset.univ.filter StrictMono,
        g (p.2 ∘ p.1) := by
    refine Finset.sum_nbij' (fun I => ((Tuple.sort I)⁻¹, I ∘ Tuple.sort I))
      (fun p => p.2 ∘ p.1) ?_ ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
      exact (Tuple.monotone_sort I).strictMono_of_injective (hI.comp (Tuple.sort I).injective)
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.injective.comp σ.injective
    · intro I _
      funext i
      simp
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      -- sorting `β ∘ σ` recovers the strictly increasing `β`
      have hsorted : (β ∘ σ) ∘ Tuple.sort (β ∘ σ) = β := by
        rw [Tuple.comp_perm_comp_sort_eq_comp_sort,
          (Tuple.sort_eq_refl_iff_monotone).2 hp.monotone]
        rfl
      have hσ : σ * Tuple.sort (β ∘ σ) = 1 := by
        ext i
        have := congrFun hsorted i
        simp only [Function.comp_apply] at this
        simpa using congrArg Fin.val (hp.injective this)
      have hinv : (Tuple.sort (β ∘ σ))⁻¹ = σ := by
        rw [inv_eq_iff_eq_inv]
        exact eq_inv_of_mul_eq_one_right hσ
      simp only [hinv, hsorted]
    · intro I _
      congr 1
      funext i
      simp
  -- Each permutation contributes `∑_β g β`, and there are `k!` permutations.
  rw [hL, hbij, hR, Finset.sum_product]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- Basis independence of the full coefficient sum (Parseval's identity, one slot at a time): for
orthonormal bases `u`, `v` of `ℝ^P` and a `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = ∑_I φ(v_{I 0}, …, v_{I (k-1)})²`, both sums over all index maps
`I : Fin k → Fin P`.  Induction on `k`: write `I = (i, J)` and `φ(w_I) = (φ.curryLeft w_i)(w_J)`,
replace `u` by `v` in the last `k` slots by the induction hypothesis for `φ.curryLeft (u i)`, then
in slot `0` by `OrthonormalBasis.norm_dual` for the functional `z ↦ (φ.curryLeft z)(v_J)`. -/
theorem Submission.slicing_mb_wn_sq_sum_onb_invariant :
    ∀ (P k : ℕ) (u v : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        ∑ I : Fin k → Fin P, (φ (fun i => v (I i))) ^ 2 := by
  intro P k u v
  induction k with
  | zero =>
    -- Both families are the empty tuple.
    intro φ
    exact Fintype.sum_congr _ _ fun I => by
      rw [Subsingleton.elim (fun i => u (I i)) (fun i => v (I i))]
  | succ k ih =>
    intro φ
    -- Split `I = Fin.cons i J`; then `φ(w_I) = (φ.curryLeft w_i)(w_J)`.
    have hsplit : ∀ w : OrthonormalBasis (Fin P) ℝ (Eucl P),
        ∑ I : Fin (k + 1) → Fin P, (φ (fun i => w (I i))) ^ 2 =
          ∑ i : Fin P, ∑ J : Fin k → Fin P, (φ.curryLeft (w i) (fun j => w (J j))) ^ 2 := by
      intro w
      rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Fin P).sum_comp]
      refine Fintype.sum_congr _ _ fun p => ?_
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    -- Slots `1, …, k`: the induction hypothesis for each `k`-covector `φ.curryLeft (u i)`.
    rw [hsplit u, hsplit v]
    simp_rw [ih]
    -- Slot `0`: for each `J`, Parseval for `ℓ_J z = (φ.curryLeft z)(v_J)` in the bases `u`, `v`.
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun J => ?_
    let ℓ : StrongDual ℝ (Eucl P) :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (fun j => v (J j))).comp φ.curryLeft
    have hu := u.norm_dual ℓ
    have hv := v.norm_dual ℓ
    simp only [ℓ, ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.apply_apply] at hu hv
    rw [← hu, ← hv]

/-- The Euclidean coefficient norm of a `k`-covector can be computed in any orthonormal basis
`u` of `ℝ^P` (Simon Ch. 6, 1.5–1.6 and Remark 2.6): `|φ|² = ∑_{I increasing} φ(u_I)²`.
With `e` the standard basis used by `covectorEuclideanNorm` and `N_w(φ) = ∑_{all I} φ(w_I)²`,
`k! |φ|² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`, and `k! ≠ 0`. -/
theorem Submission.slicing_mb_wn_norm_sq_eq_onb_sum :
    ∀ (P k : ℕ) (u : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      covectorEuclideanNorm φ ^ 2 =
        ∑ I : Fin k → Fin P, if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  -- `k! ∑_{I increasing} φ(e_I)² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`.
  have key := (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k
      (EuclideanSpace.basisFun (Fin P) ℝ) φ).symm.trans
    ((Submission.slicing_mb_wn_sq_sum_onb_invariant P k
      (EuclideanSpace.basisFun (Fin P) ℝ) u φ).trans
        (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k u φ))
  -- `|φ|² = ∑_{I increasing} φ(e_I)²`: the radicand is a sum of squares and zeros.
  rw [covectorEuclideanNorm, Real.sq_sqrt]
  · exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) key
  · exact Finset.sum_nonneg fun I _ => by split_ifs <;> positivity

/-- Full tuple sum of squared coefficients in the standard basis `e` of `ℝ^m`: for a `j`-covector
`γ`, `∑_i γ(e_{i 0}, …, e_{i (j-1)})² = j! |γ|²`, the sum over all index maps `i : Fin j → Fin m`.
The counting identity turns the left side into `j! ∑_{I increasing} γ(e_I)²`, and the
orthonormal-basis formula for `|γ|²`, applied to `e` itself, identifies that sum with `|γ|²`. -/
theorem Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul :
    ∀ (m j : ℕ) (γ : Covector (Eucl m) j),
      ∑ i : Fin j → Fin m, (γ (fun k => EuclideanSpace.basisFun (Fin m) ℝ (i k))) ^ 2 =
        (j.factorial : ℝ) * covectorEuclideanNorm γ ^ 2 := by
  intro m j γ
  rw [Submission.slicing_mb_wn_norm_sq_eq_onb_sum m j (EuclideanSpace.basisFun (Fin m) ℝ) γ]
  exact Submission.slicing_mb_wn_sq_sum_eq_factorial_mul m j (EuclideanSpace.basisFun (Fin m) ℝ) γ
/-- One-slot bound: for `L : ℝ^P → ℝ^Q` and a linear functional `f` on `ℝ^Q`,
`∑_a f(L e_a)² ≤ ‖L‖² ∑_b f(e′_b)²`.  The Riesz vector `g = (f(e′_b))_b` gives `f = ⟨g, ·⟩`
and the test vector `u = (f(L e_a))_a` has `f(L u) = |u|²`, so Cauchy–Schwarz and the operator
norm give `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`; cancel `|u|` and square. -/
theorem Submission.iwl_sp_pn_sum_sq_comp_basis_le : ∀ (P Q : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (f : Eucl Q →ₗ[ℝ] ℝ), ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 ≤ ‖L‖ ^ 2 * ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 := by
  intro P Q L f
  -- The Riesz vector `g` of `f`: `f y = ⟨g, y⟩` and `|g|² = ∑_b f(e′_b)²`.
  set g : Eucl Q := WithLp.toLp 2 (fun b => f (EuclideanSpace.basisFun (Fin Q) ℝ b)) with hg_def
  have hf : ∀ y : Eucl Q, f y = inner ℝ g y := by
    intro y
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hg_def]
  have hg : ‖g‖ ^ 2 = ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  -- The test vector `u`: `|u|² = ∑_a f(L e_a)²` and `f(L u) = |u|²`.
  set u : Eucl P := WithLp.toLp 2 (fun a => f (L (EuclideanSpace.basisFun (Fin P) ℝ a)))
    with hu_def
  have hu : ‖u‖ ^ 2 = ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hfLu : f (L u) = ‖u‖ ^ 2 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr u]
    rw [map_sum, map_sum, hu]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hu_def, sq]
  -- Cauchy–Schwarz and the operator norm: `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`.
  have key : ‖u‖ ^ 2 ≤ ‖g‖ * (‖L‖ * ‖u‖) := by
    rw [← hfLu, hf]
    calc inner ℝ g (L u) ≤ ‖g‖ * ‖L u‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * (‖L‖ * ‖u‖) := mul_le_mul_of_nonneg_left (L.le_opNorm u) (norm_nonneg _)
  -- Cancel `|u|` (trivial if `|u| = 0`), then square.
  have hle : ‖u‖ ≤ ‖L‖ * ‖g‖ := by
    rcases (norm_nonneg u).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · have : ‖u‖ * ‖u‖ ≤ (‖L‖ * ‖g‖) * ‖u‖ := by nlinarith [key]
      exact le_of_mul_le_mul_right this hpos
  rw [← hu, ← hg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Multilinear tensor-power bound: for every continuous linear `L : ℝ^P → ℝ^Q` and every
`j`-multilinear `β : (ℝ^Q)^j → ℝ` (not necessarily alternating or continuous),
`∑_{i : Fin j → Fin P} β(L e_{i(1)}, …, L e_{i(j)})²`
`≤ (‖L‖²)^j ∑_{i : Fin j → Fin Q} β(e′_{i(1)}, …, e′_{i(j)})²`,
with `e`, `e′` the standard bases.  Induction on `j`, generalizing `β`: split the sums over
`Fin (j + 1) → Fin n` along `Fin.cons`, apply the inductive hypothesis to `β.curryLeft (L e_a)`,
exchange the sums and bound each slot functional `y ↦ β(Fin.cons y (e′ ∘ i″))` by the one-slot
estimate `Submission.iwl_sp_pn_sum_sq_comp_basis_le`. -/
theorem Submission.iwl_sp_pn_multilinear_sum_sq_le :
    ∀ (P Q j : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (β : MultilinearMap ℝ (fun _ : Fin j => Eucl Q) ℝ),
      ∑ i : Fin j → Fin P, (β (fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i k)))) ^ 2 ≤
        (‖L‖ ^ 2) ^ j *
          ∑ i : Fin j → Fin Q, (β (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k))) ^ 2 := by
  intro P Q j L
  induction j with
  | zero =>
    -- Both sums have the single empty tuple as index, and both arguments of `β` are empty.
    intro β
    rw [Fintype.sum_unique, Fintype.sum_unique, pow_zero, one_mul]
    exact (congrArg (fun v => β v ^ 2) (Subsingleton.elim _ _)).le
  | succ j ih =>
    intro β
    -- Sums over `Fin (j + 1) → Fin n` split along `Fin.cons` (`Fin.consEquiv`).
    have split : ∀ (n : ℕ) (G : (Fin (j + 1) → Fin n) → ℝ),
        ∑ i, G i = ∑ a : Fin n, ∑ i' : Fin j → Fin n, G (Fin.cons a i') := by
      intro n G
      rw [← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin n) _ _ fun _ => rfl).symm
    -- The slot functionals `y ↦ β (Fin.cons y w)` are linear.
    let slot : (Fin j → Eucl Q) → Eucl Q →ₗ[ℝ] ℝ := fun w =>
      { toFun := fun y => β (Fin.cons y w)
        map_add' := fun x y => β.cons_add w x y
        map_smul' := fun c x => β.cons_smul w c x }
    calc ∑ i : Fin (j + 1) → Fin P, (β fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i k))) ^ 2
        = ∑ a : Fin P, ∑ i' : Fin j → Fin P,
            (β.curryLeft (L (EuclideanSpace.basisFun (Fin P) ℝ a))
              fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i' k))) ^ 2 := by
          rw [split P]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ =>
            congrArg (fun v => β v ^ 2)
              (Fin.comp_cons (fun p => L (EuclideanSpace.basisFun (Fin P) ℝ p)) a i')
      -- the inductive hypothesis for `β.curryLeft (L e_a)`
      _ ≤ ∑ a : Fin P, (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q,
            (β.curryLeft (L (EuclideanSpace.basisFun (Fin P) ℝ a))
              fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k)) ^ 2 :=
          Finset.sum_le_sum fun a _ => ih _
      _ = (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q, ∑ a : Fin P,
            (slot (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))
              (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          rfl
      -- the one-slot bound for each slot functional
      _ ≤ (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q, ‖L‖ ^ 2 * ∑ b : Fin Q,
            (slot (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))
              (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i'' _ => Submission.iwl_sp_pn_sum_sq_comp_basis_le P Q L _)
            (by positivity)
      _ = (‖L‖ ^ 2) ^ (j + 1) * ∑ b : Fin Q, ∑ i'' : Fin j → Fin Q,
            (β (Fin.cons (EuclideanSpace.basisFun (Fin Q) ℝ b)
              fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm, pow_succ (‖L‖ ^ 2) j, mul_assoc]
          rfl
      _ = (‖L‖ ^ 2) ^ (j + 1) * ∑ i : Fin (j + 1) → Fin Q,
            (β fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k)) ^ 2 := by
          rw [split Q]
          exact congrArg _ (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i'' _ =>
            congrArg (fun v => β v ^ 2)
              (Fin.comp_cons (fun p => EuclideanSpace.basisFun (Fin Q) ℝ p) b i'').symm)

/-- Pullback bound for the Euclidean covector norm: for `L : ℝ^P → ℝ^Q` and a `j`-covector `α`
on `ℝ^Q`, `|L^#α| ≤ ‖L‖^j |α|`.  The multilinear bound
`Submission.iwl_sp_pn_multilinear_sum_sq_le` for `β := α` gives
`∑_i α(L e∘i)² ≤ (‖L‖²)^j ∑_i α(e′∘i)²`, and `α(L e∘i) = (L^#α)(e∘i)` by definition.  By
`Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul` the two sums over all index tuples are
`j! |L^#α|²` and `j! |α|²`; cancel `j! > 0` and take square roots. -/
theorem Submission.iwl_sp_covectorEuclideanNorm_pullback_le : ∀ (P Q j : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (α : Covector (Eucl Q) j), covectorEuclideanNorm (α.compContinuousLinearMap L) ≤ ‖L‖ ^ j * covectorEuclideanNorm α := by
  intro P Q j L α
  -- Sums over all index tuples: `j! |L^#α|²` on `ℝ^P` and `j! |α|²` on `ℝ^Q`.
  have hP := Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul P j (α.compContinuousLinearMap L)
  have hQ := Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul Q j α
  -- The multilinear bound for `β := α`.
  have hβ := Submission.iwl_sp_pn_multilinear_sum_sq_le P Q j L α.toMultilinearMap
  have key : (j.factorial : ℝ) * covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2 ≤
      (j.factorial : ℝ) * (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 :=
    calc (j.factorial : ℝ) * covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2
        = ∑ i : Fin j → Fin P,
            (α.compContinuousLinearMap L fun k => EuclideanSpace.basisFun (Fin P) ℝ (i k)) ^ 2 :=
          hP.symm
      -- `(L^#α)(e∘i) = α(L e∘i)` holds by definition (`compContinuousLinearMap_apply`).
      _ ≤ (‖L‖ ^ 2) ^ j * ∑ i : Fin j → Fin Q,
            (α fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k)) ^ 2 := hβ
      _ = (j.factorial : ℝ) * (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 := by
          rw [hQ]
          ring
  -- Cancel `j! > 0`, then take square roots of nonnegative quantities.
  have hsq : covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2 ≤
      (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 :=
    le_of_mul_le_mul_left key (by exact_mod_cast j.factorial_pos)
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg (norm_nonneg L) j) (covectorEuclideanNorm_nonneg α))

/-- Contraction bound for the Euclidean coefficient norm: if the `k`-covector `δ` is the
contraction `γ(w, ·)` of a `(k+1)`-covector `γ` with `w ∈ ℝ^p`, then `|δ| ≤ √(k+1) ‖w‖ |γ|`.
Expand `w = ∑_b w_b e_b` in the first slot, so `δ(e_J) = ∑_b w_b γ(e_{(b, J)})`; Cauchy–Schwarz
gives `δ(e_J)² ≤ ‖w‖² ∑_b γ(e_{(b, J)})²`.  Summing over all `J` and reindexing `(b, J) ↦ I`
yields `k! |δ|² ≤ ‖w‖² (k+1)! |γ|²` by the all-tuples identity; cancel `k!` and take roots. -/
theorem Submission.dph_sh_ib_covectorEuclideanNorm_contract_le :
    ∀ (p k : ℕ) (γ : Covector (Eucl p) (k + 1)) (w : Eucl p) (δ : Covector (Eucl p) k),
      (∀ u : Fin k → Eucl p, δ u = γ (Fin.cons w u)) →
        covectorEuclideanNorm δ ≤ Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ := by
  intro p k γ w δ hδ
  set e := EuclideanSpace.basisFun (Fin p) ℝ with he
  -- Linearity in the first slot: `δ(e_J) = ∑_b w_b γ(e_{(b, J)})`.
  have hexp : ∀ J : Fin k → Fin p, δ (fun i => e (J i)) =
      ∑ b : Fin p, w b * γ (fun i => e ((Fin.cons b J : Fin (k + 1) → Fin p) i)) := by
    intro J
    have hw : ∑ b : Fin p, w b • e b = w := by
      simpa only [he, EuclideanSpace.basisFun_repr] using e.sum_repr w
    have hc : δ (fun i => e (J i)) = γ.curryLeft w (fun i => e (J i)) := hδ _
    rw [hc]
    conv_lhs => rw [← hw]
    rw [map_sum, ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  -- Cauchy–Schwarz in `b`.
  have hcs : ∀ J : Fin k → Fin p, δ (fun i => e (J i)) ^ 2 ≤
      ‖w‖ ^ 2 * ∑ b : Fin p, γ (fun i => e ((Fin.cons b J : Fin (k + 1) → Fin p) i)) ^ 2 := by
    intro J
    rw [hexp J, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- `(b, J) ↦ Fin.cons b J` enumerates all index maps `Fin (k + 1) → Fin p`.
  have hre : ∑ J : Fin k → Fin p, ∑ b : Fin p,
      γ (fun i => e ((Fin.cons b J : Fin (k + 1) → Fin p) i)) ^ 2 =
        ∑ I : Fin (k + 1) → Fin p, γ (fun i => e (I i)) ^ 2 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Fin p).sum_comp]
    rfl
  -- `k! |δ|² ≤ ‖w‖² (k+1)! |γ|²`.
  have hsum : (k.factorial : ℝ) * covectorEuclideanNorm δ ^ 2 ≤
      ‖w‖ ^ 2 * (((k + 1).factorial : ℝ) * covectorEuclideanNorm γ ^ 2) := by
    rw [← Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul p k δ,
      ← Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul p (k + 1) γ, ← hre, Finset.mul_sum]
    exact Finset.sum_le_sum fun J _ => hcs J
  -- Cancel `k! > 0`, using `(k+1)! = (k+1) k!`.
  have hsq : covectorEuclideanNorm δ ^ 2 ≤
      ((k : ℝ) + 1) * ‖w‖ ^ 2 * covectorEuclideanNorm γ ^ 2 := by
    have hpos : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    refine le_of_mul_le_mul_left ?_ hpos
    calc (k.factorial : ℝ) * covectorEuclideanNorm δ ^ 2
        ≤ ‖w‖ ^ 2 * (((k + 1).factorial : ℝ) * covectorEuclideanNorm γ ^ 2) := hsum
      _ = (k.factorial : ℝ) * (((k : ℝ) + 1) * ‖w‖ ^ 2 * covectorEuclideanNorm γ ^ 2) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
        ring
  -- Take nonnegative square roots.
  have hnn : 0 ≤ Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg w)) (covectorEuclideanNorm_nonneg γ)
  refine (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg δ) hnn two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  exact hsq

/-- Interior-product bound for the Euclidean coefficient norm: if
`β(v₁, …, v_k) = a γ(w, T v₁, …, T v_k)` for a `(k+1)`-covector `γ` on `ℝ^{m′}`, `w ∈ ℝ^{m′}` and
`T : ℝ^m → ℝ^{m′}`, then `|β| ≤ |a| √(k+1) ‖w‖ ‖T‖^k |γ|`.  With the contraction
`δ := γ(w, ·) = γ.curryLeft w` we have `β = a • T^#δ`, so homogeneity
`Submission.fiw_tb_ext_covectorNorm_smul`, the pull-back bound
`Submission.iwl_sp_covectorEuclideanNorm_pullback_le` and the contraction bound
`Submission.dph_sh_ib_covectorEuclideanNorm_contract_le` give
`|β| = |a| |T^#δ| ≤ |a| ‖T‖^k |δ| ≤ |a| ‖T‖^k √(k+1) ‖w‖ |γ|`. -/
theorem Submission.dph_sh_covectorEuclideanNorm_interior_le : ∀ (m m' k : ℕ) (γ : Covector (Eucl m') (k + 1)) (w : Eucl m') (T : Eucl m →L[ℝ] Eucl m') (a : ℝ) (β : Covector (Eucl m) k), (∀ v : Fin k → Eucl m, β v = a * γ (Fin.cons w (fun i => T (v i)))) → covectorEuclideanNorm β ≤ |a| * Real.sqrt ((k : ℝ) + 1) * ‖w‖ * ‖T‖ ^ k * covectorEuclideanNorm γ := by
  intro m m' k γ w T a β hβ
  -- The contraction `δ := γ(w, ·)`: `δ u = γ (Fin.cons w u)` holds by definition.
  have hδ := Submission.dph_sh_ib_covectorEuclideanNorm_contract_le m' k γ w (γ.curryLeft w)
    fun u => ContinuousAlternatingMap.curryLeft_apply_apply γ w u
  -- `β = a • T^#δ`: both sides send `v` to `a γ(w, T v₁, …, T v_k)`.
  have hβδ : β = a • (γ.curryLeft w).compContinuousLinearMap T :=
    ContinuousAlternatingMap.ext fun v => hβ v
  -- Homogeneity, then the pull-back bound for `T` and the contraction bound for `δ`.
  rw [hβδ, Submission.fiw_tb_ext_covectorNorm_smul]
  calc |a| * covectorEuclideanNorm ((γ.curryLeft w).compContinuousLinearMap T)
      ≤ |a| * (‖T‖ ^ k * covectorEuclideanNorm (γ.curryLeft w)) :=
        mul_le_mul_of_nonneg_left
          (Submission.iwl_sp_covectorEuclideanNorm_pullback_le m m' k T (γ.curryLeft w))
          (abs_nonneg a)
    _ ≤ |a| * (‖T‖ ^ k * (Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hδ (pow_nonneg (norm_nonneg T) k)) (abs_nonneg a)
    _ = |a| * Real.sqrt ((k : ℝ) + 1) * ‖w‖ * ‖T‖ ^ k * covectorEuclideanNorm γ := by ring

/-- Simon Ch. 6, 2.27 (p. 140), affine homotopy estimate: let `Z = [[0,1]] × X` (characterized
through `dt`-slices) and `G(t, x) = F₀(x) + t (F₁(x) - F₀(x))`, with `|F₁ - F₀| ≤ s` and
`|DF₀|, |DF₁| ≤ L` on an open `O ⊇ spt X`.  If `η'` equals `G^#ψ` near `[0,1] × spt X`, then
`|Z(η')| ≤ c s L^k B C` whenever `M(X) ≤ B` and `|ψ| ≤ C`, with `c = √(k+1)`. -/
theorem Submission.dph_sh_affine_estimate :
    ∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k)
      (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m')
      (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B →
      (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
        (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
          (φ s : DifferentialForm (Eucl m) k) x v =
            (η : DifferentialForm (Eucl (m + 1)) (k + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ →
      IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) →
      (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) →
      ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ)
        (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)),
        (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) →
        (∃ N : Set (Eucl (m + 1)), IsOpen N ∧
          {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
            (EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧
          ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x =
            ((ψ : DifferentialForm (Eucl m') (k + 1))
              ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                  (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
                  (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
                    F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))))
                x)).compContinuousLinearMap
              (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                  (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
                  (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
                    F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) →
        |Z η'| ≤ c * s * L ^ k * B * C := by
  intro m m' k
  refine ⟨Real.sqrt ((k : ℝ) + 1), Real.sqrt_nonneg _, ?_⟩
  intro X Z F₀ F₁ O s L B hs hL hB hXB hZ hF₀ hF₁ hO hXO hdist hDF₀ hDF₁ hprop ψ C η' hψC hη'
  obtain ⟨N', hN', hAN', hη'N'⟩ := hη'
  -- `spt X = ℝ^m \ zeroRegion X` is closed.
  have hXcl : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  -- 1. `G` is smooth, `DG(s₀, x) e₀ = F₁ x - F₀ x`, `DG(s₀, x) (0, v) = (1 - s₀) DF₀(x) v +
  -- s₀ DF₁(x) v`, and `G` is proper on the cylinder `cyl(spt X) = [0,1] × spt X`.
  obtain ⟨hG, hGd⟩ :=
    Submission.dph_sh_ae_affine_homotopy_contDiff_fderiv m m' F₀ F₁ hF₀ hF₁
  have hGprop := Submission.dph_sh_ae_affine_homotopy_isCompact_preimage_cyl m m' F₀ F₁
    X.support s hF₀.continuous hF₁.continuous hXcl (fun x hx => hdist x (hXO hx)) hprop
  set G : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
    F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
        (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
          F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))
  -- The tail projection `tl` is continuous, and `tl(s₀, x) = x`.
  have htail : Continuous (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) :=
    continuous_pi fun i => continuous_apply i.succ
  have htl : Continuous fun y : Eucl (m + 1) =>
      (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp
      (htail.comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).continuous)
  have htl_cons : ∀ (s₀ : ℝ) (x : Eucl m), (EuclideanSpace.equiv (Fin m) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))) = x := by
    intro s₀ x
    rw [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  -- 2. Cut-off: `η = ζ G^#ψ` with `0 ≤ ζ ≤ 1`, `η = G^#ψ` near `cyl(spt X)` and
  -- `spt η ⊆ tl⁻¹(O)`; it is also a test form `η₁` on all of `ℝ^{m+1}`.
  obtain ⟨η, ζ, N, hN, hAN, hζ, hη, hηN, -⟩ :=
    Submission.iwl_sp_exists_compatible_testForm (m + 1) m' (k + 1)
      ((fun y : Eucl (m + 1) => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) ⁻¹' O) univ
      {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
        (EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support}
      G (hO.preimage htl) (fun y hy => hXO hy.2) hG (fun K hK _ => hGprop K hK) ψ
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1),
      (η₁ : DifferentialForm (Eucl (m + 1)) (k + 1)) = η :=
    ⟨⟨η, η.2.1, subset_univ _⟩, rfl⟩
  -- 3. `Z(η') = Z(η₁)`: both forms equal `G^#ψ` on the open set `N' ∩ N ⊇ cyl(spt X)`.
  have hZη : Z η' = Z η₁ :=
    Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl m k X Z hZ η' η₁ (N' ∩ N) (hN'.inter hN)
      (subset_inter hAN' hAN) fun y hy => by rw [hη₁, hη'N' y hy.1, hηN y hy.2]
  -- 4. The `dt`-slices `φ` of `η₁`, and `Z(η₁) = ∫₀¹ X(φ(s₀)) ds₀`.
  obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm m k η₁
  have hZφ : Z η₁ = ∫ s₀ in (0 : ℝ)..1, X (φ s₀) := hZ η₁ φ fun s₀ _ x v => hφ s₀ x v
  have hC : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hψC 0)
  -- 5. Pointwise bound `|φ(s₀)(x)| ≤ √(k+1) s L^k C` for `s₀ ∈ [0,1]`.
  have hbound : ∀ s₀ ∈ Icc (0 : ℝ) 1, ∀ x, covectorEuclideanNorm
      ((φ s₀ : DifferentialForm (Eucl m) k) x) ≤ Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C := by
    intro s₀ hs₀ x
    have hφx := hφ s₀ x
    obtain ⟨hGe₀, hGι₀⟩ := hGd s₀ x
    have htl₀ := htl_cons s₀ x
    generalize (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x)) = y at hφx hGe₀ hGι₀ htl₀
    rw [hη₁] at hφx
    by_cases hx : x ∈ O
    · -- Over `O`: `φ(s₀)(x)(v) = ζ(y) ψ(G y)(F₁ x - F₀ x, T v₁, …, T v_k)`, where
      -- `T = (1 - s₀) DF₀(x) + s₀ DF₁(x)` has `‖T‖ ≤ L`.
      have hβ : ∀ v : Fin k → Eucl m, (φ s₀ : DifferentialForm (Eucl m) k) x v =
          ζ y * (ψ : DifferentialForm (Eucl m') (k + 1)) (G y) (Fin.cons (F₁ x - F₀ x)
            fun i => ((1 - s₀) • fderiv ℝ F₀ x + s₀ • fderiv ℝ F₁ x) (v i)) := by
        intro v
        rw [hφx, hη y, ContinuousAlternatingMap.smul_apply,
          ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul, Fin.comp_cons,
          hGe₀]
        congr 3
        funext i
        exact hGι₀ (v i)
      have hT : ‖(1 - s₀) • fderiv ℝ F₀ x + s₀ • fderiv ℝ F₁ x‖ ≤ L := by
        calc _ ≤ ‖(1 - s₀) • fderiv ℝ F₀ x‖ + ‖s₀ • fderiv ℝ F₁ x‖ := norm_add_le _ _
          _ = (1 - s₀) * ‖fderiv ℝ F₀ x‖ + s₀ * ‖fderiv ℝ F₁ x‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hs₀.2),
              Real.norm_of_nonneg hs₀.1]
          _ ≤ (1 - s₀) * L + s₀ * L :=
            add_le_add (mul_le_mul_of_nonneg_left (hDF₀ x hx) (sub_nonneg.2 hs₀.2))
              (mul_le_mul_of_nonneg_left (hDF₁ x hx) hs₀.1)
          _ = L := by ring
      have hw : ‖F₁ x - F₀ x‖ ≤ s := by
        rw [← dist_eq_norm]
        exact hdist x hx
      have hζy : |ζ y| ≤ 1 := by
        rw [abs_of_nonneg (hζ y).1]
        exact (hζ y).2
      have hψy := covectorEuclideanNorm_nonneg ((ψ : DifferentialForm (Eucl m') (k + 1)) (G y))
      calc covectorEuclideanNorm ((φ s₀ : DifferentialForm (Eucl m) k) x)
          ≤ |ζ y| * Real.sqrt ((k : ℝ) + 1) * ‖F₁ x - F₀ x‖ *
              ‖(1 - s₀) • fderiv ℝ F₀ x + s₀ • fderiv ℝ F₁ x‖ ^ k *
              covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) (G y)) :=
            Submission.dph_sh_covectorEuclideanNorm_interior_le m m' k _ _ _ _ _ hβ
        _ ≤ 1 * Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C := by
            gcongr
            exact hψC (G y)
        _ = Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C := by ring
    · -- Off `O`: `y ∉ tl⁻¹(O) ⊇ spt η`, so `φ(s₀)(x) = 0`.
      have hy : y ∉ tsupport (η : DifferentialForm (Eucl (m + 1)) (k + 1)) := by
        intro hy
        have hyO : (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ O := η.2.2 hy
        rw [htl₀] at hyO
        exact hx hyO
      have h0 : (φ s₀ : DifferentialForm (Eucl m) k) x = 0 := by
        ext v
        simp only [hφx, image_eq_zero_of_notMem_tsupport hy, ContinuousAlternatingMap.coe_zero,
          Pi.zero_apply]
      rw [h0, covectorEuclideanNorm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs) (pow_nonneg hL k)) hC
  -- 6. Mass bound for each slice, then the interval-integral bound.
  have hint : ‖∫ s₀ in (0 : ℝ)..1, X (φ s₀)‖ ≤
      B * (Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s₀ hs₀ => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs₀
    rw [Real.norm_eq_abs]
    exact Submission.cmb_abs_apply_le_of_massOn_le m k univ univ X (φ s₀) B _ hB hXB
      (subset_univ _) (hbound s₀ (Ioc_subset_Icc_self hs₀))
  rw [hZη, hZφ, ← Real.norm_eq_abs]
  calc _ ≤ _ := hint
    _ = Real.sqrt ((k : ℝ) + 1) * s * L ^ k * B * C := by
      rw [sub_zero, abs_one, mul_one]
/-- Supports of boundaries, weak limits and linear combinations: `spt ∂Z ⊆ spt Z`; a weak limit of
currents supported in a closed `K` is supported in `K`; `spt Z ⊆ spt Z₁ ∪ spt Z₂` when
`Z = a Z₁ + b Z₂`.  In each case a point outside the claimed support lies in an open `W ⊂⊂ U` on
which the current vanishes, i.e. in its zero region. -/
theorem Submission.iwl_cr_support_lemmas :
    (∀ (P m : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (m + 1)),
      Z.boundary.support ⊆ Z.support) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P))
      (Zj : ℕ → GeometricCurrentOn U n) (Z : GeometricCurrentOn U n), IsClosed K →
      (∀ j, (Zj j).support ⊆ K) → WeaklyConvergesOn Zj Z → Z.support ⊆ K) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Z₁ Z₂ Z : GeometricCurrentOn U n) (a b : ℝ),
      (∀ ω : TestFormOn U n, Z ω = a * Z₁ ω + b * Z₂ ω) →
      Z.support ⊆ Z₁.support ∪ Z₂.support) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) If `Z` vanishes on an admissible `W`, so does `∂Z`: `∂Z φ = Z (dφ)` and
    -- `tsupport dφ ⊆ tsupport φ ⊆ W`.
    intro P m U Z x hx
    refine ⟨hx.1, fun hxZ => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
    refine Set.mem_sUnion.2 ⟨W, ⟨hWo, hWc, hWU, fun φ hφ => ?_⟩, hxW⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hφ)
  · -- (2) For `x ∈ spt Z \ K`, the ball `W = B(x, ε/2)` has `closure W ⊆ U \ K`.  A test form
    -- supported in `W` misses `K ⊇ spt (Zj j)`, so every `Zj j` kills it, and so does the limit.
    intro P n U hU K Zj Z hK hZj hconv x hx
    by_contra hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.sdiff hK) x ⟨hx.1, hxK⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ U \ K := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans sdiff_subset, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have h0 : ∀ j, Zj j ω = 0 := fun j =>
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U (Zj j) ω
          (Set.disjoint_left.2 fun y hy hyS => (hcl (subset_closure (hω hy))).2 (hZj j hyS))
      have hlim := hconv ω
      simp only [h0] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- (3) For `x ∈ spt Z` outside `spt Z₁ ∪ spt Z₂`, the ball `W = B(x, ε/2)` has `closure W`
    -- inside both zero regions and `U`, so `Z₁`, `Z₂` and hence `Z = a Z₁ + b Z₂` vanish on `W`.
    intro P n U hU Z₁ Z₂ Z a b hZ x hx
    by_contra hx12
    have h1 : x ∈ Z₁.zeroRegion := by
      by_contra h
      exact hx12 (Or.inl ⟨hx.1, h⟩)
    have h2 : x ∈ Z₂.zeroRegion := by
      by_contra h
      exact hx12 (Or.inr ⟨hx.1, h⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((Z₁.isOpen_zeroRegion.inter Z₂.isOpen_zeroRegion).inter hU) x ⟨⟨h1, h2⟩, hx.1⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ Z₁.zeroRegion ∩ Z₂.zeroRegion ∩ U := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans inter_subset_right, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have e1 : Z₁ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₁ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.1)
      have e2 : Z₂ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₂ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.2)
      rw [hZ ω, e1, e2]
      ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
