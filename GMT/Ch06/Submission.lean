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

/-- Simon Ch. 6, 4.11 (Leibniz rule, pointwise): `d(ψω)(x) = ψ(x) dω(x) + Dψ(x) ∧ ω(x)`, the
wedge `Dψ(x) ∧ ω(x)` being the alternatization of `h ↦ Dψ(x)(h) ω(x)`.  As `d = Alt ∘ D`
(Mathlib's `extDeriv`), this is the product rule `D(ψω)(x) = ψ(x) Dω(x) + Dψ(x) ⊗ ω(x)`
followed by linearity of `alternatizeUncurryFin`. -/
theorem Submission.slicing_mb_lb_extDeriv_smul :
    ∀ (P m : ℕ) (ψ : Eucl P → ℝ) (ω : DifferentialForm (Eucl P) m) (x : Eucl P), DifferentiableAt ℝ ψ x → DifferentiableAt ℝ ω x → exteriorDerivative (fun y => ψ y • ω y : DifferentialForm (Eucl P) m) x = ψ x • exteriorDerivative ω x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight (ω x)) := by
  intro P m ψ ω x hψ hω
  simp only [exteriorDerivative, extDeriv]
  rw [fderiv_fun_smul hψ hω, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- Multiplication by a smooth function `ψ` maps `𝒟ᵏ(U)` into itself: `ψ φ` is smooth, and
`spt (ψ φ) ⊆ spt φ`, which is compact and contained in `U`. -/
theorem Submission.slicing_mb_lb_smul_testForm :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (φ : TestFormOn U k) (ψ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ η : TestFormOn U k, ∀ x, (η : DifferentialForm (Eucl P) k) x =
        ψ x • (φ : DifferentialForm (Eucl P) k) x := by
  intro P k U φ ψ hψ
  obtain ⟨⟨hφ, hφc⟩, hφU⟩ := φ.2
  exact ⟨⟨ψ • (φ : DifferentialForm (Eucl P) k), ⟨hψ.smul hφ, hφc.smul_left⟩,
    (tsupport_smul_subset_right ψ _).trans hφU⟩, fun _ => rfl⟩
/-- The wedge `α ∧ ω` of a `C^∞` field `α` of covectors with a test form `ω ∈ 𝒟ᵐ(U)` is a test
form in `𝒟ᵐ⁺¹(U)`, given pointwise by `alternatizeUncurryFin ((α x).smulRight (ω x))`. -/
theorem Submission.slicing_mb_lb_wedge_testForm :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U m) (α : Eucl P → (Eucl P →L[ℝ] ℝ)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α →
      ∃ η : TestFormOn U (m + 1), ∀ x, (η : DifferentialForm (Eucl P) (m + 1)) x =
        ContinuousAlternatingMap.alternatizeUncurryFin
          ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by
  intro P m U ω α hα
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  -- `η` vanishes wherever `ω` does: `(α x).smulRight 0 = 0` and `alternatizeUncurryFin` is linear.
  have hsupp : Function.support (fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ⊆
      Function.support (ω : DifferentialForm (Eucl P) m) := by
    intro x hx h0
    apply hx
    simp only [h0, ContinuousLinearMap.smulRight_zero]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
  -- Hence `η` has compact support and `tsupport η ⊆ tsupport ω ⊆ U`; the formula holds by `rfl`.
  refine ⟨⟨fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)),
    ⟨?_, hωc.mono hsupp⟩, (closure_mono hsupp).trans hωU⟩, fun x => rfl⟩
  -- Smoothness: `x ↦ (α x).smulRight (ω x)` is `C^∞` (bounded bilinear in `(α x, ω x)`), and
  -- `alternatizeUncurryFin` is the continuous linear map `alternatizeUncurryFinCLM`.
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).contDiff.comp
    (hα.smulRight hωs)
/-- Global smooth approximation of a Lipschitz function by mollification: `g k = ρ_k ⋆ h` with a
normalized smooth bump `ρ_k ≥ 0`, `∫ ρ_k = 1`, supported in `B(0, 1/(k+1))`.  Each `g k` is `C^∞`,
`L`-Lipschitz, and `|g k - h| ≤ L/(k+1)` uniformly. -/
theorem Submission.slicing_im_ll_mollify :
    ∀ (P : ℕ) (h : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L h → ∃ g : ℕ → Eucl P → ℝ,
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g k)) ∧ (∀ k, LipschitzWith L (g k)) ∧
        TendstoUniformly g h atTop := by
  intro P h L hL
  -- Step 1: normalized smooth bumps `ρ k ≥ 0` with `∫ ρ k = 1`, supported in `B(0, 1/(k+1))`.
  have hbump : ∀ k : ℕ, ∃ ρ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧
      Function.support ρ ⊆ ball (0 : Eucl P) (1 / ((k : ℝ) + 1)) ∧ ∫ y, ρ y = 1 := by
    intro k
    have hσ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    let φ : ContDiffBump (0 : Eucl P) :=
      ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), half_pos hσ, half_lt_self hσ⟩
    have hint : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hpos : 0 < ∫ y, φ y := by
      refine (integral_pos_iff_support_of_nonneg φ.nonneg' hint).mpr ?_
      rw [φ.support_eq]
      exact measure_ball_pos _ _ hσ
    have hsupp : Function.support (fun y => φ y / ∫ y, φ y) ⊆ Function.support φ :=
      fun y hy h0 => hy (by simp [h0])
    refine ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
      fun y => div_nonneg φ.nonneg hpos.le, φ.support_eq ▸ hsupp, ?_⟩
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    exact mul_inv_cancel₀ hpos.ne'
  choose ρ hρs hρc hρn hρsupp hρi using hbump
  have hρint : ∀ k, Integrable (ρ k) := fun k => integrable_of_integral_eq_one (hρi k)
  -- Step 2: `g k = ρ k ⋆ h`; the convolution exists everywhere.
  have hex : ∀ k, ConvolutionExists (ρ k) h (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun k =>
    (hρc k).convolutionExists_left _ (hρs k).continuous hL.continuous.locallyIntegrable
  refine ⟨fun k => convolution (ρ k) h (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_⟩
  -- Step 3: smoothness.
  · intro k
    exact (hρc k).contDiff_convolution_left _ (hρs k) hL.continuous.locallyIntegrable
  -- Step 4: the Lipschitz constant is preserved.
  · intro k
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hx := (hex k x).integrable
    have hx' := (hex k x').integrable
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at hx hx' ⊢
    rw [dist_eq_norm, ← integral_sub hx hx']
    refine (norm_integral_le_of_norm_le ((hρint k).mul_const ((L : ℝ) * dist x x'))
      (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hρn k t), ← dist_eq_norm]
      gcongr
      · exact hρn k t
      · calc dist (h (x - t)) (h (x' - t)) ≤ L * dist (x - t) (x' - t) := hL.dist_le_mul _ _
          _ = L * dist x x' := by rw [dist_sub_right]
    · rw [integral_mul_const, hρi k, one_mul]
  -- Steps 5–6: `|g k - h| ≤ L/(k+1)` everywhere, hence uniform convergence.
  · have hbound : ∀ k x, dist (convolution (ρ k) h (ContinuousLinearMap.lsmul ℝ ℝ) volume x) (h x)
        ≤ L * (1 / ((k : ℝ) + 1)) := by
      intro k x
      refine dist_convolution_le (by positivity) (hρsupp k) (hρn k) (hρi k)
        hL.continuous.aestronglyMeasurable fun y hy => ?_
      calc dist (h y) (h x) ≤ L * dist y x := hL.dist_le_mul _ _
        _ ≤ L * (1 / ((k : ℝ) + 1)) := by
          gcongr
          exact (mem_ball.mp hy).le
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hlim : Tendsto (fun k : ℕ => (L : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (L : ℝ)
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk x
    rw [dist_comm]
    exact (hbound k x).trans_lt hk
/-- Continuous multipliers `g k → f` converging uniformly on `ℝ^P`, integrated against a
`ν`-integrable density `F` vanishing off a compact set `K`: `∫ g k F dν → ∫ f F dν`. -/
theorem Submission.slicing_im_ll_multiplier_tendsto :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) (F : Eucl P → ℝ) (K : Set (Eucl P)) (f : Eucl P → ℝ)
      (g : ℕ → Eucl P → ℝ), Integrable F ν → IsCompact K → (∀ x, x ∉ K → F x = 0) →
      Continuous f → (∀ k, Continuous (g k)) → TendstoUniformly g f atTop →
      Tendsto (fun k => ∫ x, g k x * F x ∂ν) atTop (𝓝 (∫ x, f x * F x ∂ν)) := by
  intro P ν F K f g hF hK hFK hf hg hgf
  -- A continuous `φ` is bounded by some `B` on `K` and `F` vanishes off `K`, so
  -- `|φ F| ≤ B |F|` everywhere and `φ F` is integrable.
  have hint : ∀ φ : Eucl P → ℝ, Continuous φ → Integrable (fun x => φ x * F x) ν := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
    refine (hF.norm.const_mul B).mono' (hφ.aestronglyMeasurable.mul hF.aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    by_cases hx : x ∈ K
    · exact mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _)
    · simp [hFK x hx]
  -- With `I = ∫ |F| dν`, once `|g k - f| < ε / (I + 1)` everywhere,
  -- `|∫ g k F - ∫ f F| ≤ ∫ |g k - f| |F| ≤ ε I / (I + 1) < ε`.
  set I := ∫ x, ‖F x‖ ∂ν
  have hI : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hgf _ hδ)
  refine ⟨k₀, fun k hk => ?_⟩
  rw [dist_eq_norm, ← integral_sub (hint _ (hg k)) (hint _ hf)]
  calc ‖∫ x, (g k x * F x - f x * F x) ∂ν‖ ≤ ∫ x, ε / (I + 1) * ‖F x‖ ∂ν := by
        refine norm_integral_le_of_norm_le (hF.norm.const_mul _) (ae_of_all _ fun x => ?_)
        rw [← sub_mul, norm_mul, ← dist_eq_norm, dist_comm]
        exact mul_le_mul_of_nonneg_right (hk₀ k hk x).le (norm_nonneg _)
    _ = ε / (I + 1) * I := integral_const_mul _ _
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Simon Ch. 6, proof of 4.5(2), (2), for a `C^∞` multiplier `ψ`: the Leibniz rule
`∂T(ψ ω) = T(ψ dω) + T(Dψ ∧ ω)`, with `∂T` and `T` evaluated through their measure
representations and `T(Dψ ∧ ω) = τ(M, θ, ξ)(Dψ ∧ ω)`. -/
theorem Submission.slicing_im_ll_smooth_leibniz :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ η : TestFormOn U (m + 1), T η = tauAction (m + 1) M θ ξ η) → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)) (μ' : Measure (Eucl P)) (v' : Eucl P → NVector (Eucl P) m), IsMeasureRepresentation T μ v → IsMeasureRepresentation T.boundary μ' v' → ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ∂(μHE[m + 1] : Measure (Eucl P)) = (∫ x, ψ x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') - (∫ x, ψ x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ) := by
  intro P m U M θ ξ T hT μ v μ' v' hv hv' ω ψ hψ
  -- The test forms `η₁ = ψ ω ∈ 𝒟ᵐ(U)`, `η₂ = ψ dω ∈ 𝒟ᵐ⁺¹(U)` and `η₃ = Dψ ∧ ω ∈ 𝒟ᵐ⁺¹(U)`.
  have hdω : ((exteriorDerivativeTestOn U m ω : TestFormOn U (m + 1)) :
      DifferentialForm (Eucl P) (m + 1)) = exteriorDerivative (ω : DifferentialForm (Eucl P) m) :=
    rfl
  obtain ⟨η₁, hη₁⟩ := Submission.slicing_mb_lb_smul_testForm P m U ω ψ hψ
  obtain ⟨η₂, hη₂⟩ :=
    Submission.slicing_mb_lb_smul_testForm P (m + 1) U (exteriorDerivativeTestOn U m ω) ψ hψ
  obtain ⟨η₃, hη₃⟩ :=
    Submission.slicing_mb_lb_wedge_testForm P m U ω (fderiv ℝ ψ) (hψ.fderiv_right (by simp))
  -- Leibniz rule `d(ψ ω) = ψ dω + Dψ ∧ ω`: the exterior derivative of `η₁` is `η₂ + η₃`.
  have hd : exteriorDerivativeTestOn U m η₁ = η₂ + η₃ := by
    have hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) m) := ω.2.1.1
    have h₁ : (η₁ : DifferentialForm (Eucl P) m) =
        fun y => ψ y • (ω : DifferentialForm (Eucl P) m) y := funext hη₁
    apply Subtype.ext
    funext x
    change exteriorDerivative (η₁ : DifferentialForm (Eucl P) m) x =
      (η₂ : DifferentialForm (Eucl P) (m + 1)) x + (η₃ : DifferentialForm (Eucl P) (m + 1)) x
    rw [h₁, hη₂, hη₃, hdω, Submission.slicing_mb_lb_extDeriv_smul P m ψ _ x
      (hψ.differentiable (by simp) x) (hω.differentiable (by simp) x)]
  -- Hence `∂T(η₁) = T(dη₁) = T(η₂) + T(η₃)`.
  have hb : T.boundary η₁ = T η₂ + T η₃ := by
    rw [GeometricCurrentOn.boundary_apply, hd]
    exact map_add T.toCurrent η₂ η₃
  -- `∂T(η₁)` and `T(η₂)` through the measure representations, `T(η₃)` through `τ(M, θ, ξ)`.
  have h₁ : T.boundary η₁ = ∫ x, ψ x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ' := by
    simp only [(hv' η₁).2, hη₁, map_smul, smul_eq_mul]
  have h₂ : T η₂ =
      ∫ x, ψ x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ := by
    simp only [(hv η₂).2, hη₂, hdω, map_smul, smul_eq_mul]
  have h₃ : T η₃ = ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin
      ((fderiv ℝ ψ x).smulRight ((ω : DifferentialForm (Eucl P) m) x)))
      ∂(μHE[m + 1] : Measure (Eucl P)) := by
    simp only [hT η₃, tauAction, hη₃]
  rw [← h₁, ← h₂, ← h₃, hb]
  ring
/-- The tangent vector field dual to `θ ⟨· ∧ ω, ξ⟩` (Simon Ch. 6, proof of Lemma 4.5(2),
(1)–(3)): for a rectifiable triple `(M, θ, ξ)` of dimension `n = m + 1` and `ω ∈ 𝒟ᵐ(U)` there is
`Y : ℝ^P → ℝ^P` with `φ(Y(x)) = θ(x) ⟨φ ∧ ω(x), ξ(x)⟩` for all `x` and all functionals `φ`,
`Y ∈ L¹(Hⁿ ⌞ M)`, and `Y(x)` lies in every weighted approximate tangent plane at `Hⁿ`-a.e.
`x ∈ M`.  Take the Riesz representative `Y(x) = ∑ᵢ θ(x) ⟨eᵢ♭ ∧ ω(x), ξ(x)⟩ eᵢ`.  A.e. on `M`,
`ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|ξ(x)(β)| ≤ ‖β‖` and `|Y| ≤ C |θ| 1_{spt ω}`;
and for `w ⊥ span τ`, `(w♭ ∧ ω(x))(τ) = ∑ᵢ (-1)ⁱ ⟨w, τᵢ⟩ ω(x)(τ without τᵢ) = 0`, so
`Y(x) ∈ (span τ)ᗮᗮ = span τ`, the unique weighted tangent plane (`θ(x) > 0`). -/
theorem Submission.slicing_im_ll_tangent_dual_field :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)),
      IsRectifiableTriple U (m + 1) M θ ξ → ∀ ω : TestFormOn U m,
      ∃ Y : Eucl P → Eucl P, Integrable Y ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧
        (∀ (x : Eucl P) (φ : Eucl P →L[ℝ] ℝ), φ (Y x) = θ x * ξ x
          (ContinuousAlternatingMap.alternatizeUncurryFin
            (φ.smulRight ((ω : DifferentialForm (Eucl P) m) x)))) ∧
        ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
          HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → Y x ∈ Q := by
  intro P m U M θ ξ hT ω
  set f : DifferentialForm (Eucl P) m := (ω : DifferentialForm (Eucl P) m)
  -- `Λ x φ = θ(x) ⟨φ ∧ ω(x), ξ(x)⟩` is a continuous linear functional of `φ`.
  let Λ : Eucl P → (Eucl P →L[ℝ] ℝ) →L[ℝ] ℝ := fun x =>
    θ x • (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
      ((ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)).flip (f x)))
  have hΛ : ∀ x φ, Λ x φ = θ x * ξ x
      (ContinuousAlternatingMap.alternatizeUncurryFin (φ.smulRight (f x))) := fun x φ => rfl
  -- `Y(x) = ∑ᵢ Λ x (eᵢ♭) eᵢ`; every functional is `φ = ∑ᵢ φ(eᵢ) eᵢ♭`, so `φ(Y(x)) = Λ x φ`.
  let b := EuclideanSpace.basisFun (Fin P) ℝ
  let Y : Eucl P → Eucl P := fun x => ∑ i, Λ x (innerSL ℝ (b i)) • b i
  have hdual : ∀ φ : Eucl P →L[ℝ] ℝ, ∑ i, φ (b i) • innerSL ℝ (b i) = φ := by
    intro φ
    ext y
    conv_rhs => rw [← b.sum_repr' y]
    simp [map_sum, map_smul, mul_comm]
  have hY : ∀ x (φ : Eucl P →L[ℝ] ℝ), φ (Y x) = Λ x φ := by
    intro x φ
    conv_rhs => rw [← hdual φ]
    simp [Y, map_sum, map_smul, mul_comm]
  refine ⟨Y, ?_, fun x φ => (hY x φ).trans (hΛ x φ), ?_⟩
  · -- Integrability: each coordinate `x ↦ Λ x (eᵢ♭)` is integrable.
    have hω : IsTestForm f ∧ tsupport f ⊆ U := ω.2
    have hfc : Continuous f := ContDiff.continuous hω.1.1
    have hθK : IntegrableOn θ (tsupport f ∩ M) (μHE[m + 1] : Measure (Eucl P)) := by
      rw [inter_comm]
      exact hT.integrableOn _ hω.1.2 hω.2
    -- A.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|ξ(x)(β)| ≤ ‖β‖`.
    have hξb : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
        ∀ β : Covector (Eucl P) (m + 1), ‖ξ x β‖ ≤ ‖β‖ := by
      filter_upwards [hT.orients] with x hx β
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      have h1 : ‖β τ‖ ≤ ‖β‖ := by
        simpa [hτ.1] using β.le_opNorm τ
      rcases hξ with h | h <;> simpa [h] using h1
    refine integrable_finsetSum _ fun i _ => Integrable.smul_const ?_ (b i)
    -- `βᵢ(x) = eᵢ♭ ∧ ω(x)` is continuous with compact support, hence bounded.
    let β : Eucl P → Covector (Eucl P) (m + 1) := fun x =>
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (b i)))) (f x)
    have hβc : Continuous β := (ContinuousLinearMap.continuous _).comp hfc
    have hβs : HasCompactSupport β := hω.1.2.comp_left (map_zero _)
    obtain ⟨C, hC⟩ := hβc.bounded_above_of_compact_support hβs
    have hΛβ : ∀ x, Λ x (innerSL ℝ (b i)) = θ x * ξ x (β x) := fun x => rfl
    -- The coordinate vanishes off `spt ω`, where `θ` is integrable.
    have hsupp : Function.support (fun x => Λ x (innerSL ℝ (b i))) ⊆ tsupport f := by
      intro x hx
      by_contra hxK
      have h0 : β x = 0 := by
        dsimp only [β]
        rw [image_eq_zero_of_notMem_tsupport hxK, map_zero]
      have h1 : Λ x (innerSL ℝ (b i)) = 0 := by
        rw [hΛβ, h0, map_zero, mul_zero]
      exact hx h1
    rw [← integrableOn_iff_integrable_of_support_subset hsupp, IntegrableOn,
      Measure.restrict_restrict (isClosed_tsupport f).measurableSet]
    have hmono : (μHE[m + 1] : Measure (Eucl P)).restrict (tsupport f ∩ M) ≤
        (μHE[m + 1] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono inter_subset_right le_rfl
    have hg : AEStronglyMeasurable (fun x => ξ x (β x))
        ((μHE[m + 1] : Measure (Eucl P)).restrict M) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hT.aestronglyMeasurable.prodMk hβc.aestronglyMeasurable)
    simp only [hΛβ]
    refine hθK.mul_bdd (hg.mono_measure hmono) (c := C) ?_
    filter_upwards [ae_mono hmono hξb] with x hx
    exact (hx (β x)).trans (hC x)
  · -- Tangency: `⟨u, Y(x)⟩ = θ(x) ⟨u♭ ∧ ω(x), ±τ⟩ = 0` for `u ⊥ span τ`.
    filter_upwards [hT.orients, ae_restrict_mem₀ hT.nullMeasurableSet] with x hx hxM
    obtain ⟨τ, -, hW, hξ⟩ := hx
    intro Q hQ
    rw [HasWeightedApproximateTangentSpaceAt.unique (hT.pos x hxM).ne' hQ hW,
      ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ)), Submodule.mem_orthogonal]
    intro u hu
    have hτu : ∀ i, inner ℝ u (τ i) = 0 := fun i =>
      Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (mem_range_self i)) hu
    rw [← innerSL_apply_apply, hY, hΛ]
    rcases hξ with h | h <;>
      simp [h, ContinuousAlternatingMap.alternatizeUncurryFin_apply, hτu]
/-- **Lipschitz bound, in the field, for the pairing `∫_Ω Df(b)`.**  If `f` is `C`-Lipschitz on
the open set `Ω ⊆ ℝⁿ` and `b, b'` are integrable on `Ω`, then
`|∫_Ω Df(b) − ∫_Ω Df(b')| ≤ C ∫_Ω |b − b'|`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not
differentiable).  On `Ω` we have `‖Df(w)‖ ≤ C`, so `w ↦ Df(w)(v(w))` is dominated by `C |v|`; it
is a.e. strongly measurable because `Df` is Borel, hence integrable for `v = b, b'`, and the
estimate follows by linearity of the integral and of `Df(w)`. -/
theorem Submission.slicing_im_ll_gws_pairing_bound :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (f : Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C f Ω →
      ∀ b b' : Eucl n → Eucl n, IntegrableOn b Ω (volume : Measure (Eucl n)) →
        IntegrableOn b' Ω (volume : Measure (Eucl n)) →
        |(∫ w in Ω, fderiv ℝ f w (b w)) - ∫ w in Ω, fderiv ℝ f w (b' w)| ≤
          C * ∫ w in Ω, ‖b w - b' w‖ := by
  intro n Ω C f hΩ hf b b' hb hb'
  -- `Ω` is a neighbourhood of each of its points, so `‖Df(w)‖ ≤ C` on `Ω`.
  have hD : ∀ w ∈ Ω, ‖fderiv ℝ f w‖ ≤ C := fun w hw =>
    norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hf
  -- Hence `|Df(w)(v(w))| ≤ C |v(w)|` for a.e. `w ∈ Ω`, for every field `v`.
  have hle : ∀ v : Eucl n → Eucl n,
      ∀ᵐ w ∂(volume : Measure (Eucl n)).restrict Ω, ‖fderiv ℝ f w (v w)‖ ≤ C * ‖v w‖ := by
    intro v
    refine (ae_restrict_iff' hΩ.measurableSet).2 (Eventually.of_forall fun w hw => ?_)
    exact (fderiv ℝ f w).le_of_opNorm_le (hD w hw) (v w)
  -- `w ↦ Df(w)(v(w))` is integrable on `Ω` when `v` is: it is a.e. strongly measurable
  -- (`Df` is Borel) and dominated by `C |v|`.
  have hint : ∀ v : Eucl n → Eucl n, IntegrableOn v Ω volume →
      IntegrableOn (fun w => fderiv ℝ f w (v w)) Ω volume := fun v hv =>
    (hv.norm.const_mul C).mono' ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
      hv.aestronglyMeasurable (measurable_fderiv ℝ f).aestronglyMeasurable) (hle v)
  -- Combine the integrals by linearity, then estimate.
  rw [← integral_sub (hint b hb) (hint b' hb')]
  simp_rw [← map_sub]
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((hb.sub hb').norm.const_mul C) (hle (b - b'))
/-- **Integration by parts against a `C¹` field, for functions Lipschitz on `Ω`.**  Let `Ω ⊆ ℝⁿ`
be open and `b : ℝⁿ → ℝⁿ` be `C¹` with compact support and `tsupport b ⊆ Ω`.  The divergence
`g = ∑ᵢ Dbᵢ(·)(eᵢ)` of `b` is integrable, and for every `f` that is `L`-Lipschitz on `Ω`, `f g` is
integrable on `Ω` and `∫_Ω Df(b) = −∫_Ω f g`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not
differentiable).  Extend `f` to an `L`-Lipschitz `F` on `ℝⁿ` (McShane); `DF = Df` on the open set
`Ω` and `b, g` vanish off `Ω`, so both sides are integrals over `ℝⁿ` with `F` in place of `f`.
Expand `b = ∑ᵢ bᵢ eᵢ`: by Rademacher's theorem `DF(w)(eᵢ)` is the line derivative of `F` along
`eᵢ` for a.e. `w`, and integration by parts for Lipschitz functions moves it onto the compactly
supported Lipschitz coordinate `bᵢ`. -/
theorem Submission.slicing_im_ll_gws_lipschitz_ibp :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (b : Eucl n → Eucl n), IsOpen Ω → ContDiff ℝ 1 b →
      HasCompactSupport b → tsupport b ⊆ Ω → ∃ g : Eucl n → ℝ,
        Integrable g (volume : Measure (Eucl n)) ∧
        ∀ (L : ℝ≥0) (f : Eucl n → ℝ), LipschitzOnWith L f Ω →
          IntegrableOn (fun w => f w * g w) Ω (volume : Measure (Eucl n)) ∧
          ∫ w in Ω, fderiv ℝ f w (b w) = -∫ w in Ω, f w * g w := by
  intro n Ω b hΩ hb hbc hbΩ
  classical
  -- Coordinates `bᵢ` of `b`: `C¹` with compact support, hence Lipschitz; `Dbᵢ = 0` off
  -- `tsupport b`.
  let e : Fin n → Eucl n := fun i => EuclideanSpace.single i 1
  let bi : Fin n → Eucl n → ℝ := fun i x => EuclideanSpace.proj i (b x)
  have hbi_cd : ∀ i, ContDiff ℝ 1 (bi i) := fun i =>
    (EuclideanSpace.proj i : StrongDual ℝ (Eucl n)).contDiff.comp hb
  have hbi_cs : ∀ i, HasCompactSupport (bi i) := fun i =>
    hbc.comp_left (g := fun y => EuclideanSpace.proj i y) (map_zero _)
  have hbi_ts : ∀ i, tsupport (bi i) ⊆ tsupport b := fun i =>
    tsupport_comp_subset (g := fun y => EuclideanSpace.proj i y) (map_zero _) b
  have hbi_lip : ∀ i, ∃ D, LipschitzWith D (bi i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hbi_cs i) (hbi_cd i) one_ne_zero
  have hbi_diff : ∀ i, Differentiable ℝ (bi i) := fun i => (hbi_cd i).differentiable one_ne_zero
  have hbi_cfd : ∀ i, Continuous (fderiv ℝ (bi i)) := fun i =>
    (hbi_cd i).continuous_fderiv one_ne_zero
  have hDbi_zero : ∀ i w, w ∉ tsupport b → fderiv ℝ (bi i) w = 0 := fun i w hw =>
    image_eq_zero_of_notMem_tsupport fun h => hw (hbi_ts i (tsupport_fderiv_subset ℝ h))
  -- The divergence `g = ∑ᵢ Dbᵢ(·)(eᵢ)` is continuous and vanishes off `tsupport b`, so it has
  -- compact support and is integrable.  It does not depend on `L` or `f`.
  let g : Eucl n → ℝ := fun w => ∑ i, fderiv ℝ (bi i) w (e i)
  have hg_cont : Continuous g :=
    continuous_finsetSum _ fun i _ => (hbi_cfd i).clm_apply continuous_const
  have hg_zero : ∀ w, w ∉ tsupport b → g w = 0 := fun w hw =>
    Finset.sum_eq_zero fun i _ => by simp [hDbi_zero i w hw]
  have hg_cs : HasCompactSupport g := HasCompactSupport.intro hbc hg_zero
  refine ⟨g, hg_cont.integrable_of_hasCompactSupport hg_cs, fun L f hf => ?_⟩
  -- McShane: `F` is `L`-Lipschitz on `ℝⁿ` and `F = f` on `Ω`, so `DF = Df` on the open set `Ω`.
  obtain ⟨F, hF, hfF⟩ := hf.extend_real
  have hDf : ∀ w ∈ Ω, fderiv ℝ f w = fderiv ℝ F w := fun w hw =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hw) hfF)
  -- (a): `F g` is continuous with compact support, and `f g = F g` on `Ω`.
  have hFg_int : Integrable (fun w => F w * g w) volume :=
    (hF.continuous.mul hg_cont).integrable_of_hasCompactSupport (hg_cs.mul_left (f := F))
  refine ⟨hFg_int.integrableOn.congr_fun (fun w hw => by simp [hfF hw]) hΩ.measurableSet, ?_⟩
  -- (b) reduces to `∫ DF(b) = −∫ F g` over `ℝⁿ`, as `b` and `g` vanish off `Ω`.
  have h1 : ∫ w in Ω, fderiv ℝ f w (b w) = ∫ w, fderiv ℝ F w (b w) := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun w => fderiv ℝ F w (b w))
      (fun w hw => by simp only [hDf w hw])]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
    simp [image_eq_zero_of_notMem_tsupport fun h => hw (hbΩ h)]
  have h2 : ∫ w in Ω, f w * g w = ∫ w, F w * g w := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun w => F w * g w)
      (fun w hw => by simp only [hfF hw])]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
    simp [hg_zero w fun h => hw (hbΩ h)]
  rw [h1, h2]
  -- Expand `b = ∑ᵢ bᵢ eᵢ`; each term `DF(·)(eᵢ) bᵢ` is integrable, as `‖DF‖ ≤ L` and `bᵢ` is
  -- continuous with compact support.
  have hexp : ∀ w, fderiv ℝ F w (b w) = ∑ i, fderiv ℝ F w (e i) * bi i w := by
    intro w
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (b w)]
    simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, mul_comm, e, bi]
  have hterm_int : ∀ i, Integrable (fun w => fderiv ℝ F w (e i) * bi i w) volume := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hbi_cd i).continuous.integrable_of_hasCompactSupport (hbi_cs i))
      (measurable_fderiv_apply_const ℝ F (e i)).aestronglyMeasurable ?_
    filter_upwards with w
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  -- Rademacher (`DF(w)(eᵢ) = ∂_{eᵢ}F(w)` a.e.) and integration by parts for Lipschitz functions.
  have hibp : ∀ i, ∫ w, fderiv ℝ F w (e i) * bi i w
      = -∫ w, fderiv ℝ (bi i) w (e i) * F w := by
    intro i
    obtain ⟨D, hD⟩ := hbi_lip i
    have hae : (fun w => fderiv ℝ F w (e i) * bi i w)
        =ᵐ[volume] (fun w => lineDeriv ℝ F w (e i) * bi i w) := by
      filter_upwards [hF.ae_differentiableAt (μ := volume)] with w hw
      rw [hw.lineDeriv_eq_fderiv]
    rw [integral_congr_ae hae, hF.integral_lineDeriv_mul_eq hD (hbi_cs i) (e i), ← integral_neg]
    congr 1
    ext w
    rw [((hbi_diff i) w).lineDeriv_eq_fderiv]
    simp
  -- Sum over `i`; each `Dbᵢ(·)(eᵢ) F` is continuous and vanishes off the compact `tsupport b`.
  have hterm2_int : ∀ i, Integrable (fun w => fderiv ℝ (bi i) w (e i) * F w) volume := by
    intro i
    refine (((hbi_cfd i).clm_apply continuous_const).mul
      hF.continuous).integrable_of_hasCompactSupport (HasCompactSupport.intro hbc fun w hw => ?_)
    simp [hDbi_zero i w hw]
  calc ∫ w, fderiv ℝ F w (b w) = ∫ w, ∑ i, fderiv ℝ F w (e i) * bi i w := by
        simp_rw [hexp]
    _ = ∑ i, ∫ w, fderiv ℝ F w (e i) * bi i w :=
        integral_finsetSum _ fun i _ => hterm_int i
    _ = ∑ i, -∫ w, fderiv ℝ (bi i) w (e i) * F w :=
        Finset.sum_congr rfl fun i _ => hibp i
    _ = -∫ w, ∑ i, fderiv ℝ (bi i) w (e i) * F w := by
        rw [integral_finsetSum _ fun i _ => hterm2_int i, Finset.sum_neg_distrib]
    _ = -∫ w, F w * g w := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp [g, Finset.mul_sum, mul_comm]

/-- Convergence of the gradient pairings against a `C¹` test field: if `u_k → u` uniformly on
the open set `Ω`, all `C`-Lipschitz on `Ω`, and `b` is `C¹` with compact support in `Ω`, then
`∫_Ω Du_k(b) → ∫_Ω Du(b)`.  With the weak divergence `g ∈ L¹` of `b` given by
`slicing_im_ll_gws_lipschitz_ibp`, `∫_Ω Du_k(b) - ∫_Ω Du(b) = ∫_Ω (u - u_k) g`, which is at most
`sup_Ω |u - u_k| · ∫_Ω |g|`. -/
theorem Submission.slicing_im_ll_gws_smooth_tendsto : ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (u : Eucl n → ℝ) (ug : ℕ → Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C u Ω → (∀ k, LipschitzOnWith C (ug k) Ω) → TendstoUniformlyOn ug u atTop Ω → ∀ b : Eucl n → Eucl n, ContDiff ℝ 1 b → HasCompactSupport b → tsupport b ⊆ Ω → Tendsto (fun k => ∫ w in Ω, fderiv ℝ (ug k) w (b w)) atTop (𝓝 (∫ w in Ω, fderiv ℝ u w (b w))) := by
  intro n Ω C u ug hΩ hu hug hconv b hb hbc hbΩ
  -- Step 1: the weak divergence `g` of `b`, applied to `u` and to every `u_k` (all
  -- `C`-Lipschitz on `Ω`).
  obtain ⟨g, hg, hgf⟩ := Submission.slicing_im_ll_gws_lipschitz_ibp n Ω b hΩ hb hbc hbΩ
  obtain ⟨hu_int, hu_eq⟩ := hgf C u hu
  -- Step 2: `∫_Ω Du_k(b) - ∫_Ω Du(b) = -∫_Ω u_k g + ∫_Ω u g = ∫_Ω (u - u_k) g`.
  have hdiff : ∀ k, (∫ w in Ω, fderiv ℝ (ug k) w (b w)) - ∫ w in Ω, fderiv ℝ u w (b w) =
      ∫ w in Ω, (u w - ug k w) * g w := fun k => by
    obtain ⟨hk_int, hk_eq⟩ := hgf C (ug k) (hug k)
    simp only [sub_mul]
    rw [hk_eq, hu_eq, integral_sub hu_int hk_int]
    ring
  -- Step 3: `A = ∫_Ω |g| ≥ 0`, `η = ε / (2 (A + 1))`, and `N` with `|u - u_k| < η` on `Ω` for
  -- all `k ≥ N` (uniform convergence).
  obtain ⟨A, hA⟩ : ∃ A, ∫ w in Ω, |g w| = A := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [← hA]
    exact integral_nonneg fun w => abs_nonneg (g w)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hA1 : 0 < 2 * (A + 1) := by linarith
  have hη : 0 < ε / (2 * (A + 1)) := div_pos hε hA1
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv _ hη)
  refine ⟨N, fun k hk => ?_⟩
  -- Step 4: `|∫_Ω (u - u_k) g| ≤ ∫_Ω η |g| = η A`.
  have hbound : ∀ w ∈ Ω, ‖(u w - ug k w) * g w‖ ≤ ε / (2 * (A + 1)) * |g w| := fun w hw => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← Real.dist_eq]
    exact mul_le_mul_of_nonneg_right (hN k hk w hw).le (abs_nonneg (g w))
  have hest : ‖∫ w in Ω, (u w - ug k w) * g w‖ ≤ ∫ w in Ω, ε / (2 * (A + 1)) * |g w| :=
    norm_integral_le_of_norm_le (hg.integrableOn.abs.const_mul _)
      (ae_restrict_of_forall_mem hΩ.measurableSet hbound)
  rw [integral_const_mul, hA] at hest
  -- Step 5: `η A < η · 2 (A + 1) = ε`.
  rw [Real.dist_eq, hdiff k, ← Real.norm_eq_abs]
  calc ‖∫ w in Ω, (u w - ug k w) * g w‖ ≤ ε / (2 * (A + 1)) * A := hest
    _ < ε / (2 * (A + 1)) * (2 * (A + 1)) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ ε hA1.ne'
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

/-- Gradients of functions `u_k → u` that converge uniformly on an open `Ω ⊆ ℝⁿ` and are all
`C`-Lipschitz on `Ω` converge weakly-* on `Ω`: `∫_Ω Du_k(c) → ∫_Ω Du(c)` for every field `c`
integrable on `Ω`. -/
theorem Submission.slicing_im_ll_gradient_weak_star :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (u : Eucl n → ℝ) (ug : ℕ → Eucl n → ℝ), IsOpen Ω →
      LipschitzOnWith C u Ω → (∀ k, LipschitzOnWith C (ug k) Ω) →
      TendstoUniformlyOn ug u atTop Ω → ∀ c : Eucl n → Eucl n,
      IntegrableOn c Ω (volume : Measure (Eucl n)) →
      Tendsto (fun k => ∫ w in Ω, fderiv ℝ (ug k) w (c w)) atTop
        (𝓝 (∫ w in Ω, fderiv ℝ u w (c w))) := by
  intro n Ω C u ug hΩ hu hug hconv c hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- A smooth field `b` compactly supported in `Ω` with `∫_Ω |c - b| < ε / (3 (C + 1))`,
  -- so that `C ∫_Ω |c - b| < ε / 3`.
  obtain ⟨b, hb, hbc, hbΩ, hcb⟩ := Submission.slicing_im_ll_gws_smooth_dense n Ω c hΩ hc
    (ε / (3 * (C + 1))) (by positivity)
  have hCcb : (C : ℝ) * ∫ w in Ω, ‖c w - b w‖ < ε / 3 := by
    calc (C : ℝ) * ∫ w in Ω, ‖c w - b w‖ ≤ C * (ε / (3 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hcb.le C.coe_nonneg
      _ < ε / 3 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hbi : IntegrableOn b Ω (volume : Measure (Eucl n)) :=
    (hb.continuous.integrable_of_hasCompactSupport hbc).integrableOn
  -- The pairings against the smooth field `b` converge.
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.1
    (Submission.slicing_im_ll_gws_smooth_tendsto n Ω C u ug hΩ hu hug hconv b
      (hb.of_le (by exact_mod_cast le_top)) hbc hbΩ) (ε / 3) (by positivity)
  refine ⟨k₀, fun k hk => ?_⟩
  -- Replacing `c` by `b` moves the pairings with `Du_k` and with `Du` by at most
  -- `C ∫_Ω |c - b| < ε / 3` each.
  have h₁ := Submission.slicing_im_ll_gws_pairing_bound n Ω C (ug k) hΩ (hug k) c b hc hbi
  have h₂ := Submission.slicing_im_ll_gws_pairing_bound n Ω C u hΩ hu c b hc hbi
  have h₃ := hk₀ k hk
  rw [Real.dist_eq] at h₃ ⊢
  have h₄ := abs_sub_le (∫ w in Ω, fderiv ℝ (ug k) w (c w)) (∫ w in Ω, fderiv ℝ (ug k) w (b w))
    (∫ w in Ω, fderiv ℝ u w (c w))
  have h₅ := abs_sub_le (∫ w in Ω, fderiv ℝ (ug k) w (b w)) (∫ w in Ω, fderiv ℝ u w (b w))
    (∫ w in Ω, fderiv ℝ u w (c w))
  rw [abs_sub_comm (∫ w in Ω, fderiv ℝ u w (b w))] at h₅
  linarith

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
