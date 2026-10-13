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
/-- Euclidean coefficient norms `|γ| = covectorEuclideanNorm γ` of slices of covectors, with
`ι(v) = (0, v) ∈ ℝ^{m+1}` and `e₀ = EuclideanSpace.single 0 1`: (C1) if `γ'(v) = γ(e₀, ι ∘ v)`
then `|γ'| ≤ |γ|`; (C2) if `γ'(v) = γ(ι ∘ v)` then `|γ'| ≤ |γ|`; (C3) `|α| ≤ √(P^n) · ‖α‖`.
For (C1) and (C2), `e₀ = b_0` and `ι(b_j) = b_{j+1}` for the standard bases `b`, so the
coefficients of `γ'` are coefficients of `γ` on distinct strictly increasing multi-indices; for
(C3), each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` is at most
`‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.dph_iprod_slice_covector_norm_le :
    (∀ (m k : ℕ) (γ : Covector (Eucl (m + 1)) (k + 1)) (γ' : Covector (Eucl m) k),
      (∀ v : Fin k → Eucl m, γ' v = γ (Fin.cons (EuclideanSpace.single 0 1) fun i =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      covectorEuclideanNorm γ' ≤ covectorEuclideanNorm γ) ∧
    (∀ (m q : ℕ) (γ : Covector (Eucl (m + 1)) q) (γ' : Covector (Eucl m) q),
      (∀ v : Fin q → Eucl m, γ' v = γ (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      covectorEuclideanNorm γ' ≤ covectorEuclideanNorm γ) ∧
    (∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖) := by
  -- `e₀` is the first standard basis vector of `ℝ^{m+1}`.
  have hb0 : ∀ m : ℕ, (EuclideanSpace.single 0 1 : Eucl (m + 1)) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0 := by
    intro m; simp [EuclideanSpace.basisFun_apply]
  -- `ι` maps the `j`-th standard basis vector of `ℝ^m` to the `(j+1)`-st one of `ℝ^{m+1}`.
  have hbι : ∀ (m : ℕ) (j : Fin m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (EuclideanSpace.basisFun (Fin m) ℝ j))) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ j.succ := by
    intro m j
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [EuclideanSpace.basisFun_apply]
  -- A sum dominated termwise, along an injection, by nonnegative terms is at most the full sum.
  have key : ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (g : A → B),
      Function.Injective g → ∀ (F : B → ℝ) (G : A → ℝ), (∀ b, 0 ≤ F b) →
      (∀ a, G a ≤ F (g a)) → ∑ a, G a ≤ ∑ b, F b := by
    intro A B _ _ _ g hg F G hF hG
    calc ∑ a, G a ≤ ∑ a, F (g a) := Finset.sum_le_sum (fun a _ => hG a)
      _ = ∑ b ∈ Finset.univ.image g, F b := (Finset.sum_image (fun a _ b _ h => hg h)).symm
      _ ≤ ∑ b, F b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hF b)
  refine ⟨?_, ?_, ?_⟩
  · -- (C1): compare along `I ↦ (0, I + 1)`.
    intro m k γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin k → Fin m =>
      (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i.succ
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)) := by
          intro a b hab
          induction a using Fin.cases with
          | zero =>
            induction b using Fin.cases with
            | zero => exact absurd hab (lt_irrefl _)
            | succ j => simp [Fin.succ_pos]
          | succ i =>
            induction b using Fin.cases with
            | zero => exact absurd hab (Fin.not_lt_zero _)
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_lt_succ_iff] at hab ⊢
              exact h1 hab
        rw [ite_eq_left h1, ite_eq_left h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.cons_zero]
          exact hb0 m
        · simp only [Fin.cons_succ]
          exact hbι m (I i)
      · rw [ite_eq_right h1]
        split_ifs <;> positivity
  · -- (C2): compare along `I ↦ I + 1`.
    intro m q γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin q → Fin m => (fun i => (I i).succ : Fin q → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (fun i => (I i).succ : Fin q → Fin (m + 1)) :=
          fun a b hab => Fin.succ_lt_succ_iff.mpr (h1 hab)
        rw [ite_eq_left h1, ite_eq_left h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        exact hbι m (I i)
      · rw [ite_eq_right h1]
        split_ifs <;> positivity
  · -- (C3): every coefficient is at most `‖α‖`, and there are `P ^ n` of them.
    intro P n α
    have hcoef : ∀ I : Fin n → Fin P,
        |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
      intro I
      have h := ContinuousAlternatingMap.le_opNorm α
        (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
      simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
        Real.norm_eq_abs] at h
      exact h
    rw [covectorEuclideanNorm]
    calc Real.sqrt _ ≤ Real.sqrt ((P : ℝ) ^ n * ‖α‖ ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := by
                apply Finset.sum_le_sum
                intro I _
                split_ifs
                · rw [← sq_abs]
                  exact pow_le_pow_left₀ (abs_nonneg _) (hcoef I) 2
                · positivity
            _ = (P : ℝ) ^ n * ‖α‖ ^ 2 := by simp [Finset.card_univ]
      _ = Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- A linear functional `T₀` on `𝒟^q(U)` with `|T₀(ω)| ≤ B · sup_x |ω(x)|` (Euclidean coefficient
norm) is a current of mass at most `B`: test-form convergence makes `sup_x |ω_j(x)| → 0`, since
`|α| ≤ √(P^q) ‖α‖` (conjunct (C3) of `Submission.dph_iprod_slice_covector_norm_le`), and every
mass-admissible `ω` has `T(ω) ≤ |T₀(ω)| ≤ B`. -/
theorem Submission.dph_iprod_current_of_bound :
    ∀ (P q : ℕ) (U : Set (Eucl P)) (T₀ : TestFormOn U q →ₗ[ℝ] ℝ) (B : ℝ), 0 ≤ B →
      (∀ (ω : TestFormOn U q) (C : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) q) x) ≤ C) →
          |T₀ ω| ≤ B * C) →
      ∃ T : GeometricCurrentOn U q, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal B := by
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  intro P q U T₀ B hB hbd
  -- (C3): the coefficient norm is at most `c = √(P^q)` times the operator norm.
  have hC3 : ∀ α : Covector (Eucl P) q,
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ q) * ‖α‖ :=
    fun α => hSN.2.2 P q α
  set c := Real.sqrt ((P : ℝ) ^ q)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  refine ⟨⟨T₀, ?_⟩, fun ω => rfl, ?_⟩
  · -- Sequential continuity at `0`: the order-`0` uniform convergence on the common compact
    -- support `K` gives `|ω_j(x)| ≤ c δ` for all `x` and large `j`, so `|T₀(ω_j)| ≤ B c δ < ε`.
    intro ωs hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := hunif 0
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, B * c * δ < ε := by
      refine ⟨ε / (B * c + 1), by positivity, ?_⟩
      have hpos : 0 < B * c + 1 := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hpos]
      nlinarith [mul_nonneg hB hc0]
    rw [Metric.tendstoUniformlyOn_iff] at h0
    filter_upwards [h0 δ hδ] with n hn
    have hpt : ∀ x, covectorEuclideanNorm ((ωs n : DifferentialForm (Eucl P) q) x) ≤ c * δ := by
      intro x
      by_cases hx : x ∈ K
      · have h1 := hn x hx
        rw [dist_comm, dist_eq_norm] at h1
        have h2 : iteratedFDeriv ℝ 0
            (((0 : TestFormOn U q) : DifferentialForm (Eucl P) q)) x = 0 := by
          simp
        rw [h2, sub_zero, norm_iteratedFDeriv_zero] at h1
        calc covectorEuclideanNorm ((ωs n : DifferentialForm (Eucl P) q) x)
            ≤ c * ‖(ωs n : DifferentialForm (Eucl P) q) x‖ := hC3 _
          _ ≤ c * δ := mul_le_mul_of_nonneg_left h1.le hc0
      · -- Off `K`, `ω_j` vanishes.
        have h3 : (ωs n : DifferentialForm (Eucl P) q) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp n h))
        rw [h3, covectorEuclideanNorm_zero]
        positivity
    have h4 := hbd (ωs n) (c * δ) hpt
    rw [Real.dist_eq, sub_zero]
    calc |T₀ (ωs n)| ≤ B * (c * δ) := h4
      _ = B * c * δ := by ring
      _ < ε := hδε
  · -- Mass: a mass-admissible `ω` has `|ω(x)| ≤ 1` everywhere, so `T(ω) ≤ |T₀(ω)| ≤ B`.
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    have h5 := hbd ω 1 hω.2
    have h6 : T₀ ω ≤ |T₀ ω| := le_abs_self _
    show T₀ ω ≤ B
    linarith
/-- **Continuity along slices** (step 3 of the interval product).  Let `X` be a current in `ℝ^m`
with `M(X) < ∞`; write `(s, x) ∈ ℝ^{m+1}` for `Fin.cons s x`, `ι(w) = (0, w)`, `e₀ = (1, 0)`.
(D1) If `X ∈ 𝒟_k`, `η ∈ 𝒟^{k+1}(ℝ^{m+1})` and `φ(s)(x)(v) = η(s, x)(e₀, ι ∘ v)` for
`s ∈ [0, 1]`, then `s ↦ X(φ(s))` is continuous on `[0, 1]` and `|X(φ(s))| ≤ M(X) · sup |η|`.
(D2) If `X ∈ 𝒟_q`, `ω` is a continuous compactly supported `q`-form on `ℝ^{m+1}` and
`Ψ(s)(x)(v) = ω(s, x)(ι ∘ v)` for all `s`, then `s ↦ X(Ψ(s))` is continuous and
`|X(Ψ(s))| ≤ M(X) · sup |ω|`.  By the mass bound, `X` is `M(X)`-Lipschitz for the sup of the
Euclidean covector norm; slices are bounded by the sliced covector
(`dph_iprod_slice_covector_norm_le`), and `η`, `ω` are uniformly continuous. -/
theorem Submission.dph_iprod_slice_continuity : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → ContinuousOn (fun s => X (φ s)) (Icc (0 : ℝ) 1) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((η : DifferentialForm (Eucl (m + 1)) (k + 1)) y) ≤ C) → ∀ s ∈ Icc (0 : ℝ) 1, |X (φ s)| ≤ X.mass.toReal * C) ∧ (∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ → ∀ (ω : DifferentialForm (Eucl (m + 1)) q) (Ψ : ℝ → TestFormOn (univ : Set (Eucl m)) q), Continuous ω → HasCompactSupport ω → (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v = ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Continuous (fun s => X (Ψ s)) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm (ω y) ≤ C) → ∀ s : ℝ, |X (Ψ s)| ≤ X.mass.toReal * C) := by
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  -- (MB) If `|ω(x)| ≤ C` for all `x`, then `|X(ω)| ≤ M(X) · C` (mass bound with `U = W = univ`).
  have hMB : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ →
      ∀ (ω : TestFormOn (univ : Set (Eucl m)) q) (C : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m) q) x) ≤ C) →
          |X ω| ≤ X.mass.toReal * C := by
    intro m q X hX ω C hC
    refine Submission.cmb_abs_apply_le_of_massOn_le m q univ univ X ω X.mass.toReal C
      ENNReal.toReal_nonneg ?_ (subset_univ _) hC
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  -- If `F(s) - F(s₀)` is uniformly small for close `s, s₀ ∈ S`, then `s ↦ X(F(s))` is
  -- continuous on `S`, by (MB) and linearity of `X`.
  have hcont : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ →
      ∀ (F : ℝ → TestFormOn (univ : Set (Eucl m)) q) (S : Set ℝ),
        (∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, ∀ s₀ ∈ S, |s - s₀| < δ → ∀ x,
          covectorEuclideanNorm (((F s - F s₀ : TestFormOn (univ : Set (Eucl m)) q) :
            DifferentialForm (Eucl m) q) x) ≤ ε) →
        ContinuousOn (fun s => X (F s)) S := by
    intro m q X hX F S hF s₀ hs₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hB : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hB1 : 0 < X.mass.toReal + 1 := by linarith
    obtain ⟨δ, hδ, hFδ⟩ := hF (ε / (X.mass.toReal + 1)) (div_pos hε hB1)
    refine ⟨δ, hδ, fun {s} hs hss₀ => ?_⟩
    rw [Real.dist_eq] at hss₀ ⊢
    have hsub : X (F s - F s₀) = X (F s) - X (F s₀) := map_sub X.toCurrent _ _
    rw [← hsub]
    calc |X (F s - F s₀)| ≤ X.mass.toReal * (ε / (X.mass.toReal + 1)) :=
          hMB m q X hX _ _ (hFδ s hs s₀ hs₀ hss₀)
      _ < (X.mass.toReal + 1) * (ε / (X.mass.toReal + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) (div_pos hε hB1)
      _ = ε := by field_simp
  -- `dist ((s, x), (s₀, x)) = |s - s₀|`: only the `0`-th coordinates differ.
  have hdist : ∀ (m : ℕ) (s s₀ : ℝ) (x : Eucl m),
      dist ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))) = |s - s₀| := by
    intro m s s₀ x
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_succ]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hfrac : ∀ c ε : ℝ, 0 ≤ c → 0 < ε → c * (ε / (c + 1)) ≤ ε := by
    intro c ε hc hε
    have hc1 : 0 < c + 1 := by linarith
    calc c * (ε / (c + 1)) ≤ (c + 1) * (ε / (c + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_pos hε hc1).le
      _ = ε := by field_simp
  refine ⟨?_, ?_⟩
  · -- (D1) `dt`-slices of `η`: (C1) and (C3).
    intro m k X hX η φ hφ
    have hC1 := hSN.1 m k
    have hC3 := hSN.2.2 (m + 1) (k + 1)
    have hc0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ (k + 1)) := Real.sqrt_nonneg _
    have huc : UniformContinuous (η : DifferentialForm (Eucl (m + 1)) (k + 1)) :=
      η.property.1.2.uniformContinuous_of_continuous η.property.1.1.continuous
    refine ⟨hcont m k X hX φ (Icc 0 1) fun ε hε => ?_, fun C hC s hs =>
      hMB m k X hX (φ s) C fun x => (hC1 _ _ fun v => hφ s hs x v).trans (hC _)⟩
    obtain ⟨δ, hδ, hηδ⟩ := Metric.uniformContinuous_iff.mp huc
      (ε / (Real.sqrt (((m + 1 : ℕ) : ℝ) ^ (k + 1)) + 1)) (by positivity)
    refine ⟨δ, hδ, fun s hs s₀ hs₀ hss₀ x => ?_⟩
    -- `(φ s - φ s₀)(x)` is the `dt`-slice of `η(s, x) - η(s₀, x)`.
    have h1 := hC1 ((η : DifferentialForm (Eucl (m + 1)) (k + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
      (η : DifferentialForm (Eucl (m + 1)) (k + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
      (((φ s - φ s₀ : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x) (by
        intro v
        show ((φ s : DifferentialForm (Eucl m) k) - (φ s₀ : DifferentialForm (Eucl m) k)) x v = _
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hφ s hs x v, hφ s₀ hs₀ x v]
        rfl)
    refine h1.trans ((hC3 _).trans ((mul_le_mul_of_nonneg_left ?_ hc0).trans (hfrac _ ε hc0 hε)))
    rw [← dist_eq_norm]
    exact (hηδ (by rwa [hdist])).le
  · -- (D2) horizontal slices of `ω`: (C2) and (C3).
    intro m q X hX ω Ψ hωc hωs hΨ
    have hC2 := hSN.2.1 m q
    have hC3 := hSN.2.2 (m + 1) q
    have hc0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ q) := Real.sqrt_nonneg _
    have huc : UniformContinuous ω := hωs.uniformContinuous_of_continuous hωc
    refine ⟨continuousOn_univ.mp (hcont m q X hX Ψ univ fun ε hε => ?_), fun C hC s =>
      hMB m q X hX (Ψ s) C fun x => (hC2 _ _ fun v => hΨ s x v).trans (hC _)⟩
    obtain ⟨δ, hδ, hωδ⟩ := Metric.uniformContinuous_iff.mp huc
      (ε / (Real.sqrt (((m + 1 : ℕ) : ℝ) ^ q) + 1)) (by positivity)
    refine ⟨δ, hδ, fun s _ s₀ _ hss₀ x => ?_⟩
    -- `(Ψ s - Ψ s₀)(x)` is the horizontal slice of `ω(s, x) - ω(s₀, x)`.
    have h1 := hC2
      (ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
        ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
      (((Ψ s - Ψ s₀ : TestFormOn (univ : Set (Eucl m)) q) : DifferentialForm (Eucl m) q) x) (by
        intro v
        show ((Ψ s : DifferentialForm (Eucl m) q) - (Ψ s₀ : DifferentialForm (Eucl m) q)) x v = _
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hΨ s x v, hΨ s₀ x v]
        rfl)
    refine h1.trans ((hC3 _).trans ((mul_le_mul_of_nonneg_left ?_ hc0).trans (hfrac _ ε hc0 hε)))
    rw [← dist_eq_norm]
    exact (hωδ (by rwa [hdist])).le
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

/-- The product `[[0, 1]] × X` of a finite-mass current `X` on `ℝ^m`: with chosen `dt`-slices
`φ^η s x = η(s, x)(e₀, ι ·)`, the functional `η ↦ ∫₀¹ X(φ^η s) ds` is linear and bounded by
`M(X) · sup |η|`, hence a current `Z` with `M(Z) ≤ M(X)`; the integral does not depend on the
slice family, which gives the characterization and uniqueness; and `Z` vanishes on every ball
missing the closed cylinder `[0, 1] × spt X`, since there every slice `φ^η s` misses `spt X`. -/
theorem Submission.dph_iprod_exists :
    ∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ →
      ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1),
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
          Z η = ∫ s in (0 : ℝ)..1, X (φ s)) ∧
        (∀ Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1),
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
            Z' η = ∫ s in (0 : ℝ)..1, X (φ s)) → Z' = Z) ∧
        Z.mass ≤ X.mass ∧
        Z.support ⊆ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
          (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈
            X.support} := by
  have hSF := Submission.iwl_cr_ci_slice_testForm
  have hVS := Submission.isoperimetric_apply_eq_zero_of_disjoint_support
  have hCC := Submission.dph_iprod_current_of_bound
  have hC := Submission.dph_iprod_slice_continuity
  intro m k X hX
  -- A chosen slice family `φ η` of every `η`.
  choose φ hφc hφ using fun η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1) => hSF m k η
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  -- Any slice family of `η` on `[0, 1]` agrees with `φ η` there, so has the same integral.
  have hcongr : ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
      (ψ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
        (ψ s : DifferentialForm (Eucl m) k) x v =
          (η : DifferentialForm (Eucl (m + 1)) (k + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      ∫ s in (0 : ℝ)..1, X (ψ s) = ∫ s in (0 : ℝ)..1, X (φ η s) := by
    intro η ψ hψ
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have : ψ s = φ η s := by
      apply Subtype.ext; funext x; ext v; rw [hψ s hs x v, hφ η s x v]
    simp only [this]
  have hint : ∀ η, IntervalIntegrable (fun s => X (φ η s)) MeasureTheory.volume 0 1 := by
    intro η
    exact ((hC.1 m k X hX η (φ η) (fun s _ x v => hφ η s x v)).1).intervalIntegrable_of_Icc
      zero_le_one
  -- The linear functional `T₀ η = ∫₀¹ X(φ η s) ds`.
  let T₀ : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun η => ∫ s in (0 : ℝ)..1, X (φ η s)
      map_add' := by
        intro η η'
        have h := hcongr (η + η') (fun s => φ η s + φ η' s) (by
          intro s _ x v
          show ((φ η s : DifferentialForm (Eucl m) k) +
            (φ η' s : DifferentialForm (Eucl m) k)) x v = _
          rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, hφ η s x v, hφ η' s x v]
          rfl)
        rw [← h]
        have : (fun s => X (φ η s + φ η' s)) = fun s => X (φ η s) + X (φ η' s) := by
          funext s; exact map_add X.toCurrent _ _
        rw [this, intervalIntegral.integral_add (hint η) (hint η')]
      map_smul' := by
        intro c η
        have h := hcongr (c • η) (fun s => c • φ η s) (by
          intro s _ x v
          show (c • (φ η s : DifferentialForm (Eucl m) k)) x v = _
          rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, hφ η s x v]
          rfl)
        rw [← h]
        have : (fun s => X (c • φ η s)) = fun s => c * X (φ η s) := by
          funext s; exact map_smul X.toCurrent c _
        rw [this, intervalIntegral.integral_const_mul]
        rfl }
  have hT₀ : ∀ η, T₀ η = ∫ s in (0 : ℝ)..1, X (φ η s) := fun η => rfl
  -- `|T₀ η| ≤ M(X) · C` whenever `|η| ≤ C` pointwise.
  have hbound : ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((η : DifferentialForm (Eucl (m + 1)) (k + 1)) y) ≤ C) →
      |T₀ η| ≤ X.mass.toReal * C := by
    intro η C hηC
    have hb := (hC.1 m k X hX η (φ η) (fun s _ x v => hφ η s x v)).2 C hηC
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := X.mass.toReal * C) (f := fun s => X (φ η s)) (by
        intro s hs
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs]
        exact hb s ⟨hs.1.le, hs.2⟩)
    rw [hT₀]
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using this
  obtain ⟨Z, hZ, hZm⟩ := hCC (m + 1) (k + 1) univ T₀ X.mass.toReal hB0 hbound
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro η ψ hψ
    rw [hZ η, hT₀, hcongr η ψ hψ]
  · intro Z' hZ'
    ext η
    rw [hZ' η (φ η) (fun s _ x v => hφ η s x v), hZ η, hT₀]
  · calc Z.mass ≤ ENNReal.ofReal X.mass.toReal := hZm
      _ = X.mass := ENNReal.ofReal_toReal hX.ne
  · -- A point off the closed cylinder `[0, 1] × spt X` has a ball around it missing the
    -- cylinder; `Z` vanishes there, so the point lies in the zero region of `Z`.
    intro y₀ hy₀
    by_contra hcyl
    have hsuppX : IsClosed X.support := by
      have : X.support = (X.zeroRegion)ᶜ := by
        ext y; simp [GeometricCurrentOn.support]
      rw [this]; exact X.isOpen_zeroRegion.isClosed_compl
    have hclosed : IsClosed {y : Eucl (m + 1) |
        EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
          (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} := by
      apply IsClosed.inter
      · exact isClosed_Icc.preimage (by fun_prop)
      · exact hsuppX.preimage (by fun_prop)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl y₀ hcyl
    have hvan : Z.VanishesOn (ball y₀ ρ) := by
      intro η hη
      rw [hZ η, hT₀]
      -- For `s ∈ [0, 1]`, the slice `φ η s` is supported in `{x | (s, x) ∈ tsupport η}`,
      -- which misses `spt X`.
      have h0 : ∀ s ∈ Set.uIcc (0 : ℝ) 1, X (φ η s) = 0 := by
        intro s hs
        rw [Set.uIcc_of_le zero_le_one] at hs
        apply hVS
        rw [Set.disjoint_left]
        intro x hx hxX
        have hsub : tsupport (φ η s : DifferentialForm (Eucl m) k) ⊆
            (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ⁻¹'
              tsupport (η : DifferentialForm (Eucl (m + 1)) (k + 1)) := by
          apply closure_minimal _ ((isClosed_tsupport _).preimage (by fun_prop))
          intro x' hx'
          by_contra hn
          apply hx'
          ext v
          rw [hφ η s x' v, image_eq_zero_of_notMem_tsupport hn]
          rfl
        have h2 := hη (hsub hx)
        apply hball h2
        refine ⟨?_, ?_⟩
        · simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero]
          exact hs
        · simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
            ContinuousLinearEquiv.symm_apply_apply]
          exact hxX
      rw [intervalIntegral.integral_congr h0]
      simp
    have hW : ball y₀ ρ ⊆ Z.zeroRegion := by
      intro y hy
      refine Set.mem_sUnion.mpr ⟨ball y₀ ρ, ⟨isOpen_ball, ?_, subset_univ _, hvan⟩, hy⟩
      exact (isCompact_closedBall y₀ ρ).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    exact hy₀.2 (hW (mem_ball_self hρ))

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
