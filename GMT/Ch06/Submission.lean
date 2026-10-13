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

/-- **Unit bound for the orientation `±τ₁ ∧ ⋯ ∧ τₙ` (Simon Ch. 6, 3.1).**  If `τ` is an
orthonormal family in `ℝ^P` and `w = ±simpleNVector τ`, then `|w(α)| ≤ ‖α‖` for every
`n`-covector `α`: `simpleNVector τ α = α(τ₁, …, τₙ)` and `‖α(τ)‖ ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
(`ContinuousAlternatingMap.le_opNorm`, each `τᵢ` a unit vector). -/
theorem Submission.fiw_ims_tt_unit_bound : ∀ (P n : ℕ) (τ : Fin n → Eucl P) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → ∀ α : Covector (Eucl P) n, |w α| ≤ ‖α‖ := by
  intro P n τ w hτ hw α
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`.
  have h1 : |simpleNVector τ α| ≤ ‖α‖ := by
    rw [simpleNVector_apply, ← Real.norm_eq_abs]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
      _ = ‖α‖ := by simp [hτ.1]
  -- `w = ±simpleNVector τ`, and `|-a| = |a|`.
  rcases hw with rfl | rfl
  · exact h1
  · simpa [abs_neg] using h1
/-- **Null-set consequences of the co-area identity (Simon Ch. 6, proof of 4.5(2)).**  Assume
(CA): for every Borel `g ≥ 0`, `t ↦ ∫_{M ∩ f⁻¹{t}} g dν` is a.e.-measurable and
`∫_ℝ ∫_{M ∩ f⁻¹{t}} g dν dt = ∫_M |G| g dμ`.  Then (i) `G = 0` `μ⌞M`-a.e. on each level set
`{f = c}` (test (CA) with `g = 1_{f = c}`: the slice integrals vanish for `t ≠ c`); and (ii) a
`μ`-null `Z ⊆ M` has `ν`-null slices `Z ∩ f⁻¹{t}` for a.e. `t` (test (CA) with `g = 1_{Z'}`,
`Z' ⊇ Z` a measurable `μ`-null hull). -/
theorem Submission.slicing_im_si_coarea_null_sets : ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P), Measurable f → Measurable G → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂μ) → (∀ c : ℝ, ∀ᵐ x ∂(μ.restrict M), f x = c → G x = 0) ∧ ∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0 := by
  intro P μ ν M f G hf hG CA
  constructor
  · intro c
    have hmc : MeasurableSet (f ⁻¹' {c}) := hf (measurableSet_singleton c)
    obtain ⟨-, hCA⟩ := CA ((f ⁻¹' {c}).indicator 1) (measurable_one.indicator hmc)
    -- The slice integrals `ν(f⁻¹{c} ∩ M ∩ f⁻¹{t})` vanish for `t ≠ c`.
    have hslice : ∀ t, t ≠ c → ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν = 0 := by
      intro t ht
      rw [lintegral_indicator_one hmc, Measure.restrict_apply hmc]
      convert measure_empty (μ := ν)
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hxc _ hxt
      exact ht (hxt.symm.trans hxc)
    -- `{c}` is Lebesgue-null, so the left side of (CA) is `0`.
    have hL : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν)
        ∂(volume : Measure ℝ) = 0 := by
      have : (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν) =ᵐ[volume] 0 := by
        have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
          simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t ht
        exact hslice t ht
      rw [lintegral_congr_ae this]
      simp
    -- Hence `|G| 1_{f = c} = 0` `μ⌞M`-a.e.
    rw [hL] at hCA
    have hmeas : AEMeasurable (fun x => ‖G x‖ₑ * (f ⁻¹' {c}).indicator 1 x) (μ.restrict M) :=
      (hG.enorm.mul (measurable_one.indicator hmc)).aemeasurable
    have h0 := (lintegral_eq_zero_iff' hmeas).1 hCA.symm
    filter_upwards [h0] with x hx hfx
    have hxc : x ∈ f ⁻¹' {c} := hfx
    simp only [Pi.zero_apply, indicator_of_mem hxc, Pi.one_apply, mul_one, enorm_eq_zero] at hx
    exact hx
  · intro Z hZM hZ
    -- A measurable `μ`-null hull `Z' = toMeasurable μ Z ⊇ Z`.
    have hZ'm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hZ'0 : μ (toMeasurable μ Z) = 0 := by rw [measure_toMeasurable]; exact hZ
    obtain ⟨hae, hCA⟩ := CA ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZ'm)
    -- The right side of (CA) vanishes, since `1_{Z'} = 0` `μ`-a.e.
    have hR : ∫⁻ x in M, ‖G x‖ₑ * (toMeasurable μ Z).indicator 1 x ∂μ = 0 := by
      have hnull : ∀ᵐ x ∂μ, x ∉ toMeasurable μ Z := measure_eq_zero_iff_ae_notMem.1 hZ'0
      have : (fun x => ‖G x‖ₑ * (toMeasurable μ Z).indicator 1 x) =ᵐ[μ.restrict M] 0 := by
        filter_upwards [ae_restrict_of_ae hnull] with x hx
        simp [indicator_of_notMem hx]
      rw [lintegral_congr_ae this]
      simp
    -- So `ν(Z' ∩ (M ∩ f⁻¹{t})) = 0` for a.e. `t`, and `Z ∩ f⁻¹{t} ⊆ Z' ∩ (M ∩ f⁻¹{t})`.
    rw [hR] at hCA
    have h0 := (lintegral_eq_zero_iff' hae).1 hCA
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply] at ht
    rw [lintegral_indicator_one hZ'm, Measure.restrict_apply hZ'm] at ht
    refine measure_mono_null (fun x hx => ?_) ht
    exact ⟨subset_toMeasurable μ Z hx.1, hZM hx.1, hx.2⟩

/-- **Borel density for `θ⟨ξ, G♭ ∧ ω⟩` (Simon Ch. 6, Remark 4.2 and proof of 4.5).**  For a
rectifiable triple `(M, θ, ξ)`, a Borel `G`, `ν := |G|⁻¹G` and `ω ∈ 𝒟ᵐ(U)`, there is a Borel
`Hⁿ⌞M`-integrable `g` vanishing on `{G = 0}` with `g = θ⟨ξ⌞ν, ω⟩` where `G ≠ 0` and
`θ⟨ξ, G♭ ∧ ω⟩ = |G| g`, `Hⁿ⌞M`-a.e.: `g := 1_{K ∩ {G ≠ 0}} θ' ξ'(ν♭ ∧ ω)` with `K = tsupport ω`,
Borel versions `θ'` of `θ` on `M ∩ K` and `ξ'` of `ξ` on `M`, dominated by
`(m + 1) sup ‖ω‖ · |1_K θ'|` (unit bound `|ξ(α)| ≤ ‖α‖`). -/
theorem Submission.slicing_im_si_borel_density :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (G : Eucl P → Eucl P) (ω : TestFormOn U m), IsRectifiableTriple U (m + 1) M θ ξ → Measurable G → ∃ g : Eucl P → ℝ, Measurable g ∧ Integrable g ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧ (∀ x, G x = 0 → g x = 0) ∧ ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), (G x ≠ 0 → g x = θ x * (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x)))) ((ω : DifferentialForm (Eucl P) m) x)) ∧ θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))) = ‖G x‖ * g x := by
  have unit_bound := Submission.fiw_ims_tt_unit_bound
  intro P m U M θ ξ G ω hM hG
  have hwc : Continuous (ω : DifferentialForm (Eucl P) m) := ω.2.1.1.continuous
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) m)) := ω.2.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U := ω.2.2
  obtain ⟨K, hK⟩ : ∃ K : Set (Eucl P), K = tsupport (ω : DifferentialForm (Eucl P) m) := ⟨_, rfl⟩
  rw [← hK] at hKc hKU
  have hKm : MeasurableSet K := hK ▸ (isClosed_tsupport _).measurableSet
  have hw0 : ∀ x, x ∉ K → (ω : DifferentialForm (Eucl P) m) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hK ▸ hx)
  obtain ⟨Cw, hCw⟩ := hwc.bounded_above_of_compact_support ω.2.1.2
  -- Borel versions of θ (on M ∩ K) and ξ (on M)
  have hθK : IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P)) := hM.integrableOn K hKc hKU
  obtain ⟨θ', hθ'm, hθθ'⟩ := hθK.aestronglyMeasurable
  obtain ⟨ξ', hξ'm, hξξ'⟩ := hM.aestronglyMeasurable
  -- the covector field β = ν♭ ∧ ω with ν = G/|G|
  have hνm : Measurable (fun x => ‖G x‖⁻¹ • G x) := (hG.norm.inv).smul hG
  have hνle : ∀ x, ‖‖G x‖⁻¹ • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, norm_inv, norm_norm]
    by_cases h : ‖G x‖ = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  obtain ⟨β, hβ⟩ : ∃ β : Eucl P → Covector (Eucl P) (m + 1), β = fun x =>
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := ⟨_, rfl⟩
  have hBc : Continuous (fun p : Eucl P × Covector (Eucl P) m =>
      ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ p.1).smulRight p.2)) := by
    have h2 : Continuous (fun p : Eucl P × Covector (Eucl P) m => (innerSL ℝ p.1).smulRight p.2) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Eucl P) (F := Covector (Eucl P) m)).continuous.comp
        (((innerSL ℝ).continuous.comp continuous_fst).prodMk continuous_snd)
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp h2
  have hβm : StronglyMeasurable β := by
    have h3 : StronglyMeasurable (fun x => ((‖G x‖⁻¹ • G x : Eucl P), (ω : DifferentialForm (Eucl P) m) x)) :=
      hνm.stronglyMeasurable.prodMk hwc.stronglyMeasurable
    have h4 := hBc.comp_stronglyMeasurable h3
    beta_reduce at h4
    rw [hβ]; exact h4
  have hβle : ∀ x, ‖β x‖ ≤ (m + 1) * Cw := by
    intro x
    rw [hβ]
    calc ‖ContinuousAlternatingMap.alternatizeUncurryFin
            ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))‖
        ≤ ((m : ℝ) + 1) * ‖(innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)‖ :=
          ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _
      _ = ((m : ℝ) + 1) * (‖‖G x‖⁻¹ • G x‖ * ‖(ω : DifferentialForm (Eucl P) m) x‖) := by
          rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      _ ≤ ((m : ℝ) + 1) * (1 * Cw) := by
          gcongr
          · exact hνle x
          · exact hCw x
      _ = (m + 1) * Cw := by ring
  have hξβm : StronglyMeasurable (fun x => ξ' x (β x)) := by
    have h4 := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hξ'm.prodMk hβm)
    beta_reduce at h4
    exact h4
  -- the density
  have hSm : MeasurableSet {x | x ∈ K ∧ G x ≠ 0} :=
    hKm.inter (hG (measurableSet_singleton (0 : Eucl P))).compl
  obtain ⟨g, hg⟩ : ∃ g : Eucl P → ℝ,
      g = {x | x ∈ K ∧ G x ≠ 0}.indicator (fun x => θ' x * ξ' x (β x)) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact (hθ'm.measurable.mul hξβm.measurable).indicator hSm
  -- a.e. facts on M
  have hθae : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ K → θ x = θ' x := by
    have : ∀ᵐ x ∂(((μHE[m + 1] : Measure (Eucl P)).restrict M).restrict K), θ x = θ' x := by
      rw [Measure.restrict_restrict hKm, inter_comm]; exact hθθ'
    exact (ae_restrict_iff' hKm).1 this
  have hunit : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) (m + 1), |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, -, hξx⟩ := hx
    exact unit_bound P (m + 1) τ (ξ x) hτ hξx
  refine ⟨g, hgm, ?_, ?_, ?_⟩
  · -- integrability
    have hθ'K : IntegrableOn θ' (M ∩ K) (μHE[m + 1] : Measure (Eucl P)) := hθK.congr_fun_ae hθθ'
    have hind : Integrable (K.indicator θ') ((μHE[m + 1] : Measure (Eucl P)).restrict M) := by
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
      exact hθ'K
    refine Integrable.mono' ((hind.norm).const_mul ((m + 1) * Cw)) hgm.aestronglyMeasurable ?_
    filter_upwards [hξξ', hunit] with x hξx hux
    by_cases hS : x ∈ K ∧ G x ≠ 0
    · rw [hg, indicator_of_mem (show x ∈ {x | x ∈ K ∧ G x ≠ 0} from hS), indicator_of_mem hS.1, norm_mul]
      have : ‖ξ' x (β x)‖ ≤ (m + 1) * Cw := by
        rw [← hξx, Real.norm_eq_abs]; exact (hux (β x)).trans (hβle x)
      calc ‖θ' x‖ * ‖ξ' x (β x)‖ ≤ ‖θ' x‖ * ((m + 1) * Cw) := by gcongr
        _ = (m + 1) * Cw * ‖θ' x‖ := by ring
    · rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from hS), norm_zero]
      have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans (hCw x)
      positivity
  · intro x hx
    rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from fun h => h.2 hx)]
  · filter_upwards [hξξ', hθae] with x hξx hθx
    have hcomp : (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))
          ((ω : DifferentialForm (Eucl P) m) x) = ξ x (β x) := by
      rw [hβ]; rfl
    have part1 : G x ≠ 0 → g x = θ x * ξ x (β x) := by
      intro hG0
      by_cases hxK : x ∈ K
      · rw [hg, indicator_of_mem (show x ∈ {x | x ∈ K ∧ G x ≠ 0} from ⟨hxK, hG0⟩), hθx hxK, hξx]
      · have hβ0 : β x = 0 := by
          have hsr : (innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight (0 : Covector (Eucl P) m) = 0 := by
            ext y; simp
          rw [hβ]
          simp only [hw0 x hxK, hsr]
          exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
        rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from fun h => hxK h.1), hβ0,
          map_zero, mul_zero]
    refine ⟨fun hG0 => by rw [hcomp]; exact part1 hG0, ?_⟩
    by_cases hG0 : G x = 0
    · have h0 : ContinuousAlternatingMap.alternatizeUncurryFin (0 : Eucl P →L[ℝ] Covector (Eucl P) m) = 0 :=
        map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
      simp [hG0, h0]
    · have hGν : G x = ‖G x‖ • (‖G x‖⁻¹ • G x) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0), one_smul]
      have hlin : ∀ (c : ℝ) (v : Eucl P) (α : Covector (Eucl P) m),
          (innerSL ℝ (c • v)).smulRight α = c • (innerSL ℝ v).smulRight α := by
        intro c v α
        ext y; simp [smul_smul]
      have hsm : (innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x) =
          ‖G x‖ • (innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x) := by
        rw [← hlin]
        congr 2
      have hβx : β x = ContinuousAlternatingMap.alternatizeUncurryFin
          ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by rw [hβ]
      rw [hsm, ContinuousAlternatingMap.alternatizeUncurryFin_smul, map_smul, smul_eq_mul, ← hβx,
        part1 hG0]
      ring
/-- Signed co-area identity on a level band (Simon Ch. 6, Remark 4.2): if the co-area formula
`∫ ∫_{M ∩ f⁻¹{t}} h dν dt = ∫_M |G| h dμ` holds for every Borel `h ≥ 0` and `|G| g` is
`μ⌞M`-integrable, then `t ↦ ∫_{M ∩ f⁻¹{t}} g dν` is integrable and
`∫_{M ∩ f⁻¹(a, b)} |G| g dμ = ∫_{(a, b)} ∫_{M ∩ f⁻¹{t}} g dν dt` (split `g = g⁺ - g⁻`). -/
theorem Submission.slicing_im_si_signed_coarea :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (g : Eucl P → ℝ), Measurable f → Measurable G → Measurable g → Integrable (fun x => ‖G x‖ * g x) (μ.restrict M) → (∀ h : Eucl P → ℝ≥0∞, Measurable h → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * h x ∂μ) → Integrable (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∀ a b : ℝ, ∫ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ * g x ∂μ = ∫ t in Ioo a b, (∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) := by
  intro P μ ν M f G g hf hG hg hGg CA
  -- positive and negative parts `g⁺ = ofReal g`, `g⁻ = ofReal (-g)`
  have hgp : Measurable (fun x => ENNReal.ofReal (g x)) := ENNReal.measurable_ofReal.comp hg
  have hgn : Measurable (fun x => ENNReal.ofReal (-g x)) := ENNReal.measurable_ofReal.comp hg.neg
  obtain ⟨hφpm, hφp⟩ := CA _ hgp
  obtain ⟨hφnm, hφn⟩ := CA _ hgn
  have hprod : ∀ x, ‖G x‖ₑ * ENNReal.ofReal (g x) = ENNReal.ofReal (‖G x‖ * g x) := by
    intro x; rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  have hprodn : ∀ x, ‖G x‖ₑ * ENNReal.ofReal (-g x) = ENNReal.ofReal (-(‖G x‖ * g x)) := by
    intro x; rw [← mul_neg, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  -- both slice integrals of the parts have finite total integral, hence are a.e. finite
  have hfinp : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (g x) ∂ν) ∂(volume : Measure ℝ) ≠ ∞ := by
    rw [hφp]; simp_rw [hprod]; exact hGg.lintegral_lt_top.ne
  have hfinn : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (-g x) ∂ν) ∂(volume : Measure ℝ) ≠ ∞ := by
    rw [hφn]; simp_rw [hprodn]; exact hGg.neg.lintegral_lt_top.ne
  have hltp := ae_lt_top' hφpm hfinp
  have hltn := ae_lt_top' hφnm hfinn
  -- the slice integral equals the difference of the parts for a.e. `t`
  have hae : (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) =ᵐ[volume]
      fun t => (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (g x) ∂ν).toReal -
        (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (-g x) ∂ν).toReal := by
    filter_upwards [hltp, hltn] with t htp htn
    have hint : Integrable g (ν.restrict (M ∩ f ⁻¹' {t})) := by
      refine ⟨hg.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      have : (fun x => ‖g x‖ₑ) = fun x => ENNReal.ofReal (g x) + ENNReal.ofReal (-g x) := by
        funext x
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (g x) with h | h
        · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -g x ≤ 0), add_zero]
        · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
      rw [this, lintegral_add_left hgp]
      exact ENNReal.add_lt_top.2 ⟨htp, htn⟩
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  have hψ : Integrable (fun t => (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (g x) ∂ν).toReal -
        (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (-g x) ∂ν).toReal) (volume : Measure ℝ) :=
    (integrable_toReal_of_lintegral_ne_top hφpm hfinp).sub
      (integrable_toReal_of_lintegral_ne_top hφnm hfinn)
  refine ⟨hψ.congr hae.symm, fun a b => ?_⟩
  have hE : MeasurableSet (f ⁻¹' Ioo a b) := hf measurableSet_Ioo
  -- band identity for a nonnegative Borel function: apply (CA) to `1_{f⁻¹(a, b)} h`
  have part : ∀ h : Eucl P → ℝ≥0∞, Measurable h →
      ∫⁻ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ₑ * h x ∂μ = ∫⁻ t in Ioo a b, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) := by
    intro h hh
    obtain ⟨-, hCA⟩ := CA ((f ⁻¹' Ioo a b).indicator h) (hh.indicator hE)
    have hL : ∀ t, ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' Ioo a b).indicator h x ∂ν =
        (Ioo a b).indicator (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) t := by
      intro t
      have hft : ∀ᵐ x ∂(ν.restrict (M ∩ f ⁻¹' {t})), f x = t := by
        have hmeas : MeasurableSet {a | ¬f a = t} := (hf (measurableSet_singleton t)).compl
        rw [ae_iff, Measure.restrict_apply hmeas]
        convert measure_empty (μ := ν)
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false, not_and]
        intro h1 _ h2
        exact h1 h2
      by_cases ht : t ∈ Ioo a b
      · rw [indicator_of_mem ht]
        apply lintegral_congr_ae
        filter_upwards [hft] with x hx
        rw [indicator_of_mem (show x ∈ f ⁻¹' Ioo a b by simp [mem_preimage, hx, ht])]
      · rw [indicator_of_notMem ht]
        rw [← lintegral_zero]
        apply lintegral_congr_ae
        filter_upwards [hft] with x hx
        rw [indicator_of_notMem (show x ∉ f ⁻¹' Ioo a b by simp [mem_preimage, hx, ht])]
    simp_rw [hL] at hCA
    rw [lintegral_indicator measurableSet_Ioo] at hCA
    rw [hCA]
    have : ∀ x, ‖G x‖ₑ * (f ⁻¹' Ioo a b).indicator h x = (f ⁻¹' Ioo a b).indicator (fun x => ‖G x‖ₑ * h x) x := by
      intro x
      by_cases hx : x ∈ f ⁻¹' Ioo a b
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    simp_rw [this]
    rw [lintegral_indicator hE, Measure.restrict_restrict hE, inter_comm]
  have hpp := part _ hgp
  have hnn := part _ hgn
  have hGgE : Integrable (fun x => ‖G x‖ * g x) (μ.restrict (M ∩ f ⁻¹' Ioo a b)) :=
    hGg.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  -- subtract the finite parts on both sides
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGgE]
  simp_rw [← hprod, ← hprodn]
  rw [hpp, hnn]
  rw [integral_congr_ae (ae_restrict_of_ae hae)]
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hφpm hfinp).restrict
    (integrable_toReal_of_lintegral_ne_top hφnm hfinn).restrict]
  rw [integral_toReal hφpm.restrict (ae_restrict_of_ae hltp),
    integral_toReal hφnm.restrict (ae_restrict_of_ae hltn)]
/-- Transfer of an a.e. identity on `M` to almost every slice: if `μ`-null subsets `Z ⊆ M` have
`ν`-null slices `Z ∩ f⁻¹{t}` for a.e. `t`, `g = 0` off the Borel set `S` and `g = F` on `S`
`μ⌞M`-a.e., then `∫_{M ∩ f⁻¹{t}} g dν = ∫_{{x ∈ M : f x = t, x ∈ S}} F dν` for a.e. `t`
(Simon 4.5, slice identification). -/
theorem Submission.slicing_im_si_slice_ae_transfer :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M S : Set (Eucl P)) (f g F : Eucl P → ℝ), NullMeasurableSet M μ → MeasurableSet S → Measurable f → (∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0) → (∀ x, x ∉ S → g x = 0) → (∀ᵐ x ∂(μ.restrict M), x ∈ S → g x = F x) → ∀ᵐ t ∂(volume : Measure ℝ), ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν = ∫ x in {x | x ∈ M ∧ f x = t ∧ x ∈ S}, F x ∂ν := by
  intro P μ ν M S f g F hM hS hf hNT hg0 hgF
  -- A Borel `M₁ ⊆ M` with `μ(M \ M₁) = 0`; the bad set `Z₁ ∪ (M \ M₁) ⊆ M` is `μ`-null.
  obtain ⟨M₁, hM₁M, hM₁m, hM₁ae⟩ := hM.exists_measurable_subset_ae_eq
  have hZ₁ : μ ({x | ¬(x ∈ S → g x = F x)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply M _).trans (ae_iff.1 hgF).le) (zero_le)
  have hZ₂ : μ (M \ M₁) = 0 := (ae_eq_set.1 hM₁ae).2
  have hZ : μ (({x | ¬(x ∈ S → g x = F x)} ∩ M) ∪ (M \ M₁)) = 0 := measure_union_null hZ₁ hZ₂
  -- For a.e. `t` the slice of the bad set is `ν`-null.
  filter_upwards [hNT _ (union_subset inter_subset_right sdiff_subset) hZ] with t ht
  have hft : MeasurableSet (f ⁻¹' {t}) := hf (measurableSet_singleton t)
  -- Both domains are `ν`-a.e. equal to Borel sets cut out by `M₁`.
  have hA : (M ∩ f ⁻¹' {t} : Set (Eucl P)) =ᵐ[ν] (M₁ ∩ f ⁻¹' {t} : Set (Eucl P)) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ ht
      intro x hx
      exact ⟨Or.inr ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩, hx.1.2⟩
    · rw [sdiff_eq_empty.2 (inter_subset_inter_left _ hM₁M), measure_empty]
  have hB : ({x | x ∈ M ∧ f x = t ∧ x ∈ S} : Set (Eucl P)) =ᵐ[ν] (M₁ ∩ f ⁻¹' {t} ∩ S : Set (Eucl P)) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ ht
      rintro x ⟨⟨hxM, hxt, hxS⟩, hx⟩
      refine ⟨Or.inr ⟨hxM, fun h => hx ⟨⟨h, hxt⟩, hxS⟩⟩, hxt⟩
    · have : (M₁ ∩ f ⁻¹' {t} ∩ S : Set (Eucl P)) \ {x | x ∈ M ∧ f x = t ∧ x ∈ S} = ∅ := by
        ext x
        simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact h2 (hM₁M h1.1.1) h1.1.2 h1.2
      rw [this, measure_empty]
  rw [Measure.restrict_congr_set hA, Measure.restrict_congr_set hB]
  -- `g = 1_S g`, so the left side is the integral of `g` over `M₁ ∩ f⁻¹{t} ∩ S`.
  have hgS : (fun x => g x) = S.indicator g := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hg0 x hx]
  rw [show (∫ x in M₁ ∩ f ⁻¹' {t}, g x ∂ν) = ∫ x in M₁ ∩ f ⁻¹' {t}, S.indicator g x ∂ν by
    rw [← hgS], setIntegral_indicator hS]
  -- On this Borel set `g = F` off the `ν`-null slice of the bad set.
  apply setIntegral_congr_ae ((hM₁m.inter hft).inter hS)
  rw [ae_iff]
  refine measure_mono_null ?_ ht
  intro x hx
  simp only [mem_ofPred_eq, Classical.not_imp] at hx
  obtain ⟨⟨⟨hxM₁, hxt⟩, hxS⟩, hne⟩ := hx
  exact ⟨Or.inl ⟨fun h => hne (h hxS), hM₁M hxM₁⟩, hxt⟩
/-- One-sided Lebesgue points: for locally integrable `φ : ℝ → ℝ` and a.e. `t`, the left averages
`ε⁻¹ ∫_{(t - ε, t)} φ` tend to `φ t` as `ε → 0+` (Lebesgue differentiation along the Vitali
family of `volume`; Simon Ch. 6, Remark 4.2 and the proof of 4.5(2)). -/
theorem Submission.slicing_im_si_left_lebesgue_point :
    ∀ φ : ℝ → ℝ, LocallyIntegrable φ (volume : Measure ℝ) → ∀ᵐ t ∂(volume : Measure ℝ), Tendsto (fun ε : ℝ => ε⁻¹ * ∫ r in Ioo (t - ε) t, φ r) (𝓝[>] 0) (𝓝 (φ t)) := by
  intro φ hφ
  -- Lebesgue differentiation along the Vitali family of `volume`, restricted to left intervals.
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average hφ]
    with t ht
  have hleft := ht.comp (Real.tendsto_Icc_vitaliFamily_left t)
  -- `ε ↦ t - ε` maps `𝓝[>] 0` to `𝓝[<] t`.
  have hsub : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] 0) (𝓝[<] t) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => t - ε) (𝓝 0) (𝓝 (t - 0)) := tendsto_const_nhds.sub tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp only [mem_Iio]; linarith
  -- For `ε > 0` the average over `Icc (t - ε) t` is `ε⁻¹ ∫_{(t - ε, t)} φ`.
  refine (hleft.comp hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp_apply, average, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioo, show t - (t - ε) = ε by ring,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hε.le, smul_eq_mul]
/-- Tangential gradient of the level cut-off `h_ε = ψ ∘ f`, `ψ(s) = max(0, min(1, (t - s)/ε))`:
`h_ε` is Lipschitz and, wherever `G` is a tangential gradient of `f` vanishing on the level sets
`{f = t - ε}` and `{f = t}`, `G_ε = 1_{t - ε < f < t} · (-ε⁻¹ G)` is a bounded Borel tangential
gradient of `h_ε` (Simon Ch. 6, proof of 4.5(2)). -/
theorem Submission.slicing_im_si_cutoff_tangential_gradient :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (Tan : Eucl P → Submodule ℝ (Eucl P) → Prop) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P) (t ε : ℝ), 0 < ε → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → (∀ᵐ x ∂μ, f x = t - ε → G x = 0) → (∀ᵐ x ∂μ, f x = t → G x = 0) → ∃ K : ℝ≥0, LipschitzWith K (fun x => max 0 (min 1 ((t - f x) / ε))) ∧ Measurable ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) ∧ (∀ x, ‖(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x‖ ≤ K) ∧ ∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → (f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => max 0 (min 1 ((t - f (x + s • u)) / ε))) (inner ℝ ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x) u) 0 := by
  intro P μ Tan f L G t ε hε hf hG hGL hTG h1 h2
  set ψ : ℝ → ℝ := fun s => max 0 (min 1 ((t - s) / ε)) with hψdef
  set Kψ : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.2 hε.le⟩ with hKψ
  -- `ψ` is `ε⁻¹`-Lipschitz: an affine map of slope `-ε⁻¹`, clamped to `[0, 1]`.
  have hψL : LipschitzWith Kψ ψ := by
    have hlin : LipschitzWith Kψ (fun s : ℝ => (t - s) / ε) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, Real.dist_eq, show (t - a) / ε - (t - b) / ε = ε⁻¹ * (b - a) by ring,
        abs_mul, abs_of_pos (inv_pos.2 hε), abs_sub_comm]
      rfl
    exact (hlin.const_min 1).const_max 0
  have hfm : Measurable f := hf.continuous.measurable
  set E : Set (Eucl P) := f ⁻¹' Ioo (t - ε) t with hEdef
  have hE : MeasurableSet E := hfm measurableSet_Ioo
  refine ⟨Kψ * L, hψL.comp hf, (hG.const_smul (-ε⁻¹)).indicator hE, fun x => ?_, ?_⟩
  · -- `‖G_ε x‖ ≤ ε⁻¹ L`
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.2 hε)]
      simp only [hKψ]
      exact mul_le_mul_of_nonneg_left (hGL x) (inv_nonneg.2 hε.le)
    · rw [indicator_of_notMem hx, norm_zero]
      exact NNReal.coe_nonneg _
  · filter_upwards [hTG, h1, h2] with x hx hx1 hx2
    intro Q hQ
    obtain ⟨hGQ, hder⟩ := hx Q hQ
    constructor
    · by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]; exact Q.smul_mem _ hGQ
      · rw [indicator_of_notMem hxE]; exact Q.zero_mem
    intro u hu
    have hd := hder u hu
    have hc : ContinuousAt (fun s : ℝ => f (x + s • u)) 0 := hd.continuousAt
    -- the cut-off composed with the line
    change HasDerivAt (fun s => ψ (f (x + s • u))) _ 0
    -- at points where `G x = 0` the Lipschitz bound gives derivative `0`
    have edge : G x = 0 → HasDerivAt (fun s : ℝ => ψ (f (x + s • u))) 0 (0 : ℝ) := by
      intro hG0
      rw [hG0, inner_zero_left] at hd
      rw [hasDerivAt_iff_isLittleO] at hd ⊢
      simp only [sub_zero, smul_zero] at hd ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
      refine Asymptotics.IsBigO.of_bound (Kψ : ℝ) (Eventually.of_forall fun s => ?_)
      have := hψL.dist_le_mul (f (x + s • u)) (f (x + (0 : ℝ) • u))
      simpa [Real.dist_eq, Real.norm_eq_abs] using this
    -- case analysis on the position of `f x`
    rcases lt_trichotomy (f x) (t - ε) with hlt | heq | hgt
    · -- below the band: locally constant `1`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t - ε := by
        have := hc.eventually_lt (continuousAt_const (y := t - ε)) (by simpa using hlt)
        simpa using this
      apply (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hev] with s hs
      have : 1 ≤ (t - f (x + s • u)) / ε := by rw [le_div_iff₀ hε]; linarith
      simp only [hψdef, min_eq_left this, max_eq_right zero_le_one]
    · -- lower edge: `G x = 0`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      exact edge (hx1 heq)
    · rcases lt_trichotomy (f x) t with hlt' | heq' | hgt'
      · -- inside the band: affine with slope `-1/ε`
        have hxE : x ∈ E := by simp [hEdef]; exact ⟨hgt, hlt'⟩
        rw [indicator_of_mem hxE, real_inner_smul_left]
        have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), t - ε < f (x + s • u) := by
          have := (continuousAt_const (y := t - ε)).eventually_lt hc (by simpa using hgt)
          simpa using this
        have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t := by
          have := hc.eventually_lt (continuousAt_const (y := t)) (by simpa using hlt')
          simpa using this
        have hlin : HasDerivAt (fun s : ℝ => (t - f (x + s • u)) / ε)
            (-ε⁻¹ * inner ℝ (G x) u) 0 := by
          have := (hd.const_sub t).div_const ε
          convert this using 1
          field_simp
        apply hlin.congr_of_eventuallyEq
        filter_upwards [hev1, hev2] with s hs1 hs2
        have ha : (t - f (x + s • u)) / ε ≤ 1 := by rw [div_le_iff₀ hε]; linarith
        have hb : 0 ≤ (t - f (x + s • u)) / ε := div_nonneg (by linarith) hε.le
        simp only [hψdef, min_eq_right ha, max_eq_right hb]
      · -- upper edge: `G x = 0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        exact edge (hx2 heq')
      · -- above the band: locally constant `0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        have hev : ∀ᶠ s in 𝓝 (0 : ℝ), t < f (x + s • u) := by
          have := (continuousAt_const (y := t)).eventually_lt hc (by simpa using hgt')
          simpa using this
        apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hev] with s hs
        have : (t - f (x + s • u)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
        simp only [hψdef, max_eq_left ((min_le_right _ _).trans this)]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
