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

/-- `L¹` comparison of two weighted integrals against a bounded continuous test weight `φ`
vanishing off `B̄_s(x)`, `s ≤ ρ`: with `h = 1_{M₂} θ₂ - c 1_{M₁} θ₁`,
`‖∫_{M₂} φ θ₂ - c ∫_{M₁} φ θ₁‖ₑ ≤ K · ∫⁻_{B̄_s(x)} ‖h‖ₑ`.
Both integrals are integrals of `φ · 1_{M_i} θ_i = φ · 1_{M_i ∩ B̄_ρ(x)} θ_i`, which are
integrable, so the difference is `∫ φ h`, and `‖φ h‖ₑ ≤ 1_{B̄_s(x)} K ‖h‖ₑ` pointwise. -/
theorem Submission.fiw_tl_tr_weighted_diff_bound :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ φ : Eucl P → ℝ) (x : Eucl P) (c ρ s K : ℝ),
      NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) →
      IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
      IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
      Continuous φ → (∀ z, ‖φ z‖ ≤ K) → (∀ z, z ∉ closedBall x s → φ z = 0) → s ≤ ρ →
      ‖(∫ z in M₂, φ z * θ₂ z ∂(μHE[n] : Measure (Eucl P))) -
          c * ∫ z in M₁, φ z * θ₁ z ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal K * ∫⁻ z in closedBall x s,
          ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n M₁ M₂ θ₁ θ₂ φ x c ρ s K hM₁ hM₂ hθ₁ hθ₂ hφ hφK hφs hsρ
  set μ : Measure (Eucl P) := μHE[n]
  -- `φ` vanishes off `B̄_ρ(x) ⊇ B̄_s(x)`.
  have hφρ : ∀ z, z ∉ closedBall x ρ → φ z = 0 := fun z hz =>
    hφs z fun hzs => hz (closedBall_subset_closedBall hsρ hzs)
  -- `∫_M φ θ = ∫ φ · 1_M θ`, and `φ · 1_M θ = φ · 1_{M ∩ B̄_ρ(x)} θ` is integrable.
  have key : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ), NullMeasurableSet M μ →
      IntegrableOn θ (M ∩ closedBall x ρ) μ →
      (∫ z in M, φ z * θ z ∂μ) = ∫ z, φ z * M.indicator θ z ∂μ ∧
        Integrable (fun z => φ z * M.indicator θ z) μ := by
    intro M θ hM hθ
    refine ⟨?_, ?_⟩
    · rw [← integral_indicator₀ hM]
      congr 1
      funext z
      exact indicator_mul_right M φ θ
    · have hint : Integrable ((M ∩ closedBall x ρ).indicator θ) μ :=
        hθ.integrable_indicator₀ (hM.inter measurableSet_closedBall.nullMeasurableSet)
      refine (hint.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hφK)).congr
        (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ closedBall x ρ
      · by_cases hzM : z ∈ M
        · simp [indicator_of_mem hzM, indicator_of_mem (mem_inter hzM hz)]
        · simp [indicator_of_notMem hzM, indicator_of_notMem fun h : z ∈ M ∩ _ => hzM h.1]
      · simp [hφρ z hz]
  obtain ⟨h₁eq, h₁int⟩ := key M₁ θ₁ hM₁ hθ₁
  obtain ⟨h₂eq, h₂int⟩ := key M₂ θ₂ hM₂ hθ₂
  -- Linearity: the difference is `∫ φ · (1_{M₂} θ₂ - c 1_{M₁} θ₁)`.
  have hlin : (∫ z in M₂, φ z * θ₂ z ∂μ) - c * ∫ z in M₁, φ z * θ₁ z ∂μ =
      ∫ z, φ z * (M₂.indicator θ₂ z - c * M₁.indicator θ₁ z) ∂μ := by
    rw [h₁eq, h₂eq, ← integral_const_mul, ← integral_sub h₂int (h₁int.const_mul c)]
    congr 1
    funext z
    ring
  rw [hlin]
  calc ‖∫ z, φ z * (M₂.indicator θ₂ z - c * M₁.indicator θ₁ z) ∂μ‖ₑ
      ≤ ∫⁻ z, ‖φ z * (M₂.indicator θ₂ z - c * M₁.indicator θ₁ z)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z, (closedBall x s).indicator
          (fun z => ENNReal.ofReal K * ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ) z ∂μ := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall x s
        · rw [indicator_of_mem hz, enorm_mul]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hφK z)
        · simp [hφs z hz]
    _ = ∫⁻ z in closedBall x s,
          ENNReal.ofReal K * ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂μ :=
        lintegral_indicator measurableSet_closedBall _
    _ = ENNReal.ofReal K *
          ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
/-- Little-o scaling limit (step 7 of the proof of `fiw_tl_transfer`): if `R > 0`, `E = o(G)`
and `G(s) ≤ C sⁿ` as `s → 0⁺`, and `‖D(r)‖ₑ ≤ (rⁿ)⁻¹ · K · E(R r)` for small `r > 0`, then
`D(r) → 0` as `r → 0⁺`.  With `K₁ = max(K, 0)`, `C₁ = max(C, 0)`, `A = K₁ C₁ Rⁿ` and
`ε' = ε / (2(A + 1))`, for small `r > 0`:
`|D(r)| ≤ (rⁿ)⁻¹ · K₁ · ε' · C₁ (R r)ⁿ = A ε' < ε`. -/
theorem Submission.fiw_tl_tr_scaling_limit :
    ∀ (n : ℕ) (D : ℝ → ℝ) (E G : ℝ → ℝ≥0∞) (R K C : ℝ), 0 < R →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), E s ≤ ENNReal.ofReal ε * G s) →
      (∀ᶠ s in 𝓝[>] (0 : ℝ), G s ≤ ENNReal.ofReal (C * s ^ n)) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ),
        ‖D r‖ₑ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K * E (R * r)) →
      Tendsto D (𝓝[>] 0) (𝓝 0) := by
  intro n D E G R K C hR hE hG hD
  -- `r ↦ R r` maps `𝓝[>] 0` to `𝓝[>] 0`, so (a) and (b) hold at `s = R r` for small `r > 0`.
  have hscale : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hR hr
  -- Nonnegative constants `K₁ ≥ K`, `C₁ ≥ C`, and `ε'` with `A ε' < ε` for `A = K₁ C₁ Rⁿ`.
  obtain ⟨K₁, hKK₁, hK₁⟩ : ∃ K₁ : ℝ, K ≤ K₁ ∧ 0 ≤ K₁ :=
    ⟨max K 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨C₁, hCC₁, hC₁⟩ : ∃ C₁ : ℝ, C ≤ C₁ ∧ 0 ≤ C₁ :=
    ⟨max C 0, le_max_left _ _, le_max_right _ _⟩
  have hA : 0 ≤ K₁ * C₁ * R ^ n := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ K₁ * C₁ * R ^ n * ε' < ε := by
    refine ⟨ε / (2 * (K₁ * C₁ * R ^ n + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  filter_upwards [self_mem_nhdsWithin, hD, hscale.eventually (hE ε' hε'0), hscale.eventually hG]
    with r (hr : 0 < r) hDr hEr hGr
  have hrn : r ^ n ≠ 0 := (pow_pos hr n).ne'
  -- `‖D(r)‖ₑ ≤ ((rⁿ)⁻¹)⁺ K₁⁺ (ε'⁺ (C₁ (R r)ⁿ)⁺) = (A ε')⁺`, using `(R r)ⁿ = Rⁿ rⁿ`.
  have h1 : ‖D r‖ₑ ≤ ENNReal.ofReal (K₁ * C₁ * R ^ n * ε') := by
    calc ‖D r‖ₑ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K * E (R * r) := hDr
      _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K₁ *
          (ENNReal.ofReal ε' * ENNReal.ofReal (C₁ * (R * r) ^ n)) := by
        gcongr
        calc E (R * r) ≤ ENNReal.ofReal ε' * G (R * r) := hEr
          _ ≤ ENNReal.ofReal ε' * ENNReal.ofReal (C₁ * (R * r) ^ n) := by
            gcongr
            exact hGr.trans (ENNReal.ofReal_le_ofReal (by gcongr))
      _ = ENNReal.ofReal ((r ^ n)⁻¹ * K₁ * (ε' * (C₁ * (R * r) ^ n))) := by
        rw [ENNReal.ofReal_mul (p := (r ^ n)⁻¹ * K₁) (by positivity),
          ENNReal.ofReal_mul (p := (r ^ n)⁻¹) (by positivity),
          ENNReal.ofReal_mul (p := ε') hε'0.le]
      _ = ENNReal.ofReal (K₁ * C₁ * R ^ n * ε') := by
        congr 1
        calc (r ^ n)⁻¹ * K₁ * (ε' * (C₁ * (R * r) ^ n))
            = K₁ * C₁ * R ^ n * ε' * ((r ^ n)⁻¹ * r ^ n) := by ring
          _ = K₁ * C₁ * R ^ n * ε' := by rw [inv_mul_cancel₀ hrn, mul_one]
  -- Back to `ℝ`: `|D(r)| ≤ A ε' < ε`.
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  rw [dist_zero_right]
  exact h1.trans_lt hε'
/-- Change of variables under Simon's blow-up `η = η_{x,r}`, `η(z) = r⁻¹(z − x)` (Ch. 3, §1, p. 71),
as used for the locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)): for
`r > 0`, every set `S` and every real function `g`, `∫_{η(S)} g dHⁿ = r⁻ⁿ ∫_S g ∘ η dHⁿ`.
`η` is a homeomorphism (inverse `w ↦ x + r w`) and `η⁻¹(F) = x + r F`, so `Hⁿ(η⁻¹ F) = rⁿ Hⁿ(F)`
by translation invariance and `n`-homogeneity of `Hⁿ`.  Hence `η_# Hⁿ = rⁿ Hⁿ`, and the change of
variables along the measurable embedding `η` needs no integrability. -/
theorem Submission.fiw_tl_blowup_setIntegral :
    ∀ (P n : ℕ) (x : Eucl P) (r : ℝ) (S : Set (Eucl P)) (g : Eucl P → ℝ), 0 < r → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, g y ∂(μHE[n] : Measure (Eucl P)) = (r ^ n)⁻¹ * ∫ z in S, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n x r S g hr
  set η : Eucl P → Eucl P := Poincare.SimonGMT.Chapter03.blowUpMap x r
  have hηapp : ∀ z, η z = r⁻¹ • (z - x) := fun _ => rfl
  -- `η` is a homeomorphism with inverse `w ↦ x + r • w`.
  let e : Eucl P ≃ₜ Eucl P :=
    { toFun := η
      invFun := fun w => x + r • w
      left_inv := fun z => by simp [hηapp, smul_smul, hr.ne']
      right_inv := fun w => by simp [hηapp, smul_smul, hr.ne']
      continuous_toFun := by
        show Continuous fun z : Eucl P => r⁻¹ • (z - x)
        fun_prop
      continuous_invFun := by fun_prop }
  have hemb : MeasurableEmbedding η := e.measurableEmbedding
  have hinj : Function.Injective η := e.injective
  -- `η⁻¹(F) = x + r • F`, so `Hⁿ(η⁻¹ F) = ‖r‖₊ⁿ Hⁿ(F)` for every set `F`.
  have hpre : ∀ F : Set (Eucl P), (μHE[n] : Measure (Eucl P)) (η ⁻¹' F) =
      ‖r‖₊ ^ n • (μHE[n] : Measure (Eucl P)) F := by
    intro F
    have hF : η ⁻¹' F = (fun z => z + -x) ⁻¹' ((fun w => r⁻¹ • w) ⁻¹' F) := by
      ext z
      simp only [mem_preimage, hηapp, sub_eq_add_neg]
    rw [hF, measure_preimage_add_right, preimage_smul_inv₀ hr.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne']
  -- Push-forward: `η_# Hⁿ = ‖r‖₊ⁿ Hⁿ`.
  have hmap : Measure.map η (μHE[n] : Measure (Eucl P)) =
      (‖r‖₊ ^ n) • (μHE[n] : Measure (Eucl P)) := by
    ext F hF
    rw [Measure.map_apply hemb.measurable hF, Measure.smul_apply, hpre]
  -- Change of variables along the measurable embedding `η` (no integrability needed).
  have h := hemb.setIntegral_map (μ := (μHE[n] : Measure (Eucl P))) g (η '' S)
  rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure, preimage_image_eq S hinj,
    NNReal.smul_def, smul_eq_mul] at h
  have hc : ((‖r‖₊ ^ n : ℝ≥0) : ℝ) = r ^ n := by
    rw [NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg hr.le]
  rw [hc] at h
  rw [← h, inv_mul_cancel_left₀ (pow_ne_zero n hr.ne')]

/-- Simon Ch. 3, 1.7: if `M` has weighted approximate tangent space `Q` at `x` and `θ ≥ 0` is
`Hⁿ`-integrable on `M ∩ B̄_ρ(x)`, then `∫_{M ∩ B̄_s(x)} θ dHⁿ ≤ C sⁿ` for all small `s > 0`.
Test with the cut-off `f₀ = max 0 (min 1 (2 - ‖·‖))` (`= 1` on `B̄₁(0)`, `= 0` off `B₂(0)`): by
`fiw_tl_blowup_setIntegral` the tangent integrals equal `s⁻ⁿ ∫_M f₀(η_s z) θ(z) dHⁿ(z)`, which
dominate `s⁻ⁿ ∫_{M ∩ B̄_s(x)} θ dHⁿ` and converge as `s ↓ 0`. -/
theorem Submission.fiw_tl_growth_bound :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (ρ : ℝ)
      (Q : Submodule ℝ (Eucl P)), 0 < ρ → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) →
      (∀ y ∈ M, 0 ≤ θ y) → IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
      HasWeightedApproximateTangentSpaceAt n M θ x Q → ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂(μHE[n] : Measure (Eucl P)) ≤
          ENNReal.ofReal (C * s ^ n) := by
  intro P n M θ x ρ Q hρ hM hθ hθi hT
  -- Step 1: the cut-off `f₀ ∈ C_c(ℝ^P)`: `f₀ = 1` on `B̄₁(0)`, `f₀ = 0` off `B₂(0)`, `0 ≤ f₀ ≤ 1`.
  obtain ⟨f₀, hf₀0, hf₀1, hf₀nn, hf₀le⟩ : ∃ f₀ : CompactlySupportedContinuousMap (Eucl P) ℝ,
      (∀ y, 2 ≤ ‖y‖ → f₀ y = 0) ∧ (∀ y, ‖y‖ ≤ 1 → f₀ y = 1) ∧ (∀ y, 0 ≤ f₀ y) ∧
        ∀ y, f₀ y ≤ 1 := by
    have h0 : ∀ y : Eucl P, 2 ≤ ‖y‖ → max 0 (min 1 (2 - ‖y‖)) = 0 := fun y hy =>
      max_eq_left (min_le_of_right_le (by linarith))
    refine ⟨⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)),
        continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) fun y hy =>
        h0 y (not_le.1 fun h => hy (mem_closedBall_zero_iff.2 h)).le⟩, h0, fun y hy => ?_,
      fun y => le_max_left _ _, fun y => max_le zero_le_one (min_le_left _ _)⟩
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 2: `I(s) → L := θ(x) ∫_Q f₀ dHⁿ` as `s ↓ 0`, so `I(s) < C := |L| + 1` for small `s`.
  refine ⟨|θ x * ∫ y in (Q : Set (Eucl P)), f₀ y ∂(μHE[n] : Measure (Eucl P))| + 1, ?_⟩
  filter_upwards [(hT.2 f₀).eventually (gt_mem_nhds ((le_abs_self _).trans_lt (lt_add_one _))),
    Ioo_mem_nhdsGT (half_pos hρ)] with s hIs hs
  obtain ⟨hs0, hsρ⟩ := hs
  -- Step 3: `I(s) = s⁻ⁿ ∫_M F dHⁿ`, `F z = f₀(η_s z) θ(z)`, since `x + s η_s(z) = z`.
  have hη : ∀ z, Poincare.SimonGMT.Chapter03.blowUpMap x s z = s⁻¹ • (z - x) := fun z => rfl
  have hxη : ∀ z, x + s • Poincare.SimonGMT.Chapter03.blowUpMap x s z = z := fun z => by
    rw [hη, smul_inv_smul₀ hs0.ne', add_sub_cancel]
  have hcv := Submission.fiw_tl_blowup_setIntegral P n x s M (fun y => f₀ y * θ (x + s • y)) hs0
  simp only [hxη] at hcv
  -- Step 4: `F = 0` off `B̄_ρ(x)` (as `2s < ρ`) and `F = θ` on `B̄_s(x)`.
  have hnη : ∀ z, ‖Poincare.SimonGMT.Chapter03.blowUpMap x s z‖ = dist z x / s := fun z => by
    rw [hη, norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, dist_eq_norm, inv_mul_eq_div]
  have hF0 : ∀ z, z ∉ closedBall x ρ →
      f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z = 0 := fun z hz => by
    rw [mem_closedBall, not_le] at hz
    rw [hf₀0 _ (by rw [hnη, le_div_iff₀ hs0]; linarith), zero_mul]
  have hF1 : ∀ z ∈ closedBall x s,
      f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z = θ z := fun z hz => by
    rw [hf₀1 _ (by rw [hnη, div_le_one hs0]; exact hz), one_mul]
  -- Step 5: `F` is integrable on `M`: bounded continuous times `θ` on `M ∩ B̄_ρ(x)`, zero off it.
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x s) := by
    show Continuous fun z => s⁻¹ • (z - x)
    fun_prop
  have hFρ : IntegrableOn (fun z => f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z)
      (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) :=
    Integrable.bdd_mul (c := 1) hθi (f₀.continuous.comp hηc).aestronglyMeasurable
      (Eventually.of_forall fun z => (Real.norm_of_nonneg (hf₀nn _)).trans_le (hf₀le _))
  have hFi : IntegrableOn (fun z => f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z) M
      (μHE[n] : Measure (Eucl P)) :=
    hFρ.of_ae_sdiff_eq_zero hM (Eventually.of_forall fun z hz => hF0 z fun h => hz.2 ⟨hz.1, h⟩)
  -- Steps 6–7: `∫_{M ∩ B̄_s(x)} θ = ∫_{M ∩ B̄_s(x)} F ≤ ∫_M F = sⁿ I(s) ≤ C sⁿ`.
  have hMs : NullMeasurableSet (M ∩ closedBall x s) (μHE[n] : Measure (Eucl P)) :=
    hM.inter measurableSet_closedBall.nullMeasurableSet
  have hθs : IntegrableOn θ (M ∩ closedBall x s) (μHE[n] : Measure (Eucl P)) :=
    hθi.mono_set (inter_subset_inter_right _ (closedBall_subset_closedBall (by linarith)))
  rw [← ofReal_integral_eq_lintegral_ofReal hθs
    (by filter_upwards [ae_restrict_mem₀ hMs] with z hz using hθ z hz.1)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ z in M ∩ closedBall x s, θ z ∂(μHE[n] : Measure (Eucl P))
      = ∫ z in M ∩ closedBall x s, f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z
          ∂(μHE[n] : Measure (Eucl P)) :=
        setIntegral_congr_fun₀ hMs fun z hz => (hF1 z hz.2).symm
    _ ≤ ∫ z in M, f₀ (Poincare.SimonGMT.Chapter03.blowUpMap x s z) * θ z
          ∂(μHE[n] : Measure (Eucl P)) :=
        setIntegral_mono_set hFi (by
          filter_upwards [ae_restrict_mem₀ hM] with z hz using mul_nonneg (hf₀nn _) (hθ z hz))
          inter_subset_left.eventuallyLE
    _ = s ^ n * ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x s '' M, f₀ y * θ (x + s • y)
          ∂(μHE[n] : Measure (Eucl P)) := by
        rw [hcv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs0.ne'), one_mul]
    _ ≤ s ^ n * (|θ x * ∫ y in (Q : Set (Eucl P)), f₀ y ∂(μHE[n] : Measure (Eucl P))| + 1) :=
        mul_le_mul_of_nonneg_left hIs.le (pow_nonneg hs0.le _)
    _ = _ := mul_comm _ _

/-- Simon Ch. 3, Remarks 1.5(2), 1.8(1): pointwise transfer of a weighted approximate tangent
space.  If `θ₂(x) = c θ₁(x)` and `h = 1_{M₂}θ₂ − c 1_{M₁}θ₁` is `o(∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ)` in
`L¹(B̄_s(x))` as `s ↓ 0`, then every tangent space `Q` of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.
For `f ∈ C_c(ℝ^P)` (`f = 0` off `B_R(0)`, `|f| ≤ K`) the tangent integrals are
`I_i(r) = r⁻ⁿ ∫_{M_i} f(η_r z) θ_i(z) dHⁿ(z)` by `fiw_tl_blowup_setIntegral`, so
`|I₂(r) − c I₁(r)| ≤ r⁻ⁿ K ∫_{B̄_{Rr}(x)} |h| dHⁿ` (`fiw_tl_tr_weighted_diff_bound`), which tends
to `0` by `fiw_tl_growth_bound` and `fiw_tl_tr_scaling_limit`.  Hence
`I₂(r) → c θ₁(x) ∫_Q f dHⁿ = θ₂(x) ∫_Q f dHⁿ`. -/
theorem Submission.fiw_tl_transfer :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (x : Eucl P) (c ρ : ℝ), 0 < ρ → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M₁, 0 ≤ θ₁ y) → IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → θ₂ x = c * θ₁ x → (∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal ε * ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q := by
  intro P n M₁ M₂ θ₁ θ₂ x c ρ hρ hM₁ hM₂ hθ₁ hθ₁i hθ₂i hx hsmall Q hT
  -- Step 2: `∫⁻_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ ≤ C₀ sⁿ` for all small `s > 0`.
  obtain ⟨C₀, hC₀⟩ := Submission.fiw_tl_growth_bound P n M₁ θ₁ x ρ Q hρ hM₁ hθ₁ hθ₁i hT
  -- Step 1: `finrank Q = n` is inherited; fix `f ∈ C_c(ℝ^P)`.
  refine ⟨hT.1, fun f => ?_⟩
  -- Step 3: `f = 0` off `B_R(0)` and `‖f‖ ≤ K`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨K, hK⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  -- Steps 4–7: `D(r) := I₂(r) − c I₁(r) → 0` as `r ↓ 0`.
  have hD : Tendsto (fun r : ℝ =>
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M₂, f y * θ₂ (x + r • y)
        ∂(μHE[n] : Measure (Eucl P))) -
      c * ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M₁, f y * θ₁ (x + r • y)
        ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
    refine Submission.fiw_tl_tr_scaling_limit n _
      (fun s => ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ
        ∂(μHE[n] : Measure (Eucl P)))
      (fun s => ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P)))
      R K C₀ hR hsmall hC₀ ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    obtain ⟨hr0, hrρ⟩ := hr
    have hRr : R * r ≤ ρ := by
      rw [lt_div_iff₀ hR, mul_comm] at hrρ
      exact hrρ.le
    -- `η_r(z) = r⁻¹(z − x)`: `x + r η_r(z) = z` and `‖η_r(z)‖ = |z − x| / r`.
    have hη : ∀ z, Poincare.SimonGMT.Chapter03.blowUpMap x r z = r⁻¹ • (z - x) := fun z => rfl
    have hxη : ∀ z, x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r z = z := fun z => by
      rw [hη, smul_inv_smul₀ hr0.ne', add_sub_cancel]
    have hnη : ∀ z, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = dist z x / r := fun z => by
      rw [hη, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le, dist_eq_norm, inv_mul_eq_div]
    have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
      show Continuous fun z => r⁻¹ • (z - x)
      fun_prop
    -- Step 4: `I_i(r) = r⁻ⁿ ∫_{M_i} f(η_r z) θ_i(z) dHⁿ(z)`.
    have hcv₁ := Submission.fiw_tl_blowup_setIntegral P n x r M₁
      (fun y => f y * θ₁ (x + r • y)) hr0
    have hcv₂ := Submission.fiw_tl_blowup_setIntegral P n x r M₂
      (fun y => f y * θ₂ (x + r • y)) hr0
    simp only [hxη] at hcv₁ hcv₂
    -- Steps 5–6: the weight `f ∘ η_r` is continuous, bounded by `K` and `0` off `B̄_{Rr}(x)`.
    have hA := Submission.fiw_tl_tr_weighted_diff_bound P n M₁ M₂ θ₁ θ₂
      (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) x c ρ (R * r) K hM₁ hM₂ hθ₁i
      hθ₂i (f.continuous.comp hηc) (fun z => hK _) (fun z hz => hfR _ (by
        rw [mem_closedBall, not_le] at hz
        rw [hnη, le_div_iff₀ hr0]
        exact hz.le)) hRr
    rw [hcv₁, hcv₂, mul_left_comm c, ← mul_sub, enorm_mul,
      Real.enorm_eq_ofReal (inv_nonneg.2 (pow_nonneg hr0.le n)), mul_assoc]
    exact mul_le_mul_of_nonneg_left hA zero_le
  -- Step 8: `c I₁(r) → c θ₁(x) ∫_Q f dHⁿ = θ₂(x) ∫_Q f dHⁿ`, so `I₂(r) = D(r) + c I₁(r)` converges.
  have h := hD.add ((hT.2 f).const_mul c)
  rw [zero_add, ← mul_assoc, ← hx] at h
  exact h.congr fun r => sub_add_cancel _ _
/-- Reduction of an almost-everywhere property to balls: if `Φ` holds `μ ⌞ (A ∩ B_r(y))`-a.e.
for every ball with `B̄_r(y) ⊆ U`, then `Φ` holds `μ ⌞ A`-a.e. for `A ⊆ U`, `U` open.  Countably
many such balls cover `A` (`ℝ^P` is second countable), and `μ ⌞ A`-a.e. is checked on the
pieces of a countable cover without any measurability assumption. -/
theorem Submission.fiw_tl_ald_ball_reduction :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (U A : Set (Eucl P)) (Φ : Eucl P → Prop), IsOpen U →
      A ⊆ U → (∀ (y : Eucl P) (r : ℝ), closedBall y r ⊆ U →
        ∀ᵐ x ∂(μ.restrict (A ∩ ball y r)), Φ x) → ∀ᵐ x ∂(μ.restrict A), Φ x := by
  intro P μ U A Φ hU hAU hball
  -- The balls `B_r(y)` with `B̄_r(y) ⊆ U`, indexed by `ι`; a countable subfamily `T` has the
  -- same union.
  let ι := {p : Eucl P × ℝ // closedBall p.1 p.2 ⊆ U}
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : ι => ball i.1.1 i.1.2) fun i => isOpen_ball
  -- `A = ⋃_{i ∈ T} (A ∩ B_i)`: each `x ∈ A ⊆ U` lies in `B_{δ/2}(x)`, and
  -- `B̄_{δ/2}(x) ⊆ B_δ(x) ⊆ U`.
  have hA : A = ⋃ i ∈ T, A ∩ ball i.1.1 i.1.2 := by
    rw [← inter_iUnion₂, hT, eq_comm, inter_eq_left]
    intro x hx
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x (hAU hx)
    exact mem_iUnion.2 ⟨⟨(x, δ / 2), (closedBall_subset_ball (half_lt_self hδ)).trans hδU⟩,
      mem_ball_self (half_pos hδ)⟩
  rw [hA, ae_restrict_biUnion_iff _ hTc]
  exact fun i _ => hball i.1.1 i.1.2 i.2
/-- Weighted Lebesgue points (for the locality of weighted approximate tangent spaces, Simon
Ch. 3, 1.5(2), 1.8(1)).  Let `M ⊆ ℝ^P` be `μ`-null-measurable, `θ > 0` on `M`, and `θ`, `θ f`
`μ`-integrable on `M ∩ B̄_r(y)`.  Then for `μ`-a.e. `x ∈ M ∩ B_r(y)`,
`∫_{M ∩ B̄_s(x)} θ |f - f(x)| dμ / ∫_{M ∩ B̄_s(x)} θ dμ → 0` as `s ↓ 0`.  The measure
`ν = θ⁺ μ ⌞ (M ∩ B̄_r(y))` is finite, `μ ⌞ (M ∩ B̄_r(y)) ≪ ν` as `θ > 0` on `M`, and `f ∈ L¹(ν)`
as `θ f ∈ L¹(μ ⌞ (M ∩ B̄_r(y)))`.  So the Lebesgue differentiation theorem for `ν` along closed
balls (Simon Ch. 1, 3.17; `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` for
`Besicovitch.vitaliFamily ν`) holds `μ ⌞ (M ∩ B_r(y))`-a.e.; for `0 < s < r - |x - y|`,
`B̄_s(x) ⊆ B̄_r(y)`, so the two `ν`-integrals over `B̄_s(x)` are the two integrals above. -/
theorem Submission.fiw_tl_ald_ld_weighted_lebesgue_point :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (M : Set (Eucl P)) (θ f : Eucl P → ℝ) (y : Eucl P) (r : ℝ),
      NullMeasurableSet M μ → (∀ z ∈ M, 0 < θ z) → IntegrableOn θ (M ∩ closedBall y r) μ →
      IntegrableOn (fun z => θ z * f z) (M ∩ closedBall y r) μ →
      ∀ᵐ x ∂(μ.restrict (M ∩ ball y r)),
        Tendsto (fun s : ℝ =>
          (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) * ‖f z - f x‖ₑ ∂μ) /
            (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ)) (𝓝[>] 0) (𝓝 0) := by
  intro P μ M θ f y r hM hpos hθ hθf
  -- Step 1: `S = M ∩ B̄_r(y)` and `M ∩ B_r(y)` are `μ`-null-measurable.
  have hS : NullMeasurableSet (M ∩ closedBall y r) μ :=
    hM.inter measurableSet_closedBall.nullMeasurableSet
  have hMB : NullMeasurableSet (M ∩ ball y r) μ :=
    hM.inter measurableSet_ball.nullMeasurableSet
  set μS := μ.restrict (M ∩ closedBall y r) with hμS
  set ν := μS.withDensity (fun z => ENNReal.ofReal (θ z)) with hν
  -- Step 2: `ν = (μ ⌞ S).withDensity θ⁺` is finite, since `θ` is integrable on `S`.
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hθ.2
  -- Step 3: `μ ⌞ S ≪ ν`, since `θ > 0` on `M`.
  have hθm : AEMeasurable (fun z => ENNReal.ofReal (θ z)) μS :=
    hθ.1.aemeasurable.ennreal_ofReal
  have hmemS : ∀ᵐ z ∂μS, z ∈ M ∩ closedBall y r := ae_restrict_mem₀ hS
  have hac : μS ≪ ν := by
    refine withDensity_absolutelyContinuous' hθm ?_
    filter_upwards [hmemS] with z hz
    exact (ENNReal.ofReal_pos.2 (hpos z hz.1)).ne'
  -- Step 4: `f ∈ L¹(ν)`, since `θ.toNNReal • f = θ f` on `S`; hence `f` is `μ ⌞ S`-measurable.
  have hfν : Integrable f ν := by
    have hnn : AEMeasurable (fun z => (θ z).toNNReal) μS :=
      hθ.1.aemeasurable.real_toNNReal
    have hνeq : ν = μS.withDensity (fun z => ((θ z).toNNReal : ℝ≥0∞)) := rfl
    rw [hνeq, integrable_withDensity_iff_integrable_smul₀ hnn]
    refine hθf.congr ?_
    filter_upwards [hmemS] with z hz
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hpos z hz.1).le, smul_eq_mul]
  have hfS : AEStronglyMeasurable f μS := hfν.1.mono_ac hac
  -- Step 5: Lebesgue differentiation for `ν` along closed balls.
  have hLeb : ∀ᵐ x ∂ν, Tendsto (fun s : ℝ =>
      (∫⁻ z in closedBall x s, ‖f z - f x‖ₑ ∂ν) / ν (closedBall x s)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_lintegral_enorm_sub_div
      hfν.locallyIntegrable] with x hx
    exact hx.comp (Besicovitch.tendsto_filterAt ν x)
  -- Step 6: transfer to `μ ⌞ (M ∩ B_r(y)) ≤ μ ⌞ S ≪ ν`.
  have hlam : μ.restrict (M ∩ ball y r) ≪ ν :=
    (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (inter_subset_inter_right M ball_subset_closedBall) le_rfl)).trans hac
  filter_upwards [hlam.ae_le hLeb, ae_restrict_mem₀ hMB] with x hx hxmem
  -- Step 7: for `0 < s < r - dist x y`, `B̄_s(x) ⊆ B̄_r(y)` and the two quotients agree.
  refine hx.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (mem_ball.1 hxmem.2))] with s hs
  have hsub : closedBall x s ⊆ closedBall y r :=
    closedBall_subset_closedBall' (by linarith [hs.2])
  have hinter : closedBall x s ∩ (M ∩ closedBall y r) = M ∩ closedBall x s := by
    ext z
    exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hsub hz.2⟩⟩
  have hgm : AEMeasurable (fun z => ‖f z - f x‖ₑ) μS :=
    (hfS.sub aestronglyMeasurable_const).enorm
  have hnum : ∫⁻ z in closedBall x s, ‖f z - f x‖ₑ ∂ν =
      ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) * ‖f z - f x‖ₑ ∂μ := by
    rw [hν, setLIntegral_withDensity_eq_lintegral_mul₀ hθm hgm measurableSet_closedBall,
      hμS, Measure.restrict_restrict measurableSet_closedBall, hinter]
    rfl
  have hden : ν (closedBall x s) = ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ := by
    rw [hν, withDensity_apply _ measurableSet_closedBall, hμS,
      Measure.restrict_restrict measurableSet_closedBall, hinter]
  rw [hnum, hden]
/-- Weighted density points (for the locality of weighted approximate tangent spaces, Simon
Ch. 3, 1.5(2), 1.8(1)).  Let `M, E ⊆ ℝ^P` be `μ`-null-measurable with `E ⊆ M`, `θ > 0` on `M` and
`θ` `μ`-integrable on `M ∩ B̄_r(y)`.  Then for `μ`-a.e. `x ∈ E ∩ B_r(y)`,
`∫_{E ∩ B̄_s(x)} θ dμ / ∫_{M ∩ B̄_s(x)} θ dμ → 1` as `s ↓ 0`.  The measure
`ν = θ⁺ μ ⌞ (M ∩ B̄_r(y))` is finite and `μ ⌞ (M ∩ B̄_r(y)) ≪ ν` as `θ > 0` on `M`, so
`μ ⌞ (E ∩ B_r(y)) ≪ ν ⌞ E` and the Besicovitch density theorem for `ν` and `E`
(`Besicovitch.ae_tendsto_measure_inter_div`) applies; for `0 < s < r - |x - y|`,
`B̄_s(x) ⊆ B̄_r(y)`, so `ν(E ∩ B̄_s(x))` and `ν(B̄_s(x))` are the two integrals. -/
theorem Submission.fiw_tl_ald_ld_weighted_density_point :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (M E : Set (Eucl P)) (θ : Eucl P → ℝ) (y : Eucl P) (r : ℝ),
      NullMeasurableSet M μ → NullMeasurableSet E μ → E ⊆ M → (∀ z ∈ M, 0 < θ z) →
      IntegrableOn θ (M ∩ closedBall y r) μ →
      ∀ᵐ x ∂(μ.restrict (E ∩ ball y r)),
        Tendsto (fun s : ℝ => (∫⁻ z in E ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ) /
          (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ)) (𝓝[>] 0) (𝓝 1) := by
  intro P μ M E θ y r hM hE hEM hθ hint
  -- Step 1: null-measurability of `S = M ∩ B̄_r(y)` and of `E` for `μ ⌞ S`.
  have hS : NullMeasurableSet (M ∩ closedBall y r) μ :=
    hM.inter measurableSet_closedBall.nullMeasurableSet
  have hES : NullMeasurableSet E (μ.restrict (M ∩ closedBall y r)) :=
    hE.mono Measure.restrict_le_self
  -- Step 2: `ν = (μ ⌞ S).withDensity θ⁺` is finite, since `θ` is integrable on `S`.
  have : IsFiniteMeasure ((μ.restrict (M ∩ closedBall y r)).withDensity
      fun z => ENNReal.ofReal (θ z)) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  -- Step 3: `μ ⌞ S ≪ ν`, since `θ > 0` on `M`.
  have hac : μ.restrict (M ∩ closedBall y r) ≪ (μ.restrict (M ∩ closedBall y r)).withDensity
      fun z => ENNReal.ofReal (θ z) := by
    refine withDensity_absolutelyContinuous' hint.1.aemeasurable.ennreal_ofReal ?_
    filter_upwards [ae_restrict_mem₀ hS] with z hz
    exact (ENNReal.ofReal_pos.2 (hθ z hz.1)).ne'
  -- Step 4: `μ ⌞ (E ∩ B_r(y)) ≤ (μ ⌞ S) ⌞ E ≪ ν ⌞ E`.
  have hle : μ.restrict (E ∩ ball y r) ≤ (μ.restrict (M ∩ closedBall y r)).restrict E := by
    rw [Measure.restrict_restrict₀ hES]
    refine Measure.restrict_mono ?_ le_rfl
    intro z hz
    exact ⟨hz.1, hEM hz.1, ball_subset_closedBall hz.2⟩
  have hlam : μ.restrict (E ∩ ball y r) ≪ ((μ.restrict (M ∩ closedBall y r)).withDensity
      fun z => ENNReal.ofReal (θ z)).restrict E :=
    (Measure.absolutelyContinuous_of_le hle).trans (hac.restrict E)
  -- Step 5: the Besicovitch density theorem for `ν` and `E`, transferred to `μ ⌞ (E ∩ B_r(y))`.
  filter_upwards [hlam.ae_le (Besicovitch.ae_tendsto_measure_inter_div _ E),
    ae_restrict_mem₀ (hE.inter measurableSet_ball.nullMeasurableSet)] with x hx hxE
  -- Step 6: for `0 < s < r - dist x y`, `B̄_s(x) ⊆ B̄_r(y)` and the two quotients agree.
  refine hx.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (mem_ball.1 hxE.2))] with s hs
  have hsub : closedBall x s ⊆ closedBall y r :=
    closedBall_subset_closedBall' (by linarith [hs.2])
  have hEs : NullMeasurableSet (E ∩ closedBall x s) (μ.restrict (M ∩ closedBall y r)) :=
    hES.inter measurableSet_closedBall.nullMeasurableSet
  have hE' : E ∩ closedBall x s ∩ (M ∩ closedBall y r) = E ∩ closedBall x s :=
    inter_eq_left.2 fun z hz => ⟨hEM hz.1, hsub hz.2⟩
  have hM' : closedBall x s ∩ (M ∩ closedBall y r) = M ∩ closedBall x s := by
    ext z
    exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hsub hz.2⟩⟩
  rw [withDensity_apply₀ _ hEs, Measure.restrict_restrict₀ hEs, hE',
    withDensity_apply _ measurableSet_closedBall,
    Measure.restrict_restrict measurableSet_closedBall, hM']
/-- Lebesgue differentiation along closed balls: for a finite measure `ν` on `ℝ^P` and
`g ∈ L¹(ν)`, `ν`-a.e. `x` satisfies `⨍_{B̄_s(x)} |g - g(x)| dν → 0` as `s → 0⁺`.  The closed balls
`B̄_s(x)` form the Besicovitch Vitali family of `ν` (`ℝ^P` has the Besicovitch covering property),
along which every locally integrable function has Lebesgue points `ν`-a.e. -/
theorem Submission.fiw_tl_ald_closedBall_lebesgue_point :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) [IsFiniteMeasure ν] (g : Eucl P → ℝ), Integrable g ν →
      ∀ᵐ x ∂ν, Tendsto (fun s : ℝ => (∫⁻ z in closedBall x s, ‖g z - g x‖ₑ ∂ν) /
        ν (closedBall x s)) (𝓝[>] 0) (𝓝 0) := by
  intro P ν _ g hg
  filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_lintegral_enorm_sub_div
    hg.locallyIntegrable] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt ν x)

/-- Local differentiation on a ball: let `θᵢ > 0` on `Mᵢ` be `Hⁿ`-integrable on `Mᵢ ∩ B̄_r(y)` and
`g = 1_{M₁ ∩ M₂} θ₂/θ₁`.  For `Hⁿ ⌞ (M₁ ∩ M₂ ∩ B_r(y))`-a.e. `x`, as `s → 0⁺`, `x` is a Lebesgue
point of `g` for `θ₁ Hⁿ ⌞ M₁` and `M₁ ∩ M₂` has density `1` at `x` for `θ₂ Hⁿ ⌞ M₂`, both along
the closed balls `B̄_s(x)`.  Since `θ₁ g = 1_{M₁ ∩ M₂} θ₂` is integrable on `M₁ ∩ B̄_r(y)`, these
are the weighted Lebesgue-point lemma for `(M₁, θ₁, g)`, with `g(x) = θ₂(x)/θ₁(x)` on `M₁ ∩ M₂`,
and the weighted density lemma for `M₁ ∩ M₂ ⊆ M₂`. -/
theorem Submission.fiw_tl_ald_local_differentiation :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (y : Eucl P) (r : ℝ),
      NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ z ∈ M₁, 0 < θ₁ z) →
      (∀ z ∈ M₂, 0 < θ₂ z) → IntegrableOn θ₁ (M₁ ∩ closedBall y r) (μHE[n] : Measure (Eucl P)) →
      IntegrableOn θ₂ (M₂ ∩ closedBall y r) (μHE[n] : Measure (Eucl P)) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂ ∩ ball y r)),
        Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) *
            ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - θ₂ x / θ₁ x‖ₑ
              ∂(μHE[n] : Measure (Eucl P))) /
          (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))))
          (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z)
            ∂(μHE[n] : Measure (Eucl P))) /
          (∫⁻ z in M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z) ∂(μHE[n] : Measure (Eucl P))))
          (𝓝[>] 0) (𝓝 1) := by
  intro P n M₁ M₂ θ₁ θ₂ y r hM₁ hM₂ hθ₁ hθ₂ hθ₁i hθ₂i
  -- `θ₁ g = 1_{M₁ ∩ M₂} θ₂` (as `θ₁ > 0` on `M₁`), which is integrable on `M₁ ∩ B̄_r(y)` because
  -- `θ₂` is integrable on `M₂ ∩ B̄_r(y)`.
  have hθ₁g : IntegrableOn (fun z => θ₁ z * (M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z)
      (M₁ ∩ closedBall y r) (μHE[n] : Measure (Eucl P)) := by
    have h : (fun z => θ₁ z * (M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z) =
        (M₁ ∩ M₂).indicator θ₂ := by
      funext z
      by_cases hz : z ∈ M₁ ∩ M₂
      · rw [indicator_of_mem hz, indicator_of_mem hz, mul_div_cancel₀ _ (hθ₁ z hz.1).ne']
      · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]
    rw [h, integrableOn_indicator_iff (hM₁.inter hM₂)]
    exact hθ₂i.mono_set fun z hz => ⟨hz.1.2, hz.2.2⟩
  -- (L) holds a.e. on `M₁ ∩ B_r(y) ⊇ M₁ ∩ M₂ ∩ B_r(y)` and (D) a.e. on `M₁ ∩ M₂ ∩ B_r(y)`.
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun z hz => ⟨hz.1.1, hz.2⟩ : M₁ ∩ M₂ ∩ ball y r ⊆ M₁ ∩ ball y r)
      (Submission.fiw_tl_ald_ld_weighted_lebesgue_point P (μHE[n] : Measure (Eucl P)) M₁ θ₁
        ((M₁ ∩ M₂).indicator fun w => θ₂ w / θ₁ w) y r hM₁ hθ₁ hθ₁i hθ₁g),
    Submission.fiw_tl_ald_ld_weighted_density_point P (μHE[n] : Measure (Eucl P)) M₂ (M₁ ∩ M₂)
      θ₂ y r hM₂ (hM₁.inter hM₂) inter_subset_right hθ₂ hθ₂i,
    ae_restrict_mem₀ ((hM₁.inter hM₂).inter measurableSet_ball.nullMeasurableSet)]
    with x hL hD hx
  -- At `x ∈ M₁ ∩ M₂`, `g(x) = θ₂(x)/θ₁(x)`.
  have hgx : (M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) x = θ₂ x / θ₁ x :=
    indicator_of_mem hx.1 _
  rw [hgx] at hL
  exact ⟨hL, hD⟩
/-- Relative `L¹` estimate at a point.  Let `θᵢ > 0` on `Mᵢ` be `Hⁿ`-integrable on
`Mᵢ ∩ B̄_ρ(x)`, `x ∈ M₁ ∩ M₂`, `c = θ₂(x)/θ₁(x)` and `g = 1_{M₁ ∩ M₂} θ₂/θ₁`.  If, as `s ↓ 0`,
(L) `∫_{M₁ ∩ B̄_s(x)} θ₁ |g − c| dHⁿ / ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ → 0` and
(D) `∫_{M₁ ∩ M₂ ∩ B̄_s(x)} θ₂ dHⁿ / ∫_{M₂ ∩ B̄_s(x)} θ₂ dHⁿ → 1`, then for every `ε > 0` and all
small `s > 0`, `∫_{B̄_s(x)} |1_{M₂} θ₂ − c 1_{M₁} θ₁| dHⁿ ≤ ε ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ`.
Pointwise `|1_{M₂} θ₂ − c 1_{M₁} θ₁| = 1_{M₁} θ₁ |g − c| + 1_{M₂ ∖ M₁} θ₂`.  With
`bᵢ = ∫_{Mᵢ ∩ B̄_s(x)} θᵢ dHⁿ`, (L) bounds the first part by `δ b₁` and (D) bounds the second by
`δ b₂ ≤ 2δ(c + δ) b₁`. -/
theorem Submission.fiw_tl_ald_pointwise_estimate :
    ∀ (P n : ℕ) (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (x : Eucl P),
      NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) →
      (∀ z ∈ M₁, 0 < θ₁ z) → (∀ z ∈ M₂, 0 < θ₂ z) → x ∈ M₁ ∩ M₂ →
      (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ₁ (M₁ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧
        IntegrableOn θ₂ (M₂ ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) →
      Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) *
          ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - θ₂ x / θ₁ x‖ₑ
            ∂(μHE[n] : Measure (Eucl P))) /
        (∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P))))
        (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun s : ℝ => (∫⁻ z in M₁ ∩ M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z)
            ∂(μHE[n] : Measure (Eucl P))) /
        (∫⁻ z in M₂ ∩ closedBall x s, ENNReal.ofReal (θ₂ z) ∂(μHE[n] : Measure (Eucl P))))
        (𝓝[>] 0) (𝓝 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ∫⁻ z in closedBall x s, ‖M₂.indicator θ₂ z - θ₂ x / θ₁ x * M₁.indicator θ₁ z‖ₑ
            ∂(μHE[n] : Measure (Eucl P)) ≤
          ENNReal.ofReal ε *
            ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n M₁ M₂ θ₁ θ₂ x hM₁ hM₂ hθ₁ hθ₂ hx hint hL hD ε hε
  obtain ⟨ρ, hρ, hi₁, hi₂⟩ := hint
  generalize (μHE[n] : Measure (Eucl P)) = H at hM₁ hM₂ hi₁ hi₂ hL hD ⊢
  have hc : 0 < θ₂ x / θ₁ x := div_pos (hθ₂ x hx.2) (hθ₁ x hx.1)
  generalize θ₂ x / θ₁ x = c at hc hL ⊢
  -- `δ = min(1/2, ε/(3c+3))`: `0 < δ ≤ 1/2` and `δ(3c+3) ≤ ε`.
  obtain ⟨δ, hδ, hδ2, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ * (3 * c + 3) ≤ ε :=
    ⟨min (1 / 2) (ε / (3 * c + 3)), lt_min (by norm_num) (div_pos hε (by linarith)),
      min_le_left _ _, (le_div_iff₀ (by linarith)).1 (min_le_right _ _)⟩
  -- Eventually `s < ρ`, `a₂/b₂ > 1 − δ` (by (D)) and `I/b₁ < δ` (by (L)).
  filter_upwards [Ioo_mem_nhdsGT hρ,
    (tendsto_order.1 hD).1 (ENNReal.ofReal (1 - δ)) (ENNReal.ofReal_lt_one.2 (by linarith)),
    (tendsto_order.1 hL).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)] with s hs hs2 hs3
  have hBρ : closedBall x s ⊆ closedBall x ρ := closedBall_subset_closedBall hs.2.le
  have hi₁s : IntegrableOn θ₁ (M₁ ∩ closedBall x s) H :=
    hi₁.mono_set (inter_subset_inter_right _ hBρ)
  have hi₂s : IntegrableOn θ₂ (M₂ ∩ closedBall x s) H :=
    hi₂.mono_set (inter_subset_inter_right _ hBρ)
  have hBm : MeasurableSet (closedBall x s) := measurableSet_closedBall
  set B := closedBall x s with hB_def
  set b₁ := ∫⁻ z in M₁ ∩ B, ENNReal.ofReal (θ₁ z) ∂H with hb₁_def
  set I := ∫⁻ z in M₁ ∩ B, ENNReal.ofReal (θ₁ z) *
    ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ ∂H with hI_def
  set a₂ := ∫⁻ z in M₁ ∩ M₂ ∩ B, ENNReal.ofReal (θ₂ z) ∂H with ha₂_def
  set b₂ := ∫⁻ z in M₂ ∩ B, ENNReal.ofReal (θ₂ z) ∂H with hb₂_def
  set d₂ := ∫⁻ z in (M₂ \ M₁) ∩ B, ENNReal.ofReal (θ₂ z) ∂H with hd₂_def
  have hb₁ : b₁ ≠ ∞ := hi₁s.setLIntegral_lt_top.ne
  have hb₂ : b₂ ≠ ∞ := hi₂s.setLIntegral_lt_top.ne
  -- `b₂ = a₂ + d₂`: split `M₂ ∩ B` along `M₁`.
  have hsplit : b₂ = a₂ + d₂ := by
    have e : M₁ ∩ M₂ ∩ B = M₂ ∩ B ∩ M₁ := by
      ext z; simp only [mem_inter_iff]; tauto
    rw [hb₂_def, ha₂_def, hd₂_def, e, sdiff_inter_right_comm, ← lintegral_add_measure,
      Measure.restrict_inter_add_sdiff₀ _ hM₁]
  have ha₂ : a₂ ≠ ∞ := ne_top_of_le_ne_top hb₂ (by rw [hsplit]; exact le_self_add)
  have hd₂ : d₂ ≠ ∞ := ne_top_of_le_ne_top hb₂ (by rw [hsplit]; exact le_add_self)
  -- `(1 − δ) b₂ ≤ a₂` and `I ≤ δ b₁`.
  have h2 : ENNReal.ofReal (1 - δ) * b₂ ≤ a₂ :=
    ((ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.ofReal_ne_top) (Or.inl hb₂)).1 hs2).le
  have h3 : I ≤ ENNReal.ofReal δ * b₁ := by
    rcases eq_or_ne I 0 with h0 | h0
    · rw [h0]; exact zero_le
    · exact ((ENNReal.div_lt_iff (Or.inr h0) (Or.inl hb₁)).1 hs3).le
  have hI : I ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁) h3
  -- `a₂ ≤ c b₁ + I`, since `θ₂ ≤ c θ₁ + θ₁ |g − c|` on `M₁ ∩ M₂`.
  have h4 : a₂ ≤ ENNReal.ofReal c * b₁ + I := by
    have hA : NullMeasurableSet (M₁ ∩ M₂ ∩ B) H := (hM₁.inter hM₂).inter hBm.nullMeasurableSet
    have hm : AEMeasurable (fun z => ENNReal.ofReal c * ENNReal.ofReal (θ₁ z))
        (H.restrict (M₁ ∩ B)) :=
      hi₁s.aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul _
    calc a₂ ≤ ∫⁻ z in M₁ ∩ M₂ ∩ B, (ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) +
          ENNReal.ofReal (θ₁ z) * ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) ∂H := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hA] with z hz
          have h1z : 0 < θ₁ z := hθ₁ z hz.1.1
          have e : θ₁ z * (θ₂ z / θ₁ z) = θ₂ z := mul_div_cancel₀ _ h1z.ne'
          rw [indicator_of_mem hz.1]
          calc ENNReal.ofReal (θ₂ z)
              = ENNReal.ofReal (c * θ₁ z + θ₁ z * (θ₂ z / θ₁ z - c)) := by
                congr 1; rw [mul_sub, e]; ring
            _ ≤ ENNReal.ofReal (c * θ₁ z) + ENNReal.ofReal (θ₁ z * (θ₂ z / θ₁ z - c)) :=
                ENNReal.ofReal_add_le
            _ ≤ ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) + ‖θ₁ z * (θ₂ z / θ₁ z - c)‖ₑ := by
                rw [ENNReal.ofReal_mul hc.le]; gcongr; exact Real.ofReal_le_enorm _
            _ = ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) +
                ENNReal.ofReal (θ₁ z) * ‖θ₂ z / θ₁ z - c‖ₑ := by
                rw [enorm_mul, Real.enorm_of_nonneg h1z.le]
      _ ≤ ∫⁻ z in M₁ ∩ B, (ENNReal.ofReal c * ENNReal.ofReal (θ₁ z) +
          ENNReal.ofReal (θ₁ z) * ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) ∂H :=
          lintegral_mono_set fun z hz => ⟨hz.1.1, hz.2⟩
      _ = ENNReal.ofReal c * b₁ + I := by
          rw [lintegral_add_left' hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Pointwise, `|1_{M₂} θ₂ − c 1_{M₁} θ₁| = 1_{M₁} θ₁ |g − c| + 1_{M₂ ∖ M₁} θ₂`.
  have hpt : ∀ z, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ≤
      M₁.indicator (fun z => ENNReal.ofReal (θ₁ z) *
        ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) z +
      (M₂ \ M₁).indicator (fun z => ENNReal.ofReal (θ₂ z)) z := by
    intro z
    by_cases h1 : z ∈ M₁ <;> by_cases h2 : z ∈ M₂
    · have h1z : 0 < θ₁ z := hθ₁ z h1
      have e : θ₁ z * (θ₂ z / θ₁ z) = θ₂ z := mul_div_cancel₀ _ h1z.ne'
      have hn : z ∉ M₂ \ M₁ := fun h => h.2 h1
      simp only [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (mem_inter h1 h2),
        indicator_of_notMem hn, add_zero]
      refine le_of_eq ?_
      rw [show θ₂ z - c * θ₁ z = θ₁ z * (θ₂ z / θ₁ z - c) by rw [mul_sub, e]; ring, enorm_mul,
        Real.enorm_of_nonneg h1z.le]
    · have h1z : 0 < θ₁ z := hθ₁ z h1
      have hn : z ∉ M₂ \ M₁ := fun h => h.2 h1
      have hn' : z ∉ M₁ ∩ M₂ := fun h => h2 h.2
      simp only [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_notMem hn',
        indicator_of_notMem hn, add_zero]
      refine le_of_eq ?_
      rw [show (0 : ℝ) - c * θ₁ z = θ₁ z * (0 - c) by ring, enorm_mul,
        Real.enorm_of_nonneg h1z.le]
    · have h2z : 0 < θ₂ z := hθ₂ z h2
      simp only [indicator_of_notMem h1, indicator_of_mem h2,
        indicator_of_mem (show z ∈ M₂ \ M₁ from ⟨h2, h1⟩), mul_zero, sub_zero, zero_add]
      exact (Real.enorm_of_nonneg h2z.le).le
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2,
        indicator_of_notMem (show z ∉ M₂ \ M₁ from fun h => h2 h.1), mul_zero, sub_zero,
        enorm_zero, add_zero, le_refl]
  -- Hence `∫_B |1_{M₂} θ₂ − c 1_{M₁} θ₁| dH ≤ I + d₂`.
  have h5 : ∫⁻ z in B, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂H ≤ I + d₂ := by
    have hGm : AEMeasurable ((M₂ \ M₁).indicator fun z => ENNReal.ofReal (θ₂ z))
        (H.restrict B) := by
      rw [aemeasurable_indicator_iff₀ ((hM₂.diff hM₁).mono Measure.restrict_le_self),
        Measure.restrict_restrict' hBm]
      exact hi₂s.aestronglyMeasurable.aemeasurable.ennreal_ofReal.mono_set
        (inter_subset_inter_left _ sdiff_subset)
    calc ∫⁻ z in B, ‖M₂.indicator θ₂ z - c * M₁.indicator θ₁ z‖ₑ ∂H
        ≤ ∫⁻ z in B, (M₁.indicator (fun z => ENNReal.ofReal (θ₁ z) *
            ‖(M₁ ∩ M₂).indicator (fun w => θ₂ w / θ₁ w) z - c‖ₑ) z +
          (M₂ \ M₁).indicator (fun z => ENNReal.ofReal (θ₂ z)) z) ∂H := lintegral_mono hpt
      _ = I + d₂ := by
        rw [lintegral_add_right' _ hGm,
          setLIntegral_indicator₀ _ (hM₁.mono Measure.restrict_le_self),
          setLIntegral_indicator₀ _ ((hM₂.diff hM₁).mono Measure.restrict_le_self)]
  -- Real arithmetic: `I + d₂ ≤ δ b₁ + δ b₂ ≤ δ (1 + 2c + 2δ) b₁ ≤ ε b₁`.
  have hfin : I + d₂ ≤ ENNReal.ofReal ε * b₁ := by
    have hcb : ENNReal.ofReal c * b₁ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁
    have r1 : b₂.toReal = a₂.toReal + d₂.toReal := by rw [hsplit, ENNReal.toReal_add ha₂ hd₂]
    have r2 : (1 - δ) * b₂.toReal ≤ a₂.toReal := by
      have := ENNReal.toReal_mono ha₂ h2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have r3 : I.toReal ≤ δ * b₁.toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁) h3
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
    have r4 : a₂.toReal ≤ c * b₁.toReal + I.toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hcb, hI⟩) h4
      rwa [ENNReal.toReal_add hcb hI, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at this
    have hB₁ : 0 ≤ b₁.toReal := ENNReal.toReal_nonneg
    have hB₂ : 0 ≤ b₂.toReal := ENNReal.toReal_nonneg
    have e1 : 0 ≤ (1 / 2 - δ) * b₂.toReal := mul_nonneg (by linarith) hB₂
    have hB2 : b₂.toReal ≤ 2 * (c + δ) * b₁.toReal := by linarith
    have e2 : δ * b₂.toReal ≤ δ * (2 * (c + δ) * b₁.toReal) :=
      mul_le_mul_of_nonneg_left hB2 hδ.le
    have e3 : δ * (3 * c + 3) * b₁.toReal ≤ ε * b₁.toReal := mul_le_mul_of_nonneg_right hδε hB₁
    have e4 : 0 ≤ δ * b₁.toReal * (c + 2 - 2 * δ) :=
      mul_nonneg (mul_nonneg hδ.le hB₁) (by linarith)
    rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hI, hd₂⟩)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁), ENNReal.toReal_add hI hd₂,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]
    linarith
  exact h5.trans hfin

/-- Relative `L¹` density of the weighted measures `θᵢ Hⁿ ⌞ Mᵢ`, as used for the locality of
approximate tangent spaces (Simon Ch. 3, Remark 1.8(1)): for `Hⁿ ⌞ (M₁ ∩ M₂)`-a.e. `x` and every
`ε > 0`, `∫_{B̄_s(x)} |1_{M₂} θ₂ − (θ₂(x)/θ₁(x)) 1_{M₁} θ₁| dHⁿ ≤ ε ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ` for
all small `s > 0`.  Cover `U` by balls `B_r(y)` with `B̄_r(y) ⊆ U`.  On each, `θᵢ` is integrable
on the compact `Mᵢ ∩ B̄_r(y)`, so the weighted Lebesgue-point and Besicovitch density limits hold
a.e. on `M₁ ∩ M₂ ∩ B_r(y)`; at such `x` they give the estimate, with `ρ = r − dist(x, y)`. -/
theorem Submission.fiw_tl_ae_l1_density :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ),
      M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) →
      (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ ε : ℝ, 0 < ε →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in closedBall x s,
          ‖M₂.indicator θ₂ z - θ₂ x / θ₁ x * M₁.indicator θ₁ z‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤
            ENNReal.ofReal ε * ∫⁻ z in M₁ ∩ closedBall x s, ENNReal.ofReal (θ₁ z)
              ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U hU M₁ M₂ θ₁ θ₂ hM₁U _hM₂U hM₁ hM₂ hθ₁ hθ₂ hθ₁i hθ₂i
  -- Step 1: it suffices to prove the claim a.e. on `M₁ ∩ M₂ ∩ B_r(y)` whenever `B̄_r(y) ⊆ U`.
  refine Submission.fiw_tl_ald_ball_reduction P _ U (M₁ ∩ M₂) _ hU
    (inter_subset_left.trans hM₁U) fun y r hyr => ?_
  -- Steps 2–4: `θᵢ` is integrable on the compact `Mᵢ ∩ B̄_r(y)`, so the weighted Lebesgue-point
  -- and density limits at `x` hold a.e. on `M₁ ∩ M₂ ∩ B_r(y)`.
  filter_upwards [Submission.fiw_tl_ald_local_differentiation P n M₁ M₂ θ₁ θ₂ y r hM₁ hM₂ hθ₁ hθ₂
      (hθ₁i _ (isCompact_closedBall y r) hyr) (hθ₂i _ (isCompact_closedBall y r) hyr),
    ae_restrict_mem₀ ((hM₁.inter hM₂).inter measurableSet_ball.nullMeasurableSet)]
    with x ⟨hL, hD⟩ hx
  -- Steps 5–8: the estimate at `x`, using `B̄_ρ(x) ⊆ B̄_r(y) ⊆ U` for `ρ = r - dist x y > 0`.
  have hρU : closedBall x (r - dist x y) ⊆ U :=
    (closedBall_subset_closedBall' (sub_add_cancel r _).le).trans hyr
  exact Submission.fiw_tl_ald_pointwise_estimate P n M₁ M₂ θ₁ θ₂ x hM₁ hM₂ hθ₁ hθ₂ hx.1
    ⟨r - dist x y, sub_pos.2 (mem_ball.1 hx.2), hθ₁i _ (isCompact_closedBall x _) hρU,
      hθ₂i _ (isCompact_closedBall x _) hρU⟩ hL hD

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
