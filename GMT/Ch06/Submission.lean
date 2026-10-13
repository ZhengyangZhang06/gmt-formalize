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

/-- The Euclidean coefficient norm of an `n`-covector on `ℝ^P` is at most `√(P^n)` times its
operator norm: each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` (`b` the standard
orthonormal basis) is bounded by `‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.fiw_ims_sc_covectorNorm_le_opNorm :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
  intro P n α
  -- Every coefficient is at most `‖α‖`, since the standard basis vectors are unit vectors.
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
        -- The sum has `P ^ n` terms, each at most `‖α‖ ^ 2`.
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

/-- **Test forms have bounded Euclidean coefficient norm**: Simon's
`|ω| = sup_x √⟨ω(x), ω(x)⟩` (Ch. 6, 1.15, p. 134) is finite, with a positive bound.
A test form is smooth, hence continuous, and has compact support, so `‖ω(x)‖ ≤ B` for its
operator norm; `|α| ≤ √(Pⁿ) ‖α‖` (`fiw_ims_sc_covectorNorm_le_opNorm`) then gives the bound
`C = √(Pⁿ) B + 1 > 0`. -/
theorem Submission.fiw_ims_sc_testForm_bounded : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U n), ∃ C : ℝ, 0 < C ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C := by
  intro P n U ω
  -- `ω` is smooth, hence continuous, and has compact support, so `‖ω(x)‖ ≤ B` for all `x`.
  have hω : Continuous (ω : DifferentialForm (Eucl P) n) := ω.property.1.1.continuous
  obtain ⟨B, hB⟩ := ω.property.1.2.exists_bound_of_continuous hω
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ Real.sqrt ((P : ℝ) ^ n) := Real.sqrt_nonneg _
  refine ⟨Real.sqrt ((P : ℝ) ^ n) * B + 1, by positivity, fun x => ?_⟩
  calc covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)
      ≤ Real.sqrt ((P : ℝ) ^ n) * ‖(ω : DifferentialForm (Eucl P) n) x‖ :=
        Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
    _ ≤ Real.sqrt ((P : ℝ) ^ n) * B := mul_le_mul_of_nonneg_left (hB x) hD0
    _ ≤ Real.sqrt ((P : ℝ) ^ n) * B + 1 := by linarith
/-- **A null sequence of test forms is uniformly small (Simon Ch. 6, 2.1).**  If `ω_q → 0` in
`𝒟ⁿ(U)`, then all `ω_q` are supported in one compact `K ⊆ U` and, for every `ε > 0`, eventually
`|ω_q(x)| ≤ ε` for every `x`, in the Euclidean coefficient norm of Remark 2.6.  The `k = 0` part
of the convergence makes the operator norm `‖ω_q(x)‖` uniformly small on `K`, and `ω_q = 0` off
`K`; `Submission.fiw_ims_sc_covectorNorm_le_opNorm` gives `|α| ≤ √(P^n) ‖α‖`. -/
theorem Submission.fiw_ims_sc_converges_zero_small : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : ℕ → TestFormOn U n), TestFormOnConverges ω 0 → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ U ∧ (∀ q, tsupport ((ω q : DifferentialForm (Eucl P) n)) ⊆ K) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop, ∀ x, covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x) ≤ ε := by
  intro P n U ω hω
  obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hω
  refine ⟨K, hK, hKU, hsupp, fun ε hε => ?_⟩
  set D := Real.sqrt ((P : ℝ) ^ n)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hδ : 0 < ε / (D + 1) := by positivity
  -- `k = 0`: eventually `‖ω_q(x) - 0‖ < ε / (D + 1)` for all `x ∈ K`.
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv 0) _ hδ] with q hq x
  have hx : ‖(ω q : DifferentialForm (Eucl P) n) x‖ ≤ ε / (D + 1) := by
    by_cases hxK : x ∈ K
    · have h := hq x hxK
      rw [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
        norm_iteratedFDeriv_zero] at h
      exact h.le
    · -- off `K ⊇ tsupport ω_q` the form vanishes
      rw [image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp q h), norm_zero]
      exact hδ.le
  calc covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x)
      ≤ D * ‖(ω q : DifferentialForm (Eucl P) n) x‖ :=
        Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
    _ ≤ D * (ε / (D + 1)) := mul_le_mul_of_nonneg_left hx hD
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **Continuity criterion on `𝒟ⁿ(U)`** (the topology of Simon Ch. 6, §1, p. 134, and the
continuity required in 2.1): if for each compact `K ⊆ U` there is `A` with `|L(ω)| ≤ A·C`
whenever `spt ω ⊆ K` and `|ω(x)| ≤ C` for all `x` (the Euclidean coefficient norm of 1.15), then
`L(ω_q) → 0` for every null sequence `ω_q → 0` of test forms.  By
`fiw_ims_sc_converges_zero_small` all `spt ω_q` lie in one compact `K ⊆ U` and
`sup_x |ω_q(x)| → 0`; for `ε > 0` and `δ = ε / (|A| + 1)`, eventually
`|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.  Neither linearity of `L` nor a sign of `A` is used. -/
theorem Submission.fiw_ims_sc_continuous_of_bound : ∀ (P n : ℕ) (U : Set (Eucl P)) (L : TestFormOn U n → ℝ), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ A : ℝ, ∀ (ω : TestFormOn U n) (C : ℝ), 0 < C → tsupport ((ω : DifferentialForm (Eucl P) n)) ⊆ K → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) → |L ω| ≤ A * C) → ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 → Tendsto (fun q => L (ωs q)) atTop (𝓝 0) := by
  intro P n U L hL ωs hωs
  -- One compact `K ⊆ U` carries every `spt ω_q`, and `sup_x |ω_q(x)| → 0`.
  obtain ⟨K, hK, hKU, hsupp, hsmall⟩ :=
    Submission.fiw_ims_sc_converges_zero_small P n U ωs hωs
  -- The hypothesis on `K`: `|L(ω)| ≤ A·C` whenever `spt ω ⊆ K` and `|ω| ≤ C`.
  obtain ⟨A, hA⟩ := hL K hK hKU
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA1 : 0 < |A| + 1 := by positivity
  have hδ : 0 < ε / (|A| + 1) := div_pos hε hA1
  -- Eventually `|ω_q| ≤ δ = ε / (|A| + 1)`, hence `|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.
  filter_upwards [hsmall _ hδ] with q hq
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs q)| ≤ A * (ε / (|A| + 1)) := hA (ωs q) _ hδ (hsupp q) hq
    _ ≤ |A| * (ε / (|A| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self A) hδ.le
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hA1]
      nlinarith [abs_nonneg A]
/-- **Integer-weighted series estimate** (behind the `M`-absolutely convergent integer series
`∑_r c_r T_r` of currents, Simon Ch. 6, 3.13, pp. 149–150, used in the proof of 7.2).  If
`ofReal |a_r| ≤ m_r · ofReal C` for every `r` and `∑' r, |c_r| m_r < ∞` in `[0, ∞]`, then
`r ↦ c_r a_r` is summable and `ofReal |∑' r, c_r a_r| ≤ ofReal C · ∑' r, |c_r| m_r`.
Termwise `ofReal |c_r a_r| = |c_r| · ofReal |a_r| ≤ ofReal C · (|c_r| m_r)`, so
`∑' r, ofReal |c_r a_r|` is finite; this gives absolute summability, and the estimate follows
from `|∑' r, x_r| ≤ ∑' r, |x_r|`. -/
theorem Submission.fiw_ims_sc_series_bound : ∀ (a : ℕ → ℝ) (c : ℕ → ℤ) (m : ℕ → ℝ≥0∞) (C : ℝ), (∀ r, ENNReal.ofReal |a r| ≤ m r * ENNReal.ofReal C) → (∑' r, ((c r).natAbs : ℝ≥0∞) * m r) < ∞ → Summable (fun r => (c r : ℝ) * a r) ∧ ENNReal.ofReal |∑' r, (c r : ℝ) * a r| ≤ ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r := by
  intro a c m C ha hsum
  -- `ofReal |(c_r : ℝ)| = |c_r|` in `[0, ∞]`.
  have hc : ∀ r, ENNReal.ofReal |(c r : ℝ)| = ((c r).natAbs : ℝ≥0∞) := fun r => by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, ENNReal.ofReal_natCast]
  -- Termwise bound `ofReal |c_r a_r| ≤ ofReal C · (|c_r| m_r)`.
  have hterm : ∀ r, ENNReal.ofReal |(c r : ℝ) * a r| ≤
      ENNReal.ofReal C * (((c r).natAbs : ℝ≥0∞) * m r) := fun r => by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), hc]
    calc ((c r).natAbs : ℝ≥0∞) * ENNReal.ofReal |a r|
        ≤ ((c r).natAbs : ℝ≥0∞) * (m r * ENNReal.ofReal C) := by gcongr; exact ha r
      _ = ENNReal.ofReal C * (((c r).natAbs : ℝ≥0∞) * m r) := by ring
  -- Summing: `∑' ofReal |c_r a_r| ≤ ofReal C · ∑' |c_r| m_r < ∞`.
  have hle : ∑' r, ENNReal.ofReal |(c r : ℝ) * a r| ≤
      ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hterm
  have hfin : ∑' r, ENNReal.ofReal |(c r : ℝ) * a r| ≠ ∞ :=
    (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum)).ne
  -- Absolute summability, hence summability.
  have habs : Summable fun r => |(c r : ℝ) * a r| :=
    (ENNReal.summable_toReal hfin).congr fun r => ENNReal.toReal_ofReal (abs_nonneg _)
  refine ⟨habs.of_abs, ?_⟩
  -- `|∑' x_r| ≤ ∑' |x_r|`, and `ofReal` commutes with the nonnegative sum.
  have hnorm : Summable fun r => ‖(c r : ℝ) * a r‖ := by simpa only [Real.norm_eq_abs] using habs
  have htri : |∑' r, (c r : ℝ) * a r| ≤ ∑' r, |(c r : ℝ) * a r| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  calc ENNReal.ofReal |∑' r, (c r : ℝ) * a r|
      ≤ ENNReal.ofReal (∑' r, |(c r : ℝ) * a r|) := ENNReal.ofReal_le_ofReal htri
    _ = ∑' r, ENNReal.ofReal |(c r : ℝ) * a r| :=
        ENNReal.ofReal_tsum_of_nonneg (fun r => abs_nonneg _) habs
    _ ≤ ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r := hle
/-- Mass bound: if `η` is supported in `V` and `|η(x)| ≤ C` everywhere (Euclidean covector
norm) with `C > 0`, then `|X(η)| ≤ M_V(X) · C` in `[0, ∞]`. -/
theorem Submission.fiw_ims_mass_bound :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U k) (V : Set (Eucl P))
      (η : TestFormOn U k) (C : ℝ), 0 < C → tsupport (η : DifferentialForm (Eucl P) k) ⊆ V →
      (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) k) x) ≤ C) →
      ENNReal.ofReal |X η| ≤ X.massOn V * ENNReal.ofReal C := by
  intro P k U X V η C hC hV hη
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- A sign `s = ±C⁻¹` with `s X(η) = C⁻¹ |X(η)|`.
  obtain ⟨s, hs, hsX⟩ : ∃ s : ℝ, |s| = C⁻¹ ∧ s * X η = C⁻¹ * |X η| := by
    rcases le_or_gt 0 (X η) with h | h
    · exact ⟨C⁻¹, abs_of_pos (inv_pos.mpr hC), by rw [abs_of_nonneg h]⟩
    · exact ⟨-C⁻¹, by rw [abs_neg, abs_of_pos (inv_pos.mpr hC)], by rw [abs_of_neg h]; ring⟩
  -- `s η` is mass-admissible for `V`: supported in `V`, pointwise norm `≤ C⁻¹ C = 1`.
  have hadm : s • η ∈ massAdmissibleOn U k V := by
    refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hV, fun x => ?_⟩
    change covectorEuclideanNorm (s • (η : DifferentialForm (Eucl P) k) x) ≤ 1
    rw [hsmul, hs, inv_mul_le_iff₀ hC, mul_one]
    exact hη x
  -- Definition of mass and linearity of `X`: `ofReal (C⁻¹ |X(η)|) ≤ M_V(X)`.
  have hle := X.le_massOn hadm
  rw [map_smul, smul_eq_mul, hsX] at hle
  -- Undo the scaling by `C⁻¹`.
  calc ENNReal.ofReal |X η| = ENNReal.ofReal (C⁻¹ * |X η| * C) := by
        rw [mul_comm C⁻¹, mul_assoc, inv_mul_cancel₀ hC.ne', mul_one]
    _ = ENNReal.ofReal (C⁻¹ * |X η|) * ENNReal.ofReal C :=
        ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hC.le) (abs_nonneg _))
    _ ≤ X.massOn V * ENNReal.ofReal C := by gcongr

/-- Series of currents: if `∑' r, |c_r| M_W(T_r) < ∞` for every `W ⊂⊂ U`, then `∑ c_r T_r`
converges unconditionally on every test form to a current `S` with
`M_W(S) ≤ ∑' r, |c_r| M_W(T_r)` for every set `W`. -/
theorem Submission.fiw_ims_series_current :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : ℕ → GeometricCurrentOn U n) (c : ℕ → ℤ),
      (∀ W, CompactlyContainedOpen W U →
        (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W) < ∞) →
      ∃ S : GeometricCurrentOn U n, (∀ ω, HasSum (fun r => (c r : ℝ) * T r ω) (S ω)) ∧
        ∀ W, S.massOn W ≤ ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W := by
  intro P n U hU T c hT
  -- Every compact `K ⊆ U` lies in some `W ⊂⊂ U`.
  have hW : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      ∃ W, CompactlyContainedOpen W U ∧ K ⊆ W := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨W, ⟨hWo, hWc, hWU⟩, hKW⟩
  -- Core estimate: for `ω` supported in `V` with `|ω| ≤ C`, the series converges and
  -- `|∑' r, c_r T_r(ω)| ≤ C ∑' r, |c_r| M_V(T_r)` in `[0, ∞]`.
  have hcore : ∀ (V : Set (Eucl P)) (ω : TestFormOn U n) (C : ℝ), 0 < C →
      tsupport (ω : DifferentialForm (Eucl P) n) ⊆ V →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn V) < ∞ →
      Summable (fun r => (c r : ℝ) * T r ω) ∧
        ENNReal.ofReal |∑' r, (c r : ℝ) * T r ω| ≤
          ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn V :=
    fun V ω C hC hV hω hfin =>
      Submission.fiw_ims_sc_series_bound (fun r => T r ω) c (fun r => (T r).massOn V) C
        (fun r => Submission.fiw_ims_mass_bound P n U (T r) V ω C hC hV hω) hfin
  -- The series converges on every test form: `tsupport ω` is a compact subset of `U`.
  have hsum : ∀ ω : TestFormOn U n, Summable (fun r => (c r : ℝ) * T r ω) := by
    intro ω
    obtain ⟨C, hC, hω⟩ := Submission.fiw_ims_sc_testForm_bounded P n U ω
    obtain ⟨W, hWU, hKW⟩ := hW (tsupport (ω : DifferentialForm (Eucl P) n))
      ω.property.1.2 ω.property.2
    exact (hcore W ω C hC hKW hω (hT W hWU)).1
  -- The sum `S₀(ω) = ∑' r, c_r T_r(ω)` is linear in `ω`.
  let S₀ : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑' r, (c r : ℝ) * T r ω
      map_add' := fun ω η => by
        simp only [map_add, mul_add]
        exact (hsum ω).tsum_add (hsum η)
      map_smul' := fun a ω => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun r => mul_left_comm _ _ _ }
  -- Sequential continuity: on forms supported in a compact `K ⊆ U` with `|ω| ≤ C`,
  -- `|S₀(ω)| ≤ A C` with `A = ∑' r, |c_r| M_W(T_r)` for some `W ⊂⊂ U` containing `K`.
  have hcont : ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 →
      Tendsto (fun q => S₀ (ωs q)) atTop (𝓝 0) := by
    refine Submission.fiw_ims_sc_continuous_of_bound P n U S₀ fun K hK hKU => ?_
    obtain ⟨W, hWU, hKW⟩ := hW K hK hKU
    have hA := hT W hWU
    refine ⟨(∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W).toReal,
      fun ω C hC hω hωC => ?_⟩
    have h : ENNReal.ofReal |S₀ ω| ≤
        ENNReal.ofReal (C * (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W).toReal) := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hA.ne]
      exact (hcore W ω C hC (hω.trans hKW) hωC hA).2
    rw [mul_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le ENNReal.toReal_nonneg)).1 h
  refine ⟨⟨S₀, hcont⟩, fun ω => (hsum ω).hasSum, fun W => ?_⟩
  -- Mass bound: test the admissible forms of `M_W` with `C = 1`.
  rcases eq_top_or_lt_top (∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W) with hA | hA
  · rw [hA]
    exact le_top
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (S₀ ω) ≤ ENNReal.ofReal |S₀ ω| := ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal 1 * ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W :=
      (hcore W ω 1 one_pos hω.1 hω.2 hA).2
    _ = ∑' r, ((c r).natAbs : ℝ≥0∞) * (T r).massOn W := by
      rw [ENNReal.ofReal_one, one_mul]
/-- Orthonormal frames of the same subspace have the same simple `n`-vector up to sign (Simon
Ch. 6, 3.1: `ξ(x) = τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM` is determined by `TₓM` up
to sign).  `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q = span τ = span τ'`.  Restricted to
`Q`, an `n`-covector `ω` is an alternating `n`-form on the `n`-dimensional space `Q`, so
`ω(τ') = b.det(b') ω(τ)` (`AlternatingMap.eq_smul_basis_det`, as in the determinant computation
after (3.4), p. 147), and `b.det(b') = ±1` because the change of basis between orthonormal bases
is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.fiw_ims_frame_sign :
    ∀ (P n : ℕ) (τ τ' : Fin n → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ τ' →
      Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') →
      simpleNVector τ' = simpleNVector τ ∨ simpleNVector τ' = -simpleNVector τ := by
  intro P n τ τ' hτ hτ' hspan
  set Q : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ)
  -- Step 1: `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`.
  let b : Module.Basis (Fin n) ℝ Q := Module.Basis.span hτ.linearIndependent
  let b' : Module.Basis (Fin n) ℝ Q :=
    (Module.Basis.span hτ'.linearIndependent).map (LinearEquiv.ofEq _ _ hspan.symm)
  have hb : Q.subtype ∘ b = τ :=
    funext fun i => Module.Basis.coe_span_apply hτ.linearIndependent i
  have hb' : Q.subtype ∘ b' = τ' := by
    funext i
    simp [b']
  have hbo : Orthonormal ℝ b := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb]
    exact hτ
  have hbo' : Orthonormal ℝ b' := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb']
    exact hτ'
  -- Step 2: the restriction `f = ω ∘ Q.subtype` of an `n`-covector `ω` is an alternating
  -- `n`-form on `Q`, so `f = f b • b.det`; evaluated at `b'` this is `ω τ' = b.det b' * ω τ`.
  have key : ∀ ω : Covector (Eucl P) n, ω τ' = b.det b' * ω τ := by
    intro ω
    have h := DFunLike.congr_fun
      ((ω.toAlternatingMap.compLinearMap Q.subtype).eq_smul_basis_det b) ⇑b'
    rw [AlternatingMap.smul_apply, smul_eq_mul] at h
    change ω (Q.subtype ∘ b') = ω (Q.subtype ∘ b) * b.det b' at h
    rw [hb, hb'] at h
    rw [h, mul_comm]
  -- Step 3: `b.det b' = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : b.det b' = 1 ∨ b.det b' = -1 := by
    simpa using (b.toOrthonormalBasis hbo).det_to_matrix_orthonormalBasis_real
      (b'.toOrthonormalBasis hbo')
  -- Step 4: extensionality, as `simpleNVector v ω = ω v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key ω, hd, one_mul]
  · right
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key ω, hd, neg_one_mul]

/-- Orientations of rectifiable triples agree up to sign on the overlap where every weighted
approximate tangent space of `(M₁, θ₁)` is one of `(M₂, θ₂)` (Simon Ch. 6, 3.1: `ξ(x)` is
`±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`).  At `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂` the `orients`
fields give orthonormal frames `τ`, `τ'` with `ξ₁(x) = ±s(τ)` and `ξ₂(x) = ±s(τ')`, where
`s = simpleNVector`.  By hypothesis `span τ` is a weighted approximate tangent space of
`(M₂, θ₂)` at `x`, so `span τ = span τ'` by uniqueness (Ch. 3, 1.7; `θ₂(x) > 0`), and
`Submission.fiw_ims_frame_sign` gives `s(τ') = ±s(τ)`. -/
theorem Submission.fiw_ims_orientation_sign :
    ∀ (P n : ℕ) (U M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ)
      (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple U n M₁ θ₁ ξ₁ → IsRectifiableTriple U n M₂ θ₂ ξ₂ →
      (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q →
          HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ξ₁ x = ξ₂ x ∨ ξ₁ x = -ξ₂ x := by
  intro P n U M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ h₁ h₂ htan
  -- Step 1: `M₁ ∩ M₂` is `Hⁿ`-null-measurable, so a.e. point of the overlap lies in it.
  have hmem : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), x ∈ M₁ ∩ M₂ :=
    ae_restrict_mem₀ (h₁.nullMeasurableSet.inter h₂.nullMeasurableSet)
  -- Step 2: both orientation conditions hold a.e. on the overlap.
  have ho₁ := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M₁ ∩ M₂ ⊆ M₁) h₁.orients
  have ho₂ := ae_restrict_of_ae_restrict_of_subset (inter_subset_right : M₁ ∩ M₂ ⊆ M₂) h₂.orients
  filter_upwards [hmem, ho₁, ho₂, htan] with x hx hx₁ hx₂ hQ
  obtain ⟨τ, hτ, hT, hξ₁⟩ := hx₁
  obtain ⟨τ', hτ', hT', hξ₂⟩ := hx₂
  -- Step 3: `span τ` is also a weighted approximate tangent space of `(M₂, θ₂)` at `x`, and
  -- `θ₂ x > 0`, so it is `span τ'`.
  have hspan : Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') :=
    (hQ _ hT).unique (h₂.pos x hx.2).ne' hT'
  -- Step 4: `s(τ') = ±s(τ)`; combine the three signs.  (`rw [neg_neg]` and `simp` do not fire
  -- on `NVector` negation at this pin, but `neg_neg` applied to a term does.)
  have hnn : ∀ v : NVector (Eucl P) n, - -v = v := fun v => neg_neg v
  rcases Submission.fiw_ims_frame_sign P n τ τ' hτ hτ' hspan with hs | hs <;>
    rcases hξ₁ with hξ₁ | hξ₁ <;> rcases hξ₂ with hξ₂ | hξ₂ <;> rw [hξ₁, hξ₂, hs] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact Or.inl (hnn _).symm
    | exact Or.inr (hnn _).symm
/-- Local finiteness for an integer series of currents `∑ c_r τ(M_r, θ_r, ξ_r)` (Simon Ch. 6, 3.13,
used for `R^(ℓ)`, `S^(ℓ)` in the proof of 7.2): with `Θ = ∑' r, |c_r| 1_{M_r} θ_r` and
`∑' r, |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞` for each `W ⊂⊂ U`, `Θ` is locally `Hⁿ`-integrable in `U`
and `Hⁿ`-a.e. `x` lies in `M_r` for only finitely many `r` with `c_r ≠ 0`.  Termwise integration
(`lintegral_tsum`) gives `∫_W Θ dHⁿ < ∞` on each `W ⊂⊂ U`, so `Θ < ∞` a.e. near each point of
`U`, hence a.e. on `U` (`ℝ^P` is second countable); at such `x` each such `r` adds at least `1`
to `Θ(x)`, and off `U` no `M_r` contains `x`. -/
theorem Submission.fiw_ims_overlap_finite :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (c : ℕ → ℤ), (∀ r, M r ⊆ U) →
        (∀ r, NullMeasurableSet (M r) (μHE[n] : Measure (Eucl P))) →
        (∀ r, ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
          IntegrableOn (θ r) (M r ∩ K) (μHE[n] : Measure (Eucl P))) →
        (∀ r, ∀ x ∈ M r, 1 ≤ θ r x) →
        (∀ W, CompactlyContainedOpen W U →
          (∑' r, ((c r).natAbs : ℝ≥0∞) *
            ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) →
        (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
          (∫⁻ x in K, ∑' r, ((c r).natAbs : ℝ≥0∞) *
            (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x
              ∂(μHE[n] : Measure (Eucl P))) < ∞) ∧
        ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), {r | c r ≠ 0 ∧ x ∈ M r}.Finite := by
  intro P n U hU M θ c hMU hMnull hint hθ1 hsum
  set H : Measure (Eucl P) := (μHE[n] : Measure (Eucl P))
  -- `g r = |c_r| 1_{M_r} θ_r` and `Θ = ∑' r, g r`.
  set g : ℕ → Eucl P → ℝ≥0∞ := fun r x =>
    ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x with hg
  set Θ : Eucl P → ℝ≥0∞ := fun x => ∑' r, g r x with hΘ
  -- Steps 1–2: on `W ⊂⊂ U` every `g r` is a.e.-measurable (`θ_r` is integrable on
  -- `M_r ∩ closure W`), so `∫_W Θ = ∑' r, |c_r| ∫_{M_r ∩ W} θ_r < ∞`.
  have hW : ∀ W, CompactlyContainedOpen W U →
      AEMeasurable Θ (H.restrict W) ∧ ∫⁻ x in W, Θ x ∂H < ∞ := by
    intro W hWcc
    obtain ⟨hWo, hWc, hWU⟩ := hWcc
    have hnull : ∀ r, NullMeasurableSet (M r) (H.restrict W) := fun r =>
      (hMnull r).mono Measure.restrict_le_self
    have hterm : ∀ r, AEMeasurable (g r) (H.restrict W) := by
      intro r
      have hi : IntegrableOn (θ r) (M r ∩ W) H :=
        (hint r _ hWc hWU).mono_set (inter_subset_inter_right _ subset_closure)
      have hmeas : AEMeasurable (fun y => ENNReal.ofReal (θ r y))
          ((H.restrict W).restrict (M r)) := by
        rw [Measure.restrict_restrict' hWo.measurableSet]
        exact hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      exact ((aemeasurable_indicator_iff₀ (hnull r)).2 hmeas).const_mul _
    refine ⟨AEMeasurable.tsum hterm, ?_⟩
    have hEq : ∫⁻ x in W, Θ x ∂H =
        ∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂H := by
      rw [hΘ, lintegral_tsum hterm]
      refine tsum_congr fun r => ?_
      rw [hg, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_indicator₀ (hnull r),
        Measure.restrict_restrict' hWo.measurableSet]
    rw [hEq]
    exact hsum W ⟨hWo, hWc, hWU⟩
  -- Every compact `K ⊆ U` lies in some `W ⊂⊂ U`.
  have hcover : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      ∃ W, CompactlyContainedOpen W U ∧ K ⊆ W := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨W, ⟨hWo, hWc, hWU⟩, hKW⟩
  -- Step 3: conclusion (a), as `∫_K Θ ≤ ∫_W Θ` for `K ⊆ W ⊂⊂ U`.
  refine ⟨fun K hK hKU => ?_, ?_⟩
  · obtain ⟨W, hWcc, hKW⟩ := hcover K hK hKU
    exact (lintegral_mono_set hKW).trans_lt (hW W hWcc).2
  -- Step 4: `N = {x ∈ U | Θ x = ∞}` is null: each `x ∈ U` has a neighbourhood `W ⊂⊂ U` on which
  -- `Θ < ∞` a.e., and `ℝ^P` is second countable.
  set N : Set (Eucl P) := {x | x ∈ U ∧ Θ x = ∞}
  have hN0 : H N = 0 := by
    refine measure_null_of_locally_null N fun x hx => ?_
    obtain ⟨W, hWcc, hxW⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx.1)
    obtain ⟨hmeas, hfin⟩ := hW W hWcc
    have hae : ∀ᵐ y ∂H, y ∈ W → Θ y < ∞ :=
      (ae_restrict_iff' hWcc.1.measurableSet).1 (ae_lt_top' hmeas hfin.ne)
    refine ⟨N ∩ W, inter_mem_nhdsWithin N (hWcc.1.mem_nhds (hxW rfl)), ?_⟩
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    simp only [mem_ofPred_eq, not_imp, not_lt, top_le_iff]
    exact ⟨hy.2, hy.1.2⟩
  -- Step 5: conclusion (b).  For `x ∈ U \ N`, every `r` with `c_r ≠ 0` and `x ∈ M_r` has
  -- `g r x ≥ 1` while `∑' r, g r x < ∞`; for `x ∉ U` no `M_r` contains `x`.
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with x hxN
  by_cases hxU : x ∈ U
  · have hΘx : Θ x ≠ ∞ := fun h => hxN ⟨hxU, h⟩
    refine (ENNReal.finite_const_le_of_tsum_ne_top hΘx one_ne_zero).subset ?_
    rintro r ⟨hc, hxM⟩
    have h1 : (1 : ℝ≥0∞) ≤ ((c r).natAbs : ℝ≥0∞) := by
      exact_mod_cast Int.natAbs_pos.2 hc
    have h2 : (1 : ℝ≥0∞) ≤ (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x := by
      rw [indicator_of_mem hxM]
      simpa using ENNReal.ofReal_le_ofReal (hθ1 r x hxM)
    simpa [hg] using mul_le_mul' h1 h2
  · exact finite_empty.subset fun r hr => hxU (hMU r hr.2)
/-- Orthonormal frames of the same subspace have the same simple `n`-vector up to sign (Simon
Ch. 6, 3.1: `ξ(x) = τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM` is determined by `TₓM` up
to sign).  `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q = span τ = span τ'`.  Restricted to
`Q`, an `n`-covector `ω` is an alternating `n`-form on the `n`-dimensional space `Q`, so
`ω(τ') = b.det(b') ω(τ)` (`AlternatingMap.eq_smul_basis_det`, as in the determinant computation
after (3.4), p. 147), and `b.det(b') = ±1` because the change of basis between orthonormal bases
is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.fiw_ims_frame_sign :
    ∀ (P n : ℕ) (τ τ' : Fin n → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ τ' →
      Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') →
      simpleNVector τ' = simpleNVector τ ∨ simpleNVector τ' = -simpleNVector τ := by
  intro P n τ τ' hτ hτ' hspan
  set Q : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ)
  -- Step 1: `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`.
  let b : Module.Basis (Fin n) ℝ Q := Module.Basis.span hτ.linearIndependent
  let b' : Module.Basis (Fin n) ℝ Q :=
    (Module.Basis.span hτ'.linearIndependent).map (LinearEquiv.ofEq _ _ hspan.symm)
  have hb : Q.subtype ∘ b = τ :=
    funext fun i => Module.Basis.coe_span_apply hτ.linearIndependent i
  have hb' : Q.subtype ∘ b' = τ' := by
    funext i
    simp [b']
  have hbo : Orthonormal ℝ b := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb]
    exact hτ
  have hbo' : Orthonormal ℝ b' := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb']
    exact hτ'
  -- Step 2: the restriction `f = ω ∘ Q.subtype` of an `n`-covector `ω` is an alternating
  -- `n`-form on `Q`, so `f = f b • b.det`; evaluated at `b'` this is `ω τ' = b.det b' * ω τ`.
  have key : ∀ ω : Covector (Eucl P) n, ω τ' = b.det b' * ω τ := by
    intro ω
    have h := DFunLike.congr_fun
      ((ω.toAlternatingMap.compLinearMap Q.subtype).eq_smul_basis_det b) ⇑b'
    rw [AlternatingMap.smul_apply, smul_eq_mul] at h
    change ω (Q.subtype ∘ b') = ω (Q.subtype ∘ b) * b.det b' at h
    rw [hb, hb'] at h
    rw [h, mul_comm]
  -- Step 3: `b.det b' = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : b.det b' = 1 ∨ b.det b' = -1 := by
    simpa using (b.toOrthonormalBasis hbo).det_to_matrix_orthonormalBasis_real
      (b'.toOrthonormalBasis hbo')
  -- Step 4: extensionality, as `simpleNVector v ω = ω v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key ω, hd, one_mul]
  · right
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key ω, hd, neg_one_mul]

/-- Orientations of rectifiable triples agree up to sign on the overlap where every weighted
approximate tangent space of `(M₁, θ₁)` is one of `(M₂, θ₂)` (Simon Ch. 6, 3.1: `ξ(x)` is
`±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`).  At `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂` the `orients`
fields give orthonormal frames `τ`, `τ'` with `ξ₁(x) = ±s(τ)` and `ξ₂(x) = ±s(τ')`, where
`s = simpleNVector`.  By hypothesis `span τ` is a weighted approximate tangent space of
`(M₂, θ₂)` at `x`, so `span τ = span τ'` by uniqueness (Ch. 3, 1.7; `θ₂(x) > 0`), and
`Submission.fiw_ims_frame_sign` gives `s(τ') = ±s(τ)`. -/
theorem Submission.fiw_ims_orientation_sign :
    ∀ (P n : ℕ) (U M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ)
      (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple U n M₁ θ₁ ξ₁ → IsRectifiableTriple U n M₂ θ₂ ξ₂ →
      (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q →
          HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ξ₁ x = ξ₂ x ∨ ξ₁ x = -ξ₂ x := by
  intro P n U M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ h₁ h₂ htan
  -- Step 1: `M₁ ∩ M₂` is `Hⁿ`-null-measurable, so a.e. point of the overlap lies in it.
  have hmem : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), x ∈ M₁ ∩ M₂ :=
    ae_restrict_mem₀ (h₁.nullMeasurableSet.inter h₂.nullMeasurableSet)
  -- Step 2: both orientation conditions hold a.e. on the overlap.
  have ho₁ := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M₁ ∩ M₂ ⊆ M₁) h₁.orients
  have ho₂ := ae_restrict_of_ae_restrict_of_subset (inter_subset_right : M₁ ∩ M₂ ⊆ M₂) h₂.orients
  filter_upwards [hmem, ho₁, ho₂, htan] with x hx hx₁ hx₂ hQ
  obtain ⟨τ, hτ, hT, hξ₁⟩ := hx₁
  obtain ⟨τ', hτ', hT', hξ₂⟩ := hx₂
  -- Step 3: `span τ` is also a weighted approximate tangent space of `(M₂, θ₂)` at `x`, and
  -- `θ₂ x > 0`, so it is `span τ'`.
  have hspan : Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') :=
    (hQ _ hT).unique (h₂.pos x hx.2).ne' hT'
  -- Step 4: `s(τ') = ±s(τ)`; combine the three signs.  (`rw [neg_neg]` and `simp` do not fire
  -- on `NVector` negation at this pin, but `neg_neg` applied to a term does.)
  have hnn : ∀ v : NVector (Eucl P) n, - -v = v := fun v => neg_neg v
  rcases Submission.fiw_ims_frame_sign P n τ τ' hτ hτ' hspan with hs | hs <;>
    rcases hξ₁ with hξ₁ | hξ₁ <;> rcases hξ₂ with hξ₂ | hξ₂ <;> rw [hξ₁, hξ₂, hs] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact Or.inl (hnn _).symm
    | exact Or.inr (hnn _).symm
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

/-- One term of Simon Ch. 6, 3.1 (‡): for a rectifiable triple `(M, θ, ξ)` in `U`, an open
`W ⊂⊂ U` and a continuous `n`-form `ω` with `tsupport ω ⊆ W` and `‖ω(x)‖ ≤ B`, the integrand
`1_M θ ⟨ω, ξ⟩` is `Hⁿ`-a.e. strongly measurable and `∫ |1_M θ ⟨ω, ξ⟩| dHⁿ ≤ B ∫_{M ∩ W} θ dHⁿ`,
since `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖` for `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` (`Submission.fiw_ims_tt_unit_bound`). -/
theorem Submission.fiw_ims_tt_term_bound :
    ∀ (P n : ℕ) (U W M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
      (ω : Eucl P → Covector (Eucl P) n) (B : ℝ), IsRectifiableTriple U n M θ ξ →
      CompactlyContainedOpen W U → Continuous ω → tsupport ω ⊆ W → (∀ x, ‖ω x‖ ≤ B) →
      AEStronglyMeasurable (M.indicator fun x => θ x * ξ x (ω x)) (μHE[n] : Measure (Eucl P)) ∧
      ∫⁻ x, ‖M.indicator (fun y => θ y * ξ y (ω y)) x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤
        ENNReal.ofReal B * ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U W M θ ξ ω B htri hW hω hωW hB
  obtain ⟨hWo, hLc, hLU⟩ := hW
  set g : Eucl P → ℝ := fun x => θ x * ξ x (ω x)
  -- `g` vanishes off `tsupport ω ⊆ W`.
  have hg0 : ∀ x, x ∉ W → g x = 0 := by
    intro x hx
    have hωx : ω x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hωW h)
    show θ x * ξ x (ω x) = 0
    rw [hωx, map_zero, mul_zero]
  have hML : NullMeasurableSet (M ∩ closure W) (μHE[n] : Measure (Eucl P)) :=
    htri.nullMeasurableSet.inter isClosed_closure.measurableSet.nullMeasurableSet
  have hMW : NullMeasurableSet (M ∩ W) (μHE[n] : Measure (Eucl P)) :=
    htri.nullMeasurableSet.inter hWo.measurableSet.nullMeasurableSet
  -- Hence `1_M g = 1_{M ∩ closure W} g`.
  have hG : M.indicator g = (M ∩ closure W).indicator g := by
    funext x
    by_cases hxL : x ∈ closure W
    · by_cases hxM : x ∈ M <;> simp [Set.indicator, hxL, hxM]
    · simp [Set.indicator, hxL, hg0 x fun hxW => hxL (subset_closure hxW)]
  refine ⟨?_, ?_⟩
  · -- On `M ∩ closure W`: `θ` is integrable (`closure W` is a compact subset of `U`), `ξ` is
    -- measurable (restricted from `M`), `ω` is continuous, and `(v, α) ↦ v α` is continuous.
    have hθ : AEStronglyMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict (M ∩ closure W)) :=
      (htri.integrableOn (closure W) hLc hLU).aestronglyMeasurable
    have hξ : AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict (M ∩ closure W)) :=
      htri.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have hev : Continuous fun p : NVector (Eucl P) n × Covector (Eucl P) n => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    rw [hG, aestronglyMeasurable_indicator_iff₀ hML]
    exact hθ.mul (hev.comp_aestronglyMeasurable (hξ.prodMk hω.aestronglyMeasurable))
  · -- `Hⁿ`-a.e. `|1_M g| ≤ 1_{M ∩ W} B θ`: on `M ∩ W`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ`
    -- orthonormal, so `|ξ(x)(ω(x))| ≤ ‖ω(x)‖ ≤ B`; elsewhere `1_M g` vanishes.
    have hae : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ‖M.indicator g x‖ₑ ≤
        (M ∩ W).indicator (fun y => ENNReal.ofReal B * ENNReal.ofReal (θ y)) x := by
      filter_upwards [(ae_restrict_iff'₀ htri.nullMeasurableSet).1 htri.orients] with x hx
      by_cases hxM : x ∈ M
      · by_cases hxW : x ∈ W
        · obtain ⟨τ, hτ, -, hξx⟩ := hx hxM
          have hθx : 0 < θ x := htri.pos x hxM
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
          have hub : |ξ x (ω x)| ≤ B :=
            (Submission.fiw_ims_tt_unit_bound P n τ (ξ x) hτ hξx (ω x)).trans (hB x)
          rw [Set.indicator_of_mem hxM, Set.indicator_of_mem (show x ∈ M ∩ W from ⟨hxM, hxW⟩)]
          show ‖θ x * ξ x (ω x)‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (θ x)
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hB0, abs_mul, abs_of_pos hθx,
            mul_comm B]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hub hθx.le)
        · simp [Set.indicator_of_mem hxM, hg0 x hxW]
      · simp [Set.indicator_of_notMem hxM]
    calc ∫⁻ x, ‖M.indicator g x‖ₑ ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ x, (M ∩ W).indicator (fun y => ENNReal.ofReal B * ENNReal.ofReal (θ y)) x
            ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hae
      _ = ∫⁻ x in M ∩ W, ENNReal.ofReal B * ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_indicator₀ hMW _
      _ = ENNReal.ofReal B * ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Termwise integration of an integer series of rectifiable triples** (Simon Ch. 6, 3.1 (‡)
for the `M`-absolutely convergent series of 3.13 and the proof of 7.2).
Let `(M_r, θ_r, ξ_r)` be rectifiable triples in `U` and `c_r ∈ ℤ` with
`∑_r |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞` for every `W ⊂⊂ U`.  Then for every `ω ∈ 𝒟ⁿ(U)`, with
`F_r := 1_{M_r} c_r θ_r ⟨ω, ξ_r⟩`, the series `∑_r c_r τ(M_r, θ_r, ξ_r)(ω)` has sum
`∫ ∑_r F_r dHⁿ`.  Choose an open `W ⊂⊂ U` with `tsupport ω ⊆ W` and a bound `‖ω(x)‖ ≤ B`;
`Submission.fiw_ims_tt_term_bound` makes each `F_r` a.e. strongly measurable with
`∫ |F_r| dHⁿ ≤ |c_r| B ∫_{M_r ∩ W} θ_r dHⁿ`, so `∑_r ∫ |F_r| dHⁿ < ∞` and the series can be
integrated termwise (`hasSum_integral_of_summable_integral_norm`); finally
`∫ F_r dHⁿ = c_r ∫_{M_r} θ_r ⟨ω, ξ_r⟩ dHⁿ = c_r τ(M_r, θ_r, ξ_r)(ω)`. -/
theorem Submission.fiw_ims_tsum_tau :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ)
      (ξ : ℕ → Eucl P → NVector (Eucl P) n) (c : ℕ → ℤ),
      (∀ r, IsRectifiableTriple U n (M r) (θ r) (ξ r)) →
      (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) →
      ∀ ω : TestFormOn U n, HasSum (fun r => (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω)
        (∫ x, ∑' r, (M r).indicator (fun y => (c r : ℝ) * (θ r y * ξ r y
          ((ω : DifferentialForm (Eucl P) n) y))) x ∂(μHE[n] : Measure (Eucl P))) := by
  intro P n U hU M θ ξ c htri hsum ω
  -- `ω` is smooth (hence continuous) with compact support `tsupport ω ⊆ U`.
  have hωc : Continuous (ω : DifferentialForm (Eucl P) n) := ω.2.1.1.continuous
  have hωK : HasCompactSupport (ω : DifferentialForm (Eucl P) n) := ω.2.1.2
  -- Localization: an open `W ⊂⊂ U` with `tsupport ω ⊆ W`, and `‖ω(x)‖ ≤ B` for all `x`.
  obtain ⟨W, hWo, hKW, hLU, hLc⟩ :=
    exists_open_between_and_isCompact_closure hωK.isCompact hU ω.2.2
  have hW : CompactlyContainedOpen W U := ⟨hWo, hLc, hLU⟩
  obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support hωK
  -- `F r = c_r G r`, where `G r := 1_{M_r} θ_r ⟨ω, ξ_r⟩` is controlled by the child lemma.
  let G : ℕ → Eucl P → ℝ := fun r =>
    (M r).indicator fun y => θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y)
  let F : ℕ → Eucl P → ℝ := fun r =>
    (M r).indicator fun y => (c r : ℝ) * (θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y))
  have hFG : ∀ r x, F r x = (c r : ℝ) * G r x := by
    intro r x
    by_cases hx : x ∈ M r <;> simp [F, G, hx]
  have hG : ∀ r, AEStronglyMeasurable (G r) (μHE[n] : Measure (Eucl P)) ∧
      ∫⁻ x, ‖G r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal B *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P)) := fun r =>
    Submission.fiw_ims_tt_term_bound P n U W (M r) (θ r) (ξ r) (ω : DifferentialForm (Eucl P) n)
      B (htri r) hW hωc hKW hB
  -- `‖(c_r : ℝ)‖ₑ = |c_r|`.
  have hc : ∀ r, ‖(c r : ℝ)‖ₑ = ((c r).natAbs : ℝ≥0∞) := fun r => by
    rw [Real.enorm_eq_ofReal_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
  have hFm : ∀ r, AEStronglyMeasurable (F r) (μHE[n] : Measure (Eucl P)) := fun r => by
    have : F r = fun x => (c r : ℝ) * G r x := funext (hFG r)
    rw [this]
    exact (hG r).1.const_mul _
  -- `∫ |F_r| dHⁿ ≤ |c_r| B ∫_{M_r ∩ W} θ_r dHⁿ`.
  have hFle : ∀ r, ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal B *
      (((c r).natAbs : ℝ≥0∞) *
        ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) := fun r =>
    calc ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P))
        = ∫⁻ x, ((c r).natAbs : ℝ≥0∞) * ‖G r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
          simp_rw [hFG r, enorm_mul, hc]
      _ = ((c r).natAbs : ℝ≥0∞) * ∫⁻ x, ‖G r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
      _ ≤ ((c r).natAbs : ℝ≥0∞) * (ENNReal.ofReal B *
            ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) := by
          gcongr
          exact (hG r).2
      _ = _ := mul_left_comm _ _ _
  -- Hence `∑_r ∫ |F_r| dHⁿ ≤ B ∑_r |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞`.
  have hFsum : ∑' r, ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B))
      (hsum W hW).ne) ?_
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hFle
  have hFi : ∀ r, Integrable (F r) (μHE[n] : Measure (Eucl P)) := fun r =>
    ⟨hFm r, (ENNReal.le_tsum (f := fun r => ∫⁻ x, ‖F r x‖ₑ ∂(μHE[n] : Measure (Eucl P))) r).trans_lt
      (lt_top_iff_ne_top.2 hFsum)⟩
  have hFs : Summable fun r => ∫ x, ‖F r x‖ ∂(μHE[n] : Measure (Eucl P)) :=
    (ENNReal.summable_toReal hFsum).congr fun r => (integral_norm_eq_lintegral_enorm (hFm r)).symm
  -- Termwise integration, and `∫ F_r dHⁿ = c_r τ(M_r, θ_r, ξ_r)(ω)`.
  have hint : ∀ r, ∫ x, F r x ∂(μHE[n] : Measure (Eucl P)) =
      (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω := fun r => by
    simp only [F]
    rw [integral_indicator₀ (htri r).nullMeasurableSet, integral_const_mul]
    rfl
  have hS := hasSum_integral_of_summable_integral_norm hFi hFs
  simp only [hint] at hS
  exact hS

/-- **Series of integer multiplicity currents, Simon Ch. 6, 3.13 (p. 149), as used in the proof
of 7.2 (p. 170).**  Under tangent locality in `U`, an `M`-absolutely convergent series
`∑ c_r τ(M_r, θ_r, ξ_r)` with `c_r ∈ ℤ` and integer `θ_r` is one integer multiplicity current
`τ(M', θ', ξ')`.  Off an `Hⁿ`-null set, only finitely many `M_r` with `c_r ≠ 0` contain `x`,
each `ξ_r` orients `M_r` at `x`, and `ξ_r(x) = ±ξ_{r'}(x)` whenever `x ∈ M_r ∩ M_{r'}`.  With
`ξ̂ = ξ_{r(x)}` for the first index `r(x)` of an `M_r ∋ x` and `ξ_r = σ_r ξ̂` (`σ_r = ±1`),
`θ̂ = ∑' r, 1_{M_r} c_r σ_r θ_r` is an integer-valued finite sum bounded by
`∑' r, |c_r| 1_{M_r} θ_r`; then `M' = {θ̂ ≠ 0}`, `θ' = |θ̂|`, `ξ' = (θ̂/|θ̂|) ξ̂` give the sum of
the series. -/
theorem Submission.fiw_ims_combine : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → (∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) → (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q) → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) n) (c : ℕ → ℤ), (∀ r, IsRectifiableTriple U n (M r) (θ r) (ξ r)) → (∀ r, ∀ x ∈ M r, ∃ k : ℕ, θ r x = k) → (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) → ∃ (M' : Set (Eucl P)) (θ' : Eucl P → ℝ) (ξ' : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M' θ' ξ' ∧ (∀ x ∈ M', ∃ k : ℕ, θ' x = k) ∧ ∀ ω : TestFormOn U n, HasSum (fun r => (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω) (tauAction n M' θ' ξ' ω) := by
  intro P n U hU hTL M θ ξ c hT hθN hsum
  classical
  -- `NVector (Eucl P) n` is a normed space, but instance search does not find its
  -- pseudometrizability; the operator-norm uniformity provides it.
  have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) n) := by
    let u : UniformSpace (NVector (Eucl P) n) := PseudoMetricSpace.toUniformSpace
    have : (uniformity (NVector (Eucl P) n)).IsCountablyGenerated :=
      @EMetric.instIsCountablyGeneratedUniformity _ PseudoMetricSpace.toPseudoEMetricSpace
    exact @UniformSpace.pseudoMetrizableSpace _ u this
  /- Step 1: the exceptional null sets.  Off a null set, only finitely many `M r` with
  `c r ≠ 0` contain `x`, every `M r ∋ x` is oriented at `x` by `ξ r`, and the orientations of
  any two `M r, M r' ∋ x` agree up to sign. -/
  have hθ1 : ∀ r, ∀ x ∈ M r, 1 ≤ θ r x := by
    intro r x hx
    obtain ⟨k, hk⟩ := hθN r x hx
    have hpos := (hT r).pos x hx
    rw [hk] at hpos ⊢
    have hk0 : 0 < k := by exact_mod_cast hpos
    exact_mod_cast hk0
  obtain ⟨hΘ, hfin⟩ := Submission.fiw_ims_overlap_finite P n U hU M θ c
    (fun r => (hT r).subset) (fun r => (hT r).nullMeasurableSet) (fun r => (hT r).integrableOn)
    hθ1 hsum
  have horient : ∀ r, ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ M r →
      ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt n (M r) (θ r) x (Submodule.span ℝ (range τ)) ∧
        (ξ r x = simpleNVector τ ∨ ξ r x = -simpleNVector τ) := fun r =>
    (ae_restrict_iff'₀ (hT r).nullMeasurableSet).1 (hT r).orients
  have hsign : ∀ r r', ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ M r → x ∈ M r' →
      (ξ r x = ξ r' x ∨ ξ r x = -ξ r' x) := by
    intro r r'
    have h := Submission.fiw_ims_orientation_sign P n U (M r) (M r') (θ r) (θ r') (ξ r) (ξ r')
      (hT r) (hT r') (hTL (M r) (M r') (θ r) (θ r') (hT r).subset (hT r').subset
        (hT r).nullMeasurableSet (hT r').nullMeasurableSet (hT r).pos (hT r').pos
        (hT r).integrableOn (hT r').integrableOn)
    rw [ae_restrict_iff'₀ ((hT r).nullMeasurableSet.inter (hT r').nullMeasurableSet)] at h
    filter_upwards [h] with x hx h1 h2 using hx ⟨h1, h2⟩
  set G : Set (Eucl P) := {x | {r | c r ≠ 0 ∧ x ∈ M r}.Finite ∧
    (∀ r, x ∈ M r → ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt n (M r) (θ r) x (Submodule.span ℝ (range τ)) ∧
        (ξ r x = simpleNVector τ ∨ ξ r x = -simpleNVector τ)) ∧
    ∀ r r', x ∈ M r → x ∈ M r' → (ξ r x = ξ r' x ∨ ξ r x = -ξ r' x)}
  have hGae : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ G := by
    have h3 : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ∀ r r', x ∈ M r → x ∈ M r' →
        (ξ r x = ξ r' x ∨ ξ r x = -ξ r' x) :=
      ae_all_iff.2 fun r => ae_all_iff.2 (hsign r)
    filter_upwards [hfin, ae_all_iff.2 horient, h3] with x h1 h2 h3 using ⟨h1, h2, h3⟩
  have hGnm : NullMeasurableSet G (μHE[n] : Measure (Eucl P)) :=
    (NullMeasurableSet.of_null (ae_iff.1 hGae)).of_compl
  /- Step 2: the first index `rf x` of a set `M r` containing `x`, and the sets `A r` on which
  it equals `r`. -/
  let rf : Eucl P → ℕ := fun x => if h : ∃ r, x ∈ M r then Nat.find h else 0
  have hrf : ∀ r, ∀ x ∈ M r, x ∈ M (rf x) := by
    intro r x hx
    have h : ∃ r, x ∈ M r := ⟨r, hx⟩
    simp only [rf, dite_eq_left h]
    exact Nat.find_spec h
  have hrfA : ∀ r x, x ∈ M r → (∀ r' < r, x ∉ M r') → rf x = r := by
    intro r x hx hlt
    have h : ∃ r, x ∈ M r := ⟨r, hx⟩
    simp only [rf, dite_eq_left h]
    exact (Nat.find_eq_iff h).2 ⟨hx, hlt⟩
  have hMA : (⋃ r, M r) = ⋃ r, M r ∩ ⋂ r' ∈ {r' | r' < r}, (M r')ᶜ := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨r, hr⟩
      have h : ∃ r, x ∈ M r := ⟨r, hr⟩
      exact ⟨Nat.find h, Nat.find_spec h, fun r' hr' => Nat.find_min h hr'⟩
    · rintro ⟨r, hr, -⟩
      exact ⟨r, hr⟩
  /- Step 3: the reference orientation `ξh x = ξ (rf x) x`, a.e.-strongly measurable on
  `⋃ r, M r` because it agrees with `ξ r` on `A r`. -/
  let ξh : Eucl P → NVector (Eucl P) n := fun x => ξ (rf x) x
  have hξh : AEStronglyMeasurable ξh
      ((μHE[n] : Measure (Eucl P)).restrict (⋃ r, M r)) := by
    rw [hMA, aestronglyMeasurable_iUnion_iff]
    intro r
    have hAnm : NullMeasurableSet (M r ∩ ⋂ r' ∈ {r' | r' < r}, (M r')ᶜ)
        (μHE[n] : Measure (Eucl P)) :=
      (hT r).nullMeasurableSet.inter
        (NullMeasurableSet.iInter fun r' => NullMeasurableSet.iInter fun _ =>
          (hT r').nullMeasurableSet.compl)
    refine ((hT r).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)).congr ?_
    filter_upwards [ae_restrict_mem₀ hAnm] with x hx
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hx
    simp only [ξh, hrfA r x hx.1 hx.2]
  /- Step 4: the signs `σ r x = ±1` with `ξ r x = σ r x • ξh x` on `G ∩ M r`. -/
  let σ : ℕ → Eucl P → ℝ := fun r x => if ξ r x = ξh x then 1 else -1
  have hσ : ∀ r, AEStronglyMeasurable (σ r) ((μHE[n] : Measure (Eucl P)).restrict (M r)) := by
    intro r
    have hE : NullMeasurableSet {x | ξ r x = ξh x}
        ((μHE[n] : Measure (Eucl P)).restrict (M r)) :=
      (hT r).aestronglyMeasurable.nullMeasurableSet_eq_fun
        (hξh.mono_measure (Measure.restrict_mono (subset_iUnion M r) le_rfl))
    have h := AEStronglyMeasurable.piecewise (f := fun _ => (1 : ℝ)) (g := fun _ => (-1 : ℝ))
      hE aestronglyMeasurable_const aestronglyMeasurable_const
    convert h using 1
    funext x
    simp only [σ, Set.piecewise, mem_ofPred_eq]
  /- Step 5: `θ r` is a.e.-strongly measurable on `M r` (local integrability). -/
  have hθm : ∀ r, AEStronglyMeasurable (θ r) ((μHE[n] : Measure (Eucl P)).restrict (M r)) := by
    intro r
    apply LocallyIntegrableOn.aestronglyMeasurable
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x ((hT r).subset hx)
    refine ⟨M r ∩ closedBall x (ε / 2),
      inter_mem_nhdsWithin _ (closedBall_mem_nhds x (half_pos hε)), ?_⟩
    exact (hT r).integrableOn _ (isCompact_closedBall x (ε / 2))
      ((closedBall_subset_ball (half_lt_self hε)).trans hball)
  /- Step 6: the integer multiplicity `θh = ∑' r, t r`, `t r = 1_{M r} c r σ r θ r`. -/
  let t : ℕ → Eucl P → ℝ := fun r => (M r).indicator fun y => (c r : ℝ) * (σ r y * θ r y)
  have ht : ∀ r, AEStronglyMeasurable (t r) (μHE[n] : Measure (Eucl P)) := fun r =>
    (aestronglyMeasurable_indicator_iff₀ (hT r).nullMeasurableSet).2
      (((hσ r).mul (hθm r)).const_mul _)
  have ht0 : ∀ x r, ¬(c r ≠ 0 ∧ x ∈ M r) → t r x = 0 := by
    intro x r h
    by_cases hx : x ∈ M r
    · have hc : c r = 0 := by
        by_contra hc
        exact h ⟨hc, hx⟩
      simp [t, hx, hc]
    · simp [t, hx]
  let θh : Eucl P → ℝ := fun x => ∑' r, t r x
  have hθh_sum : ∀ x (hx : x ∈ G), θh x = ∑ r ∈ hx.1.toFinset, t r x := by
    intro x hx
    refine tsum_eq_sum fun r hr => ht0 x r ?_
    rwa [Set.Finite.mem_toFinset] at hr
  have hθh_hasSum : ∀ x ∈ G, HasSum (fun r => t r x) (θh x) := by
    intro x hx
    refine (summable_of_ne_finset_zero (s := hx.1.toFinset) fun r hr => ht0 x r ?_).hasSum
    rwa [Set.Finite.mem_toFinset] at hr
  have hθh : AEStronglyMeasurable θh (μHE[n] : Measure (Eucl P)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N x => ∑ r ∈ Finset.range N, t r x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun r _ => ht r) ?_
    filter_upwards [hGae] with x hx
    exact (hθh_hasSum x hx).tendsto_sum_nat
  -- `ofReal |t r x| = |c r| 1_{M r} ofReal (θ r x)`, so `ofReal |θh| ≤ Θ` on `G`.
  have hterm : ∀ x r, ENNReal.ofReal |t r x| =
      ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x := by
    intro x r
    by_cases hxr : x ∈ M r
    · have hσabs : |σ r x| = 1 := by
        simp only [σ]
        split_ifs <;> simp
      have htx : t r x = (c r : ℝ) * (σ r x * θ r x) := indicator_of_mem hxr _
      rw [indicator_of_mem hxr, htx, abs_mul, abs_mul, hσabs, one_mul,
        abs_of_pos ((hT r).pos x hxr), ENNReal.ofReal_mul (abs_nonneg _), ← Int.cast_abs,
        ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
    · simp [t, hxr]
  have hΘx : ∀ x ∈ G, ENNReal.ofReal |θh x| ≤
      ∑' r, ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x := by
    intro x hx
    rw [hθh_sum x hx]
    calc ENNReal.ofReal |∑ r ∈ hx.1.toFinset, t r x|
        ≤ ENNReal.ofReal (∑ r ∈ hx.1.toFinset, |t r x|) :=
          ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ r ∈ hx.1.toFinset, ENNReal.ofReal |t r x| :=
          ENNReal.ofReal_sum_of_nonneg fun r _ => abs_nonneg _
      _ = ∑ r ∈ hx.1.toFinset,
            ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x :=
          Finset.sum_congr rfl fun r _ => hterm x r
      _ ≤ _ := ENNReal.sum_le_tsum _
  /- Step 7: the new triple. -/
  set M' : Set (Eucl P) := {x | x ∈ G ∧ θh x ≠ 0} with hM'
  set θ' : Eucl P → ℝ := fun x => |θh x| with hθ'
  set ξ' : Eucl P → NVector (Eucl P) n := fun x => (θh x / |θh x|) • ξh x
  have hM'sub : M' ⊆ ⋃ r, M r := by
    intro x hx
    by_contra hcon
    simp only [mem_iUnion, not_exists] at hcon
    apply hx.2
    have h0 : ∀ r, t r x = 0 := fun r => by simp [t, hcon r]
    simp only [θh, h0, tsum_zero]
  have hM'U : M' ⊆ U := hM'sub.trans (iUnion_subset fun r => (hT r).subset)
  have hM'nm : NullMeasurableSet M' (μHE[n] : Measure (Eucl P)) := by
    have hM'eq : M' = G ∩ θh ⁻¹' {0}ᶜ := by
      ext x
      simp only [hM', mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff,
        mem_singleton_iff]
    rw [hM'eq]
    exact hGnm.inter (hθh.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl)
  have hθ'pos : ∀ x ∈ M', 0 < θ' x := fun x hx => abs_pos.2 hx.2
  have hθ'N : ∀ x ∈ M', ∃ k : ℕ, θ' x = k := by
    intro x hx
    have hint : ∀ r, ∃ z : ℤ, t r x = z := by
      intro r
      by_cases hxr : x ∈ M r
      · obtain ⟨k, hk⟩ := hθN r x hxr
        have htx : t r x = (c r : ℝ) * (σ r x * θ r x) := indicator_of_mem hxr _
        refine ⟨c r * ((if ξ r x = ξh x then 1 else -1) * k), ?_⟩
        rw [htx, hk]
        simp only [σ]
        split_ifs <;> push_cast <;> ring
      · exact ⟨0, by simp [t, hxr]⟩
    obtain ⟨z, hz⟩ : ∃ z : ℤ, θh x = z := by
      rw [hθh_sum x hx.1]
      exact Finset.sum_induction (fun r => t r x) (fun a : ℝ => ∃ z : ℤ, a = z)
        (fun a b ⟨za, ha⟩ ⟨zb, hb⟩ => ⟨za + zb, by rw [ha, hb, Int.cast_add]⟩)
        ⟨0, by rw [Int.cast_zero]⟩ fun r _ => hint r
    refine ⟨z.natAbs, ?_⟩
    simp only [hθ', hz, Nat.cast_natAbs, Int.cast_abs]
  have hθ'int : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      IntegrableOn θ' (M' ∩ K) (μHE[n] : Measure (Eucl P)) := by
    intro K hK hKU
    refine ⟨(continuous_abs.comp_aestronglyMeasurable hθh).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ x in M' ∩ K, ‖θ' x‖ₑ ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ x in M' ∩ K, ∑' r, ((c r).natAbs : ℝ≥0∞) *
            (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x ∂(μHE[n] : Measure (Eucl P)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀
            (hM'nm.inter hK.isClosed.measurableSet.nullMeasurableSet)] with x hx
          rw [Real.enorm_eq_ofReal_abs, hθ', abs_abs]
          exact hΘx x hx.1.1
      _ ≤ ∫⁻ x in K, ∑' r, ((c r).natAbs : ℝ≥0∞) *
            (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_mono_set inter_subset_right
      _ < ∞ := hΘ K hK hKU
  have hξ'meas : AEStronglyMeasurable ξ' ((μHE[n] : Measure (Eucl P)).restrict M') := by
    have h1 : AEStronglyMeasurable (fun x => θh x / |θh x|) (μHE[n] : Measure (Eucl P)) :=
      (hθh.aemeasurable.div
        (continuous_abs.measurable.comp_aemeasurable hθh.aemeasurable)).aestronglyMeasurable
    exact h1.restrict.smul (hξh.mono_measure (Measure.restrict_mono hM'sub le_rfl))
  /- Step 10 (vii): orientation of `M'`, by tangent locality for `(M r, θ r)` and `(M', θ')`. -/
  have hloc : ∀ r, ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), x ∈ M r ∩ M' →
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n (M r) (θ r) x Q →
        HasWeightedApproximateTangentSpaceAt n M' θ' x Q := fun r =>
    (ae_restrict_iff'₀ ((hT r).nullMeasurableSet.inter hM'nm)).1
      (hTL (M r) M' (θ r) θ' (hT r).subset hM'U (hT r).nullMeasurableSet hM'nm (hT r).pos
        hθ'pos (hT r).integrableOn hθ'int)
  have horient' : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M'),
      ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt n M' θ' x (Submodule.span ℝ (range τ)) ∧
        (ξ' x = simpleNVector τ ∨ ξ' x = -simpleNVector τ) := by
    rw [ae_restrict_iff'₀ hM'nm]
    filter_upwards [ae_all_iff.2 hloc] with x hlocx hxM'
    obtain ⟨r0, hr0⟩ := mem_iUnion.1 (hM'sub hxM')
    have hxr : x ∈ M (rf x) := hrf r0 x hr0
    obtain ⟨τ, hτ, hTx, hξτ⟩ := hxM'.1.2.1 (rf x) hxr
    refine ⟨τ, hτ, hlocx (rf x) ⟨hxr, hxM'⟩ _ hTx, ?_⟩
    have hsgn : θh x / |θh x| = 1 ∨ θh x / |θh x| = -1 := by
      rcases lt_or_gt_of_ne hxM'.2 with h | h
      · right
        rw [abs_of_neg h, div_neg, div_self hxM'.2]
      · left
        rw [abs_of_pos h, div_self hxM'.2]
    change (θh x / |θh x|) • ξ (rf x) x = simpleNVector τ ∨
      (θh x / |θh x|) • ξ (rf x) x = -simpleNVector τ
    rcases hsgn with h | h <;> rw [h] <;> rcases hξτ with h' | h' <;> rw [h']
    · exact Or.inl (one_smul ℝ _)
    · exact Or.inr (one_smul ℝ _)
    · exact Or.inr (ContinuousLinearMap.ext fun α => by
        simp only [smul_apply, neg_apply, smul_eq_mul, neg_one_mul])
    · exact Or.inl (ContinuousLinearMap.ext fun α => by
        simp only [smul_apply, neg_apply, smul_eq_mul, neg_one_mul, neg_neg])
  refine ⟨M', θ', ξ', ⟨hM'U, hM'nm,
    (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion M
      fun r => (hT r).countablyRectifiable).mono hM'sub,
    hθ'pos, hθ'int, hξ'meas, horient'⟩, hθ'N, ?_⟩
  /- Steps 8–9: `∑' r, 1_{M r} c r θ r ⟨ω, ξ r⟩ = 1_{M'} θ' ⟨ω, ξ'⟩` a.e., and `tsum_tau`. -/
  intro ω
  have h := Submission.fiw_ims_tsum_tau P n U hU M θ ξ c hT hsum ω
  convert h using 1
  unfold tauAction
  rw [← integral_indicator₀ hM'nm]
  refine integral_congr_ae ?_
  filter_upwards [hGae] with x hx
  have hterm' : ∀ r, (M r).indicator (fun y => (c r : ℝ) *
      (θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y))) x =
        t r x * ξh x ((ω : DifferentialForm (Eucl P) n) x) := by
    intro r
    by_cases hxr : x ∈ M r
    · have htx : t r x = (c r : ℝ) * (σ r x * θ r x) := indicator_of_mem hxr _
      rw [indicator_of_mem hxr, htx]
      have hs := hx.2.2 r (rf x) hxr (hrf r x hxr)
      simp only [σ]
      split_ifs with heq
      · rw [heq]
        ring
      · rcases hs with hs | hs
        · exact absurd hs heq
        · change (c r : ℝ) * (θ r x * ξ r x _) = (c r : ℝ) * (-1 * θ r x) * ξ (rf x) x _
          rw [hs, neg_apply]
          ring
    · simp [t, hxr]
  rw [tsum_congr hterm', tsum_mul_right]
  change _ = θh x * ξh x ((ω : DifferentialForm (Eucl P) n) x)
  by_cases hxM' : x ∈ M'
  · rw [indicator_of_mem hxM']
    have hne : |θh x| ≠ 0 := abs_ne_zero.2 hxM'.2
    simp only [θ', ξ', smul_apply, smul_eq_mul]
    field_simp
  · rw [indicator_of_notMem hxM']
    have h0 : θh x = 0 := by
      by_contra hne
      exact hxM' ⟨hx, hne⟩
    change (0 : ℝ) = θh x * _
    rw [h0, zero_mul]
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

/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, Remarks 1.5(2), 1.8(1); the
step `T_x M_C = T_x M_Q` of Ch. 6, 3.13): for `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂`, every weighted approximate
tangent space of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.  By `fiw_tl_ae_l1_density`, a.e.
`x ∈ M₁ ∩ M₂` has `∫_{B̄_s(x)} |1_{M₂} θ₂ − c 1_{M₁} θ₁| dHⁿ = o(∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ)` as
`s ↓ 0`, where `c = θ₂(x) / θ₁(x)`, so `θ₂(x) = c θ₁(x)`.  As `x ∈ U`, some compact `B̄_ρ(x)` lies
in `U`, so `θᵢ` is integrable on `Mᵢ ∩ B̄_ρ(x)`, and `fiw_tl_transfer` carries the tangent space
from `(M₁, θ₁)` to `(M₂, θ₂)`.  The exceptional null set does not depend on `Q`. -/
theorem Submission.fiw_tangent_locality :
    ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) → (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q := by
  intro P n U hU M₁ M₂ θ₁ θ₂ hM₁U hM₂U hM₁ hM₂ hθ₁ hθ₂ hθ₁i hθ₂i
  -- Step 1: a.e. `x ∈ M₁ ∩ M₂` is an `L¹`-density point with ratio `c = θ₂(x) / θ₁(x)`.
  filter_upwards [Submission.fiw_tl_ae_l1_density P n U hU M₁ M₂ θ₁ θ₂ hM₁U hM₂U hM₁ hM₂ hθ₁ hθ₂
    hθ₁i hθ₂i, ae_restrict_mem₀ (hM₁.inter hM₂)] with x hdens hx Q hQ
  -- Step 2: `x ∈ U` is open, so `B̄_ρ(x) ⊆ U` for some `ρ > 0`.
  obtain ⟨ρ, hρ, hρU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hM₁U hx.1))
  -- Step 3: transfer the tangent space; `θ₂(x) = (θ₂(x) / θ₁(x)) θ₁(x)` as `θ₁(x) > 0`.
  exact Submission.fiw_tl_transfer P n M₁ M₂ θ₁ θ₂ x (θ₂ x / θ₁ x) ρ hρ hM₁ hM₂
    (fun y hy => (hθ₁ y hy).le) (hθ₁i _ (isCompact_closedBall x ρ) hρU)
    (hθ₂i _ (isCompact_closedBall x ρ) hρU) (div_mul_cancel₀ (θ₂ x) (hθ₁ x hx.1).ne').symm
    hdens Q hQ
/-- **Mass of `τ(M, θ, ξ)` (Simon Ch. 6, Remark 3.2(3), with 2.7–2.8).**  If `T = τ(M, θ, ξ)` for a
rectifiable triple in `U`, then `M_W(T) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  For `Hⁿ`-a.e.
`x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal; with `dx^β` the coordinate wedges, the
Cauchy–Binet identity `∑_β ξ(x)(dx^β)² = 1` (from the expansion `α = ∑_β α(e_β) dx^β` applied to
`⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τₙ, ·⟩`) gives `|ξ(x)(α)| ≤ |α|`, hence `≤`, and makes `b = (ξ(dx^β))_β` a unit
vector with `ξ(∑_β b_β dx^β) = 1`.  For `≥`, exhaust `W ∩ U` by compact sets `K`; approximate
`1_K b` in `L¹(θ Hⁿ ⌞ K')`, `K'` a compact neighbourhood of `K`, by a continuous compactly
supported map, cut it off near `K`, retract it radially onto the unit ball, mollify and rescale.
The resulting test form `ω`, with `|ω| ≤ 1` and `spt ω ⊆ W`, has `T(ω) ≥ ∫_{K ∩ M} θ dHⁿ - ε`. -/
theorem Submission.fiw_im_mass_formula : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n U hU T M θ ξ hR hT W hW
  classical
  -- Generic analytic tools, stated for an arbitrary normed space of coefficients.
  -- (D) `L¹` density of continuous compactly supported functions for a finite measure: the proof
  -- of Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` (`p = 1`), whose file is not
  -- imported here.
  have hdense : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure (Eucl P))
      [IsFiniteMeasure μ] (f : Eucl P → E), MemLp f 1 μ → ∀ {ε : ℝ≥0∞}, ε ≠ 0 →
      ∃ g : Eucl P → E, HasCompactSupport g ∧ eLpNorm (f - g) 1 μ ≤ ε ∧
        Continuous g ∧ MemLp g 1 μ := by
    intro E _ _ μ _ f hf ε hε
    -- Urysohn approximation of `c • 1_s` for closed `s ⊆ u` open (Mathlib's
    -- `exists_continuous_eLpNorm_sub_le_of_closed`).
    have hury : ∀ {s u : Set (Eucl P)}, IsClosed s → IsOpen u → s ⊆ u → μ s ≠ ∞ →
        ∀ (c : E) {ε : ℝ≥0∞}, ε ≠ 0 → ∃ f : Eucl P → E,
          Continuous f ∧ eLpNorm (fun x => f x - s.indicator (fun _y => c) x) 1 μ ≤ ε ∧
            (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f 1 μ := by
      intro s u s_closed u_open hsu hs c ε hε
      obtain ⟨η, η_pos, hη⟩ :
          ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Eucl P), μ s ≤ η → NullMeasurableSet s μ →
              eLpNorm (s.indicator fun _x => c) 1 μ ≤ ε :=
        exists_eLpNorm_indicator_le ENNReal.one_ne_top c hε
      have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
      obtain ⟨V, sV, V_open, h'V, hV⟩ :
          ∃ (V : Set (Eucl P)), V ⊇ s ∧ IsOpen V ∧ μ V < ∞ ∧ μ (V \ s) < η :=
        s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
      let v := u ∩ V
      have hsv : s ⊆ v := subset_inter hsu sV
      have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
      obtain ⟨g, hgv, hgs, hg_range⟩ :=
        exists_continuous_zero_one_of_isClosed (u_open.inter V_open).isClosed_compl s_closed
          (disjoint_compl_left_iff.2 hsv)
      have g_norm : ∀ x, ‖g x‖ = g x := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
      have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
        intro x
        simp only [norm_smul, g_norm x]
        apply mul_le_of_le_one_left (norm_nonneg _)
        exact (hg_range x).2
      have gc_bd :
          ∀ x, ‖g x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
        intro x
        by_cases hv : x ∈ v
        · rw [← Set.sdiff_union_of_subset hsv] at hv
          rcases hv with hsv | hs
          · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
              Set.indicator_of_mem] using gc_bd0 x
          · simp [hgs hs, hs]
        · simp [hgv hv, show x ∉ s from fun h => hv (hsv h)]
      have gc_support : (Function.support fun x : Eucl P => g x • c) ⊆ v := by
        refine Function.support_subset_iff'.2 fun x hx => ?_
        simp only [hgv hx, Pi.zero_apply, zero_smul]
      have gc_mem : MemLp (fun x => g x • c) 1 μ := by
        refine MemLp.smul ?_ (memLp_top_const (μ := μ) c) (p := 1) (q := ∞) (r := 1)
        have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
        have : eLpNorm (v.indicator fun _x => (1 : ℝ)) 1 μ < ∞ :=
          (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
            simp [lt_top_iff_ne_top, hμv.ne]
        refine (eLpNorm_mono g.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
        by_cases hx : x ∈ v
        · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
            indicator_of_mem, CStarRing.norm_one]
        · simp only [hgv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
      refine ⟨fun x ↦ g x • c, by fun_prop,
        (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator s_closed.measurableSet)) gc_bd).trans ?_, gc_bd0,
          gc_support.trans inter_subset_left, gc_mem⟩
      exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
        ((u_open.measurableSet.inter V_open.measurableSet).diff
          s_closed.measurableSet).nullMeasurableSet
    suffices hex : ∃ g : Eucl P → E,
        eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ MemLp g 1 μ ∧ HasCompactSupport g by
      rcases hex with ⟨g, hg, g_cont, g_mem, g_support⟩
      exact ⟨g, g_support, hg, g_cont, g_mem⟩
    apply hf.induction_dense ENNReal.one_ne_top _ _ _ hε
    rotate_left
    · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
      exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
    intro c t ht htμ ε hε
    rcases exists_Lp_half E μ 1 hε with ⟨δ, δpos, hδ⟩
    obtain ⟨η, ηpos, hη⟩ :
        ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set (Eucl P), μ s ≤ η → NullMeasurableSet s μ →
            eLpNorm (s.indicator fun _x => c) 1 μ ≤ δ :=
      exists_eLpNorm_indicator_le ENNReal.one_ne_top c δpos.ne'
    have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
    obtain ⟨s, st, s_compact, s_closed, μs⟩ :
        ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
      ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
    have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
    have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) 1 μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
      exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
    obtain ⟨k, k_compact, sk⟩ : ∃ k : Set (Eucl P), IsCompact k ∧ s ⊆ interior k :=
      exists_compact_superset s_compact
    rcases hury s_closed isOpen_interior sk hsμ.ne c δpos.ne'
      with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
    have I3 : eLpNorm (f - t.indicator fun _y => c) 1 μ ≤ ε := by
      convert (hδ _ _ I2 I1).le using 2
      ext x
      simp
    refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
    rw [← Function.notMem_support]
    contrapose hx
    exact interior_subset (f_support hx)
  -- (S) Smoothing: a continuous compactly supported map with `tsupport ⊆ O` (`O` open) is a
  -- uniform limit of smooth maps with compact `tsupport ⊆ O` (convolution with a normalized
  -- bump, then a smooth cutoff equal to `1` on the support).
  have hmoll : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (O : Set (Eucl P)) (u : Eucl P → E), IsOpen O → Continuous u → HasCompactSupport u →
      tsupport u ⊆ O → ∀ ε : ℝ, 0 < ε → ∃ v : Eucl P → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ tsupport v ⊆ O ∧ HasCompactSupport v ∧
          ∀ x, ‖u x - v x‖ ≤ ε := by
    intro E _ _ _ O u hO hu huc huO ε hε
    obtain ⟨O', hO'o, hKO', hO'O, hO'c⟩ :=
      exists_open_between_and_isCompact_closure huc.isCompact hO huO
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hO'o (isClosed_tsupport u) hKO'
    obtain ⟨δ, hδ, huδ⟩ :=
      Metric.uniformContinuous_iff.mp (huc.uniformContinuous_of_continuous hu) ε hε
    obtain ⟨φ, hφs, hφc, hφd, hφr, hφ0⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
    have hφnn : ∀ y, 0 ≤ φ y := fun y => (hφr (mem_range_self y)).1
    have hφint : 0 < ∫ y, φ y :=
      hφd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hφc (fun y => hφnn y)
        (hφ0.symm ▸ one_ne_zero : φ 0 ≠ 0)
    set ψ : Eucl P → ℝ := fun y => (∫ z, φ z)⁻¹ * φ y with hψ_def
    have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hφd
    have hψc : HasCompactSupport ψ := hφc.mul_left
    have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hφint.le) (hφnn y)
    have hψs : Function.support ψ ⊆ ball 0 δ :=
      (Function.support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hφs)
    have hψ1 : ∫ y, ψ y = 1 := by
      rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hφint.ne']
    obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (u x) ≤ ε :=
      ⟨convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume,
        hψc.contDiff_convolution_left _ hψd hu.locallyIntegrable,
        fun x => dist_convolution_le hε.le hψs hψnn hψ1 hu.aestronglyMeasurable
          fun y hy => (huδ (mem_ball.mp hy)).le⟩
    have hv_supp : tsupport (fun x => χ x • g x) ⊆ closure O' := by
      refine (tsupport_smul_subset_left χ g).trans ?_
      rw [tsupport, hχs]
    refine ⟨fun x => χ x • g x, hχ.smul hg, hv_supp.trans hO'O,
      hO'c.of_isClosed_subset (isClosed_tsupport _) hv_supp, fun x => ?_⟩
    beta_reduce
    by_cases hx : x ∈ tsupport u
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  -- (R) The radial retraction `a ↦ a / max 1 ‖a‖` onto the closed unit ball is `2`-Lipschitz
  -- towards points of the ball.
  have hretr : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E), ‖b‖ ≤ 1 →
      ‖(max 1 ‖a‖)⁻¹ • a‖ ≤ 1 ∧ ‖(max 1 ‖a‖)⁻¹ • a - b‖ ≤ 2 * ‖a - b‖ := by
    intro E _ _ a b hb
    have hm : 0 < max 1 ‖a‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, inv_mul_le_iff₀ hm, mul_one]
      exact le_max_right _ _
    · rcases le_total ‖a‖ 1 with ha | ha
      · rw [max_eq_left ha, inv_one, one_smul]
        linarith [norm_nonneg (a - b)]
      · rw [max_eq_right ha]
        have ha0 : 0 < ‖a‖ := lt_of_lt_of_le one_pos ha
        have h1 : ‖‖a‖⁻¹ • a - a‖ = ‖a‖ - 1 := by
          have : ‖a‖⁻¹ • a - a = (‖a‖⁻¹ - 1) • a := by rw [sub_smul, one_smul]
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos, neg_sub, sub_mul,
            inv_mul_cancel₀ ha0.ne', one_mul]
          rw [sub_nonpos]
          exact inv_le_one_of_one_le₀ ha
        have h2 := norm_le_norm_sub_add a b
        calc ‖‖a‖⁻¹ • a - b‖ ≤ ‖‖a‖⁻¹ • a - a‖ + ‖a - b‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * ‖a - b‖ := by rw [h1]; linarith
  -- Linear algebra of `n`-covectors on `ℝ^P` (Simon 1.1–1.5) and Cauchy–Binet.
  set dx : SimonMultiIndex n P → Covector (Eucl P) n :=
    fun I => wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) with hdx
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1 with he
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P, dx β (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    simp only [hdx]
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
        by_contra! h
        apply hβγ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range β ⊆ Set.range γ := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range γ)
        rw [Set.ncard_range_of_injective γ.injective, Set.ncard_range_of_injective β.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [e, PiLp.single_apply, hi j]
  -- Coordinate expansion `α = ∑_β α(e_β) dx^β`.
  have hexp : ∀ α : Covector (Eucl P) n,
      α = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β • dx β := by
    intro α
    set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • dx β with hR
    have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
      intro γ
      rw [hR, ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    have h2 : ∀ v : Fin n → Fin P, Function.Injective v → R (e v) = α (e v) := by
      intro v hv
      have hsm : StrictMono (v ∘ Tuple.sort v) :=
        (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
      have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
      have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
      rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
        ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
        AlternatingMap.map_perm] at hγ
      exact smul_left_cancel _ hγ
    symm
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousAlternatingMap.coe_toAlternatingMap]
    exact h2 v hv
  -- The Euclidean coefficient norm as a sum over increasing multi-indices.
  have hnorm : ∀ α : Covector (Eucl P) n, covectorEuclideanNorm α =
      Real.sqrt (∑ β : SimonMultiIndex n P, (euclideanCovectorCoordinate α β) ^ 2) := by
    intro α
    unfold covectorEuclideanNorm
    congr 1
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij (fun β : SimonMultiIndex n P => (β : Fin n → Fin P))
    · intro β _
      simpa using β.strictMono
    · intro β _ γ _ h
      exact DFunLike.coe_injective h
    · intro I hI
      have hI' : StrictMono I := (Finset.mem_filter.mp hI).2
      exact ⟨OrderEmbedding.ofStrictMono I hI', Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
    · intro β _
      simp [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]
  -- Cauchy–Binet: for an orthonormal frame `τ` and `ζ = ±τ₁ ∧ ⋯ ∧ τₙ`,
  -- `|ζ(α)| ≤ |α|` and `∑_β ζ(dx^β)² = 1`.
  have hALG : ∀ τ : Fin n → Eucl P, Orthonormal ℝ τ → ∀ ζ : NVector (Eucl P) n,
      (ζ = simpleNVector τ ∨ ζ = -simpleNVector τ) →
      (∀ α : Covector (Eucl P) n, |ζ α| ≤ covectorEuclideanNorm α) ∧
        ∑ β : SimonMultiIndex n P, (ζ (dx β)) ^ 2 = 1 := by
    intro τ hτ ζ hζ
    set α₀ : Covector (Eucl P) n := wedgeCovectors n (fun i => innerSL ℝ (τ i)) with hα₀
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀, wedgeCovectors_apply_det]
      have h1 : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp [innerSL_apply_apply, orthonormal_iff_ite.mp hτ, Matrix.one_apply]
      rw [h1, Matrix.det_one]
    have hα₀e : ∀ β : SimonMultiIndex n P, euclideanCovectorCoordinate α₀ β = dx β τ := by
      intro β
      simp only [euclideanCovectorCoordinate, hα₀, hdx, wedgeCovectors_apply_det]
      rw [← Matrix.det_transpose]
      congr 1
      ext i j
      simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    have heval : ∀ α : Covector (Eucl P) n,
        α τ = ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate α β * dx β τ := by
      intro α
      conv_lhs => rw [hexp α]
      rw [ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hsum1 : ∑ β : SimonMultiIndex n P, (dx β τ) ^ 2 = 1 := by
      rw [← hα₀τ, heval α₀]
      simp only [hα₀e, sq]
    obtain ⟨s, hs, hζs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ∀ α : Covector (Eucl P) n, ζ α = s * α τ := by
      rcases hζ with rfl | rfl
      · exact ⟨1, Or.inl rfl, fun α => by simp⟩
      · exact ⟨-1, Or.inr rfl, fun α => by simp⟩
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    refine ⟨fun α => ?_, ?_⟩
    · rw [hζs, abs_mul, habs, one_mul, hnorm, heval]
      apply Real.abs_le_sqrt
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun β => euclideanCovectorCoordinate α β) (fun β => dx β τ)
      rwa [hsum1, mul_one] at this
    · simp only [hζs, mul_pow, hs2, one_mul, hsum1]
  -- Coordinates on `Λⁿ`: `L y = ∑_β y_β dx^β` for `y ∈ ℝ^{multi-indices}` (Euclidean norm), so
  -- `|L y| = ‖y‖`, and `Bv ζ = (ζ(dx^β))_β`.
  set H : Measure (Eucl P) := (μHE[n] : Measure (Eucl P)) with hH
  set L : EuclideanSpace ℝ (SimonMultiIndex n P) →L[ℝ] Covector (Eucl P) n :=
    ∑ β : SimonMultiIndex n P, (EuclideanSpace.proj β).smulRight (dx β) with hL
  have hLapp : ∀ y : EuclideanSpace ℝ (SimonMultiIndex n P),
      L y = ∑ β : SimonMultiIndex n P, y.ofLp β • dx β := by
    intro y
    rw [hL, sum_apply]
    rfl
  have hLnorm : ∀ y : EuclideanSpace ℝ (SimonMultiIndex n P),
      covectorEuclideanNorm (L y) = ‖y‖ := by
    intro y
    rw [hnorm, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hc : euclideanCovectorCoordinate (L y) γ = y.ofLp γ := by
      change (L y) (e γ) = y.ofLp γ
      rw [hLapp, ContinuousAlternatingMap.sum_apply]
      simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc, Real.norm_eq_abs, sq_abs]
  have hLζ : ∀ (ζ : NVector (Eucl P) n) (y : EuclideanSpace ℝ (SimonMultiIndex n P)),
      ζ (L y) = ∑ β : SimonMultiIndex n P, y.ofLp β * ζ (dx β) := by
    intro ζ y
    rw [hLapp, map_sum]
    simp only [map_smul, smul_eq_mul]
  set Bv : NVector (Eucl P) n → EuclideanSpace ℝ (SimonMultiIndex n P) :=
    fun ζ => WithLp.toLp 2 (fun β => ζ (dx β)) with hBv
  have hBvc : Continuous Bv :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun β => continuous_id.clm_apply continuous_const)
  -- Pointwise consequences of the orientation condition, `Hⁿ`-a.e. on `M`.
  have hpt : ∀ᵐ x ∂(H.restrict M),
      (∀ α : Covector (Eucl P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ ‖Bv (ξ x)‖ = 1 ∧
        ξ x (L (Bv (ξ x))) = 1 := by
    filter_upwards [hR.orients] with x hx
    obtain ⟨τ, hτ, -, hξτ⟩ := hx
    obtain ⟨h1, h2⟩ := hALG τ hτ (ξ x) hξτ
    refine ⟨h1, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]
      simp only [hBv, Real.norm_eq_abs, sq_abs, h2, Real.sqrt_one]
    · rw [hLζ, ← h2]
      simp only [hBv, sq]
  -- `M_W(T) ≤ ∫_{M ∩ W} θ dHⁿ`: `|T(ω)| ≤ ∫_M θ |ξ(ω)| dHⁿ` and `|ξ(ω)| ≤ |ω| ≤ 1_W`.
  have hle : T.massOn W ≤ ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H := by
    apply sSup_le
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    change ENNReal.ofReal (T ω) ≤ _
    rw [hT ω]
    calc ENNReal.ofReal (tauAction n M θ ξ ω)
        ≤ ENNReal.ofReal ‖∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x) ∂H‖ :=
          ENNReal.ofReal_le_ofReal (Real.le_norm_self _)
      _ ≤ ENNReal.ofReal (∫⁻ x in M,
            ENNReal.ofReal ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)‖ ∂H).toReal :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)
      _ ≤ ∫⁻ x in M, ENNReal.ofReal ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)‖ ∂H :=
          ENNReal.ofReal_toReal_le
      _ ≤ ∫⁻ x in M, W.indicator (fun x => ENNReal.ofReal (θ x)) x ∂H := by
          apply lintegral_mono_ae
          filter_upwards [hpt, ae_restrict_mem₀ hR.nullMeasurableSet] with x hx hxM
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hR.pos x hxM)]
            exact mul_le_of_le_one_right (hR.pos x hxM).le ((hx.1 _).trans (hω1 x))
          · have h0 : (ω : DifferentialForm (Eucl P) n) x = 0 :=
              image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h)
            rw [h0, map_zero, mul_zero, norm_zero, ENNReal.ofReal_zero]
            exact bot_le
      _ = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H := by
          rw [lintegral_indicator hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
            inter_comm]
  -- `∫_{K ∩ M} θ dHⁿ ≤ M_W(T)` for compact `K ⊆ W ∩ U`.
  have hmain : ∀ K : Set (Eucl P), IsCompact K → K ⊆ W ∩ U →
      ∫⁻ x in K ∩ M, ENNReal.ofReal (θ x) ∂H ≤ T.massOn W := by
    intro K hK hKV
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hθK : IntegrableOn θ (K ∩ M) H := by
      rw [inter_comm]
      exact hR.integrableOn K hK (hKV.trans inter_subset_right)
    have hKMn : NullMeasurableSet (K ∩ M) H := hKm.nullMeasurableSet.inter hR.nullMeasurableSet
    rw [← ofReal_integral_eq_lintegral_ofReal hθK
      ((ae_restrict_mem₀ hKMn).mono fun x hx => (hR.pos x hx.2).le)]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨ω, hωad, hωT⟩ : ∃ ω ∈ massAdmissibleOn U n W,
        (∫ x in K ∩ M, θ x ∂H) - ε ≤ T ω := by
      -- Open sets `K ⊆ O₁ ⊆ closure O₁ ⊆ O₂ ⊆ closure O₂ = K' ⊆ W ∩ U`, `K'` compact.
      obtain ⟨O₂, hO₂o, hKO₂, hO₂V, hO₂c⟩ :=
        exists_open_between_and_isCompact_closure hK (hW.inter hU) hKV
      obtain ⟨O₁, hO₁o, hKO₁, hO₁O₂, hO₁c⟩ :=
        exists_open_between_and_isCompact_closure hK hO₂o hKO₂
      set K' := closure O₂ with hK'
      have hK'm : MeasurableSet K' := isClosed_closure.measurableSet
      have hK'U : K' ⊆ U := hO₂V.trans inter_subset_right
      have hKK' : K ⊆ K' := hKO₂.trans subset_closure
      have hθK' : IntegrableOn θ (K' ∩ M) H := by
        rw [inter_comm]
        exact hR.integrableOn K' hO₂c hK'U
      -- The finite measure `ν = θ Hⁿ ⌞ (K' ∩ M)`.
      set ν : Measure (Eucl P) :=
        (H.restrict (K' ∩ M)).withDensity (fun x => ENNReal.ofReal (θ x)) with hν
      have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hθK'.hasFiniteIntegral
      have hνac : ν ≪ H.restrict M :=
        (withDensity_absolutelyContinuous _ _).trans
          (Measure.absolutelyContinuous_of_le (Measure.restrict_mono inter_subset_right le_rfl))
      -- The target `f = 1_K (ζ(dx^β))_β`, `‖f‖ ≤ 1`.
      set f : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        K.indicator (fun x => Bv (ξ x)) with hf
      have hfM : AEStronglyMeasurable f (H.restrict M) :=
        (hBvc.comp_aestronglyMeasurable hR.aestronglyMeasurable).indicator hKm
      have hf1 : ∀ᵐ x ∂(H.restrict M), ‖f x‖ ≤ 1 := by
        filter_upwards [hpt] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK, hx.2.1]
        · rw [hf, indicator_of_notMem hxK, norm_zero]
          exact zero_le_one
      have hfmem : MemLp f 1 ν := MemLp.of_bound (hfM.mono_ac hνac) 1 (hνac.ae_le hf1)
      -- Tolerances.
      set C : ℝ := (ν univ).toReal with hC
      have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
      set ε₁ : ℝ := (ε : ℝ) / 4 with hε₁
      set ε₂ : ℝ := (ε : ℝ) / (4 * (C + 1)) with hε₂
      have hε₁0 : 0 < ε₁ := by positivity
      have hε₂0 : 0 < ε₂ := by positivity
      -- `L¹(ν)` approximation of `f` by a continuous compactly supported `γ₀`.
      obtain ⟨γ₀, -, hγ₀ε, hγ₀c, -⟩ :=
        hdense (EuclideanSpace ℝ (SimonMultiIndex n P)) ν f hfmem
          (ε := ENNReal.ofReal ε₁) (ENNReal.ofReal_pos.mpr hε₁0).ne'
      -- Cutoff `χ` (`= 1` on `K`, `= 0` off `O₁`), then the radial retraction.
      obtain ⟨χ, hχ0, hχ1, hχr⟩ := exists_continuous_zero_one_of_isClosed hO₁o.isClosed_compl
        hK.isClosed (disjoint_compl_left_iff_subset.mpr hKO₁)
      set γ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        fun x => (max 1 ‖χ x • γ₀ x‖)⁻¹ • (χ x • γ₀ x) with hγ
      have hγc : Continuous γ := by
        have h1 : Continuous fun x => χ x • γ₀ x := χ.continuous.smul hγ₀c
        exact ((continuous_const.max h1.norm).inv₀ fun x =>
          (lt_of_lt_of_le one_pos (le_max_left _ _)).ne').smul h1
      have hγs : Function.support γ ⊆ O₁ := by
        intro x hx
        by_contra hxO
        apply hx
        have h0 : χ x = 0 := hχ0 hxO
        simp only [hγ, h0, zero_smul, smul_zero]
      have hγts : tsupport γ ⊆ O₂ := (closure_mono hγs).trans hO₁O₂
      have hγcs : HasCompactSupport γ :=
        hO₁c.of_isClosed_subset (isClosed_tsupport _) (closure_mono hγs)
      have hγ1 : ∀ x, ‖γ x‖ ≤ 1 := fun x => (hretr _ (χ x • γ₀ x) 0 (by simp)).1
      have hγf : ∀ x, ‖f x‖ ≤ 1 → ‖γ x - f x‖ ≤ 2 * ‖γ₀ x - f x‖ := by
        intro x hx
        refine (hretr _ (χ x • γ₀ x) (f x) hx).2.trans ?_
        gcongr
        by_cases hxK : x ∈ K
        · rw [show χ x = 1 from hχ1 hxK, one_smul]
        · rw [hf, indicator_of_notMem hxK, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hχr x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχr x).2
      -- Smoothing and rescaling: `ψ = (1 + ε₂)⁻¹ φ`, `‖ψ‖ ≤ 1`, `‖ψ - γ‖ ≤ 2 ε₂`.
      obtain ⟨φ, hφd, hφO₂, hφc, hφε⟩ :=
        hmoll (EuclideanSpace ℝ (SimonMultiIndex n P)) O₂ γ hO₂o hγc hγcs hγts ε₂ hε₂0
      have hφ1 : ∀ x, ‖φ x‖ ≤ 1 + ε₂ := fun x => by
        have h1 := norm_le_norm_sub_add (φ x) (γ x)
        rw [norm_sub_rev] at h1
        linarith [hφε x, hγ1 x]
      set ψ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex n P) :=
        fun x => (1 + ε₂)⁻¹ • φ x with hψ
      have hε₂1 : (0 : ℝ) < 1 + ε₂ := by linarith
      have hψ1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
        rw [hψ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε₂1, inv_mul_le_iff₀ hε₂1,
          mul_one]
        exact hφ1 x
      have hψγ : ∀ x, ‖ψ x - γ x‖ ≤ 2 * ε₂ := fun x => by
        have h1 : ‖ψ x - φ x‖ ≤ ε₂ := by
          have h2 : ψ x - φ x = ((1 + ε₂)⁻¹ - 1) • φ x := by rw [hψ, sub_smul, one_smul]
          have h3 : |(1 + ε₂)⁻¹ - 1| * (1 + ε₂) = ε₂ := by
            rw [abs_of_nonpos (by rw [sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith)),
              neg_sub, sub_mul, inv_mul_cancel₀ hε₂1.ne', one_mul]
            ring
          rw [h2, norm_smul, Real.norm_eq_abs]
          calc |(1 + ε₂)⁻¹ - 1| * ‖φ x‖ ≤ |(1 + ε₂)⁻¹ - 1| * (1 + ε₂) :=
                mul_le_mul_of_nonneg_left (hφ1 x) (abs_nonneg _)
            _ = ε₂ := h3
        calc ‖ψ x - γ x‖ ≤ ‖ψ x - φ x‖ + ‖φ x - γ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ε₂ + ε₂ := add_le_add h1 (by rw [norm_sub_rev]; exact hφε x)
          _ = 2 * ε₂ := by ring
      have hψc : Continuous ψ := by
        have hφcont : Continuous φ := hφd.continuous
        rw [hψ]
        fun_prop
      have hψts : tsupport ψ ⊆ O₂ :=
        (tsupport_comp_subset (g := fun y => (1 + ε₂)⁻¹ • y) (smul_zero _) φ).trans hφO₂
      have hψcs : HasCompactSupport ψ :=
        hφc.comp_left (g := fun y => (1 + ε₂)⁻¹ • y) (smul_zero _)
      -- The test form `ω' = L ∘ ψ`.
      set ω' : Eucl P → Covector (Eucl P) n := fun x => L (ψ x) with hω'
      have hω'd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω' :=
        L.contDiff.comp (hφd.const_smul ((1 + ε₂)⁻¹))
      have hω'ts : tsupport ω' ⊆ O₂ :=
        (tsupport_comp_subset (g := fun y => L y) (map_zero L) ψ).trans hψts
      have hω'c : HasCompactSupport ω' := hψcs.comp_left (g := fun y => L y) (map_zero L)
      have hω'cont : Continuous ω' := L.continuous.comp hψc
      have hO₂W : O₂ ⊆ W ∩ U := subset_closure.trans hO₂V
      refine ⟨⟨ω', ⟨hω'd, hω'c⟩, hω'ts.trans (hO₂W.trans inter_subset_right)⟩,
        ⟨hω'ts.trans (hO₂W.trans inter_subset_left), fun x => ?_⟩, ?_⟩
      · change covectorEuclideanNorm (L (ψ x)) ≤ 1
        rw [hLnorm]
        exact hψ1 x
      · -- `∫_{K ∩ M} θ - ε ≤ T ω`.
        rw [hT]
        change (∫ x in K ∩ M, θ x ∂H) - ε ≤ ∫ x in M, θ x * ξ x (ω' x) ∂H
        have hg₁ : Integrable (K.indicator θ) (H.restrict M) := by
          rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
          exact hθK
        have hξω : AEStronglyMeasurable (fun x => ξ x (ω' x)) (H.restrict M) :=
          (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
            (hR.aestronglyMeasurable.prodMk hω'cont.aestronglyMeasurable)
        have hξω1 : ∀ᵐ x ∂(H.restrict M), ‖ξ x (ω' x)‖ ≤ 1 := by
          filter_upwards [hpt] with x hx
          rw [Real.norm_eq_abs]
          exact (hx.1 _).trans ((hLnorm _).trans_le (hψ1 x))
        have hω'0 : ∀ x, x ∉ K' → ω' x = 0 := fun x hx =>
          image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hω'ts h))
        have hg₂ : Integrable (fun x => θ x * ξ x (ω' x)) (H.restrict M) := by
          have h1 : Integrable (K'.indicator θ) (H.restrict M) := by
            rw [integrable_indicator_iff hK'm, IntegrableOn, Measure.restrict_restrict hK'm]
            exact hθK'
          refine (h1.mul_bdd hξω hξω1).congr (Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ K'
          · simp only [indicator_of_mem hx]
          · simp only [indicator_of_notMem hx, hω'0 x hx, map_zero, mul_zero]
        have hint : (∫ x in K ∩ M, θ x ∂H) = ∫ x in M, K.indicator θ x ∂H := by
          rw [integral_indicator hKm, Measure.restrict_restrict hKm]
        have hkey : ∫⁻ x in M, ENNReal.ofReal ‖K.indicator θ x - θ x * ξ x (ω' x)‖ ∂H ≤
            ENNReal.ofReal ε := by
          have hθm : AEMeasurable (fun x => ENNReal.ofReal (θ x)) (H.restrict (K' ∩ M)) :=
            hθK'.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          have hfK' : AEStronglyMeasurable f (H.restrict (K' ∩ M)) :=
            hfM.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
          have hgm : AEMeasurable (fun x => ENNReal.ofReal ‖f x - ψ x‖) (H.restrict (K' ∩ M)) :=
            (hfK'.sub hψc.aestronglyMeasurable).norm.aemeasurable.ennreal_ofReal
          have hfγ₀ : AEStronglyMeasurable (f - γ₀) ν :=
            (hfM.mono_ac hνac).sub hγ₀c.aestronglyMeasurable
          have hγ₀ε' : ∫⁻ x, ‖f x - γ₀ x‖ₑ ∂ν ≤ ENNReal.ofReal ε₁ := by
            rw [eLpNorm_one_eq_lintegral_enorm hfγ₀] at hγ₀ε
            exact hγ₀ε
          calc ∫⁻ x in M, ENNReal.ofReal ‖K.indicator θ x - θ x * ξ x (ω' x)‖ ∂H
              ≤ ∫⁻ x in M, K'.indicator
                  (fun x => ENNReal.ofReal (θ x) * ENNReal.ofReal ‖f x - ψ x‖) x ∂H := by
                apply lintegral_mono_ae
                filter_upwards [hpt, ae_restrict_mem₀ hR.nullMeasurableSet] with x hx hxM
                have hθx := hR.pos x hxM
                have hid : K.indicator θ x - θ x * ξ x (ω' x) = θ x * ξ x (L (f x - ψ x)) := by
                  rw [map_sub L, map_sub (ξ x)]
                  by_cases hxK : x ∈ K
                  · rw [indicator_of_mem hxK, hf, indicator_of_mem hxK, hx.2.2]
                    ring
                  · rw [indicator_of_notMem hxK, hf, indicator_of_notMem hxK, map_zero, map_zero]
                    ring
                rw [hid]
                by_cases hxK' : x ∈ K'
                · rw [indicator_of_mem hxK', ← ENNReal.ofReal_mul hθx.le]
                  apply ENNReal.ofReal_le_ofReal
                  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθx]
                  exact mul_le_mul_of_nonneg_left ((hx.1 _).trans (hLnorm _).le) hθx.le
                · have hf0 : f x = 0 := indicator_of_notMem (fun h => hxK' (hKK' h)) _
                  have hψ0 : ψ x = 0 :=
                    image_eq_zero_of_notMem_tsupport fun h => hxK' (subset_closure (hψts h))
                  rw [indicator_of_notMem hxK', hf0, hψ0, sub_zero, map_zero, map_zero, mul_zero,
                    norm_zero, ENNReal.ofReal_zero]
            _ = ∫⁻ x, ENNReal.ofReal ‖f x - ψ x‖ ∂ν := by
                rw [lintegral_indicator hK'm, Measure.restrict_restrict hK'm]
                exact (lintegral_withDensity_eq_lintegral_mul₀ hθm hgm).symm
            _ ≤ ∫⁻ x, (2 * ‖f x - γ₀ x‖ₑ + ENNReal.ofReal (2 * ε₂)) ∂ν := by
                apply lintegral_mono_ae
                filter_upwards [hνac.ae_le hf1] with x hx
                have h1 : ‖f x - ψ x‖ ≤ 2 * ‖f x - γ₀ x‖ + 2 * ε₂ :=
                  calc ‖f x - ψ x‖ ≤ ‖f x - γ x‖ + ‖γ x - ψ x‖ :=
                        norm_sub_le_norm_sub_add_norm_sub _ _ _
                    _ ≤ 2 * ‖f x - γ₀ x‖ + 2 * ε₂ := by
                        rw [norm_sub_rev (f x) (γ x), norm_sub_rev (f x) (γ₀ x),
                          norm_sub_rev (γ x) (ψ x)]
                        exact add_le_add (hγf x hx) (hψγ x)
                calc ENNReal.ofReal ‖f x - ψ x‖ ≤ ENNReal.ofReal (2 * ‖f x - γ₀ x‖ + 2 * ε₂) :=
                      ENNReal.ofReal_le_ofReal h1
                  _ = 2 * ‖f x - γ₀ x‖ₑ + ENNReal.ofReal (2 * ε₂) := by
                      rw [ENNReal.ofReal_add (by positivity) (by positivity),
                        ENNReal.ofReal_mul (by norm_num), ofReal_norm, ENNReal.ofReal_ofNat]
            _ = 2 * ∫⁻ x, ‖f x - γ₀ x‖ₑ ∂ν + ENNReal.ofReal (2 * ε₂) * ν univ := by
                rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
                  lintegral_const]
            _ ≤ 2 * ENNReal.ofReal ε₁ + ENNReal.ofReal (2 * ε₂) * ENNReal.ofReal C := by
                rw [hC, ENNReal.ofReal_toReal (measure_ne_top ν univ)]
                gcongr
            _ = ENNReal.ofReal (2 * ε₁ + 2 * ε₂ * C) := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity),
                  ENNReal.ofReal_mul (p := 2 * ε₂) (q := C) (by positivity),
                  ENNReal.ofReal_mul (p := 2) (q := ε₁) (by norm_num), ENNReal.ofReal_ofNat]
            _ ≤ ENNReal.ofReal ε := by
                apply ENNReal.ofReal_le_ofReal
                have h1 : ε₂ * C + ε₂ = (ε : ℝ) / 4 := by
                  rw [hε₂]
                  field_simp
                rw [hε₁]
                linarith
        have h1 := norm_integral_le_lintegral_norm (μ := H.restrict M)
          (fun x => K.indicator θ x - θ x * ξ x (ω' x))
        rw [integral_sub hg₁ hg₂] at h1
        have h2 := (Real.le_norm_self _).trans
          (h1.trans (ENNReal.toReal_le_of_le_ofReal hε0.le hkey))
        rw [hint]
        linarith
    calc ENNReal.ofReal (∫ x in K ∩ M, θ x ∂H) ≤ ENNReal.ofReal (T ω + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (T ω) + ε := by rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ T.massOn W + ε := add_le_add_left (T.le_massOn hωad) _
  -- `∫_{M ∩ W} θ dHⁿ ≤ M_W(T)`: exhaust `W ∩ U` by compact sets.
  have hge : ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂H ≤ T.massOn W := by
    have hVo : IsOpen (W ∩ U) := hW.inter hU
    obtain ⟨F, hFc, hFV, hFU, hFm⟩ := hVo.exists_iUnion_isClosed
    set Kk : ℕ → Set (Eucl P) := fun k => F k ∩ closedBall 0 k with hKk
    have hKkc : ∀ k, IsCompact (Kk k) := fun k =>
      (isCompact_closedBall (0 : Eucl P) (k : ℝ)).inter_left (hFc k)
    have hKkV : ∀ k, Kk k ⊆ W ∩ U := fun k => inter_subset_left.trans (hFV k)
    have hKkm : Monotone Kk := fun k l hkl =>
      inter_subset_inter (hFm hkl) (Metric.closedBall_subset_closedBall (by exact_mod_cast hkl))
    have hKkU : ⋃ k, Kk k = W ∩ U := by
      refine Subset.antisymm (iUnion_subset hKkV) fun x hx => ?_
      rw [← hFU] at hx
      obtain ⟨k₀, hk₀⟩ := mem_iUnion.mp hx
      obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.mpr ⟨max k₀ k₁, hFm (le_max_left _ _) hk₀, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact hk₁.trans (by exact_mod_cast le_max_right _ _)
    set ν₀ : Measure (Eucl P) := (H.restrict M).withDensity (fun x => ENNReal.ofReal (θ x))
      with hν₀
    have hν₀A : ∀ A : Set (Eucl P), MeasurableSet A →
        ν₀ A = ∫⁻ x in A ∩ M, ENNReal.ofReal (θ x) ∂H := by
      intro A hA
      rw [hν₀, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hMW : M ∩ W = (W ∩ U) ∩ M := by
      ext x
      constructor
      · rintro ⟨hxM, hxW⟩
        exact ⟨⟨hxW, hR.subset hxM⟩, hxM⟩
      · rintro ⟨⟨hxW, -⟩, hxM⟩
        exact ⟨hxM, hxW⟩
    rw [hMW, ← hν₀A _ hVo.measurableSet, ← hKkU, hKkm.measure_iUnion]
    refine iSup_le fun k => ?_
    rw [hν₀A _ (hKkc k).isClosed.measurableSet]
    exact hmain (Kk k) (hKkc k) (hKkV k)
  exact le_antisymm hle hge

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
