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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
