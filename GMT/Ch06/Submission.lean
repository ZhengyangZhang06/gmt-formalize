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

/-- The coordinate covector `dx^α = wedgeCovectors n (proj ∘ α)` on `ℝ^N` is dual to the
coordinate frames: `dx^α(e_α) = 1`, `dx^α(e_{α'}) = 0` for every other increasing multi-index
`α'`, and `covectorEuclideanNorm (c • dx^α) = |c|`. -/
theorem Submission.isoperimetric_coord_covector_eval : ∀ (n N : ℕ) (α : SimonMultiIndex n N), (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 1 ∧ (∀ α' : SimonMultiIndex n N, α' ≠ α → (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n) (fun j => EuclideanSpace.single (α' j) (1 : ℝ)) = 0) ∧ ∀ c : ℝ, covectorEuclideanNorm (c • (wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) : Covector (Eucl N) n)) = |c| := by
  intro n N α
  classical
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) with hη
  -- Kronecker property on increasing coordinate frames: `dx^α(e_I) = δ_{α I}`.
  have hK : ∀ I : Fin n → Fin N, StrictMono I →
      η (fun j => EuclideanSpace.single (I j) (1 : ℝ)) = if I = ⇑α then 1 else 0 := by
    intro I hI
    rw [hη, wedgeCovectors_apply_det]
    split_ifs with hIα
    · -- the matrix `[δ_{α i, α j}]` is the identity
      subst hIα
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [Matrix.one_apply, PiLp.single_apply, α.injective.eq_iff]
    · -- some `α i` is not among the `I j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, α i ≠ I j := by
        by_contra! h
        apply hIα
        rw [← StrictMono.range_inj_of_wellFoundedLT hI α.strictMono]
        have hsub : Set.range α ⊆ Set.range I := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range I)).symm
        rw [Set.ncard_range_of_injective hI.injective, Set.ncard_range_of_injective α.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hK α α.strictMono
  · intro α' hα'
    rw [hK α' α'.strictMono, ite_eq_right fun h => hα' (DFunLike.coe_injective h)]
  · intro c
    -- only the summand `I = α` survives, and it contributes `c²`
    have hs : ∀ I : Fin n → Fin N, (if StrictMono I then
        ((c • η) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (I i))) ^ 2 else 0) =
        if I = ⇑α then c ^ 2 else 0 := by
      intro I
      by_cases hI : StrictMono I
      · rw [ite_eq_left hI]
        simp only [EuclideanSpace.basisFun_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        rw [hK I hI]
        split_ifs <;> ring
      · have hIα : I ≠ ⇑α := fun h => hI (h ▸ α.strictMono)
        rw [ite_eq_right hI, ite_eq_right hIα]
    rw [covectorEuclideanNorm, Finset.sum_congr rfl fun I _ => hs I, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _), Real.sqrt_sq_eq_abs]
/-- Smooth cut-off for a lattice face: for `ρ, δ > 0` there is a compactly supported smooth
`φ : ℝ^N → [0, 1]` equal to `1` on the shrunken face
`{x : ρ(zᵢ + δ) ≤ xᵢ ≤ ρ(zᵢ + 1 − δ) (i ∈ α), xᵢ = ρ zᵢ (i ∉ α)}` and vanishing on every other
lattice face `ρ (z' + F_α)`, `z' ≠ z`, of the same direction `α`. -/
theorem Submission.isoperimetric_lattice_face_cutoff :
    ∀ (n N : ℕ) (ρ δ : ℝ) (z : Fin N → ℤ) (α : SimonMultiIndex n N), 0 < ρ → 0 < δ →
      ∃ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x : Eucl N, (∀ i : Fin N,
          (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
          (i ∉ range α → x i = ρ * (z i : ℝ))) → φ x = 1) ∧
        ∀ z' : Fin N → ℤ, z' ≠ z → ∀ x ∈ latticeFace ρ ((z', α) : LatticeFaceIndex n N),
          φ x = 0 := by
  intro n N ρ δ z α hρ hδ
  -- `K`: the shrunken face; `L ⊇ O ⊇ K`: a closed and an open enlarged box (margins `ρδ/2`
  -- along `range α`, transversal slab of half-width `ρ/2`).
  set K : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
    (i ∉ range α → x i = ρ * (z i : ℝ))} with hK
  set L : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ / 2) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ / 2)) ∧
    (i ∉ range α → |x i - ρ * (z i : ℝ)| ≤ ρ / 2)} with hL
  set O : Set (Eucl N) := {x | ∀ i : Fin N,
    (i ∈ range α → ρ * ((z i : ℝ) + δ / 2) < x i ∧ x i < ρ * ((z i : ℝ) + 1 - δ / 2)) ∧
    (i ∉ range α → |x i - ρ * (z i : ℝ)| < ρ / 2)} with hO
  have hc : ∀ i : Fin N, Continuous fun x : Eucl N => x i := fun i => PiLp.continuous_apply 2 _ i
  -- Step 1: `K` and `L` are closed, `O` is open.
  have hKc : IsClosed K := by
    rw [hK, ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isClosed_eq (hc i) continuous_const
  have hLc : IsClosed L := by
    rw [hL, ofPred_forall]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isClosed_le (((hc i).sub continuous_const).abs) continuous_const
  have hOo : IsOpen O := by
    rw [hO, ofPred_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hi : i ∈ range α
    · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isOpen_lt continuous_const (hc i)).inter (isOpen_lt (hc i) continuous_const)
    · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
      exact isOpen_lt (((hc i).sub continuous_const).abs) continuous_const
  -- Step 2: `K ⊆ O ⊆ L`, hence `K ⊆ interior L`.
  have hKO : K ⊆ O := by
    intro x hx i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    · rw [(hx i).2 hi, sub_self, abs_zero]
      positivity
  have hOL : O ⊆ L := by
    intro x hx i
    exact ⟨fun hi => ⟨((hx i).1 hi).1.le, ((hx i).1 hi).2.le⟩, fun hi => ((hx i).2 hi).le⟩
  have hKL : K ⊆ interior L := hKO.trans (interior_maximal hOL hOo)
  -- Step 3: `L` is compact, being a closed subset of a compact coordinate box.
  have hLk : IsCompact L := by
    have hB : IsCompact (WithLp.toLp 2 '' (univ.pi fun i : Fin N =>
        Icc (ρ * (z i : ℝ) - ρ) (ρ * (z i : ℝ) + ρ)) : Set (Eucl N)) :=
      (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
    refine hB.of_isClosed_subset hLc fun x hx =>
      ⟨WithLp.ofLp x, fun i _ => ?_, WithLp.toLp_ofLp 2 x⟩
    by_cases hi : i ∈ range α
    · obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    · have h := abs_le.1 ((hx i).2 hi)
      constructor <;> nlinarith
  -- Steps 4–5: the smooth Urysohn function for `K ⊆ interior L`; it vanishes off the compact `L`.
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Eucl N)) (n := (⊤ : ℕ∞)) hKc hKL
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, HasCompactSupport.intro hLk hf0,
    fun x => hf01 x, fun x hx => hf1.self_of_nhdsSet x hx, ?_⟩
  -- Step 6: every point of another face of direction `α` lies outside `L`.
  intro z' hz' x hx
  apply hf0
  intro hxL
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz'
  have hzi : (z' i : ℝ) + 1 ≤ z i ∨ (z i : ℝ) + 1 ≤ z' i := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  simp only [latticeFace, mem_ofPred_eq] at hx
  by_cases hA : i ∈ range α
  · obtain ⟨h1, h2⟩ := (hx i).1 hA
    obtain ⟨h3, h4⟩ := (hxL i).1 hA
    rcases hzi with h | h <;> nlinarith
  · have h1 := (hx i).2 hA
    have h3 := abs_le.1 ((hxL i).2 hA)
    rw [h1] at h3
    rcases hzi with h | h <;> nlinarith
/-- Integrals over a lattice face as integrals over the parameter cube: for every `g`,
`∫_{latticeFace ρ G} g dHᵈ = ∫_{[0,ρ]^d} g(∑_l ρ w_l e_l + ∑_j s_j e_{γ(j)}) ds`, `G = (w, γ)`.
The map `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` is an isometry (`(e_{γ(j)})_j` is orthonormal)
whose range contains the face, so `L_* Hᵈ = Hᵈ ⌞ range L` and the integral is pulled back along
`L` and then along the volume-preserving `toLp : (Fin d → ℝ) → ℝᵈ`; the face pulls back to
`[0,ρ]^d`. -/
theorem Submission.br_latticeFace_setIntegral_eq_cube :
    ∀ (P d : ℕ) (ρ : ℝ) (G : LatticeFaceIndex d P) (g : Eucl P → ℝ),
      ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P)) =
        ∫ s in Set.Icc (0 : Fin d → ℝ) (fun _ => ρ),
          g (∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (G.2 j) (1 : ℝ)) := by
  intro P d ρ G g
  -- The parametrization `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` of the face.
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin d) → Eucl P, ∀ t, L t =
      ∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
        ∑ j, t j • EuclideanSpace.single (G.2 j) (1 : ℝ) := ⟨_, fun _ => rfl⟩
  -- Coordinates: `L(t)_{γ(j)} = ρ w_{γ(j)} + t_j` and `L(t)_l = ρ w_l` for `l ∉ range γ`.
  have hcoord : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P),
      L t l = ρ * (G.1 l : ℝ) + ∑ j, if l = G.2 j then t j else 0 := by
    intro t l
    rw [hL]
    simp [Pi.single_apply]
  have hcoord₁ : ∀ (t : EuclideanSpace ℝ (Fin d)) (j : Fin d),
      L t (G.2 j) = ρ * (G.1 (G.2 j) : ℝ) + t j := by
    intro t j
    rw [hcoord]
    simp
  have hcoord₂ : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P), l ∉ Set.range G.2 →
      L t l = ρ * (G.1 l : ℝ) := by
    intro t l hl
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hl ⟨j, h.symm⟩
  -- `L` is an isometry because `(e_{γ(j)})_j` is orthonormal.
  have hv : Orthonormal ℝ (fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).comp _ G.2.injective
  have hiso : Isometry L := by
    refine Isometry.of_dist_eq fun t t' => ?_
    have hdiff : L t - L t' = ∑ j, (t j - t' j) • EuclideanSpace.single (G.2 j) (1 : ℝ) := by
      rw [hL, hL]
      simp [sub_smul, Finset.sum_sub_distrib]
    have h2 : ‖L t - L t'‖ ^ 2 = ‖t - t'‖ ^ 2 := by
      rw [hdiff, ← real_inner_self_eq_norm_sq, hv.inner_sum, EuclideanSpace.norm_sq_eq]
      simp [sq]
    rw [dist_eq_norm, dist_eq_norm]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  -- The face lies in the range of `L`.
  have hrange : latticeFace ρ G ⊆ Set.range L := by
    intro x hx
    refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), PiLp.ext fun l => ?_⟩
    by_cases hl : l ∈ Set.range G.2
    · obtain ⟨j, rfl⟩ := hl
      rw [hcoord₁]
      simp
    · rw [hcoord₂ _ _ hl]
      exact ((hx l).2 hl).symm
  -- The face pulls back to the cube `[0,ρ]^d` of parameters.
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      (L ⁻¹' latticeFace ρ G) = Set.Icc 0 (fun _ => ρ) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).1
        rw [hcoord₁] at this
        simp only [Pi.zero_apply]
        linarith
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).2
        rw [hcoord₁] at this
        linarith
    · rintro ⟨h0, h1⟩ i
      refine ⟨?_, hcoord₂ _ i⟩
      rintro ⟨j, rfl⟩
      rw [hcoord₁]
      have h0j := h0 j
      have h1j := h1 j
      simp only [Pi.zero_apply] at h0j
      constructor <;> nlinarith
  -- `L_* Hᵈ = Hᵈ ⌞ range L`; change variables along `L`, then along `toLp`.
  calc ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P))
      = ∫ x in latticeFace ρ G, g x
          ∂((μHE[d] : Measure (EuclideanSpace ℝ (Fin d))).map L) := by
        rw [hiso.map_euclideanHausdorffMeasure, Measure.restrict_restrict_of_subset hrange]
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t)
          ∂(μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) :=
        hiso.isClosedEmbedding.setIntegral_map _
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    _ = ∫ s in (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
          (L ⁻¹' latticeFace ρ G), g (L (WithLp.toLp 2 s)) :=
        ((PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
          (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
          (fun t => g (L t)) (L ⁻¹' latticeFace ρ G)).symm
    _ = _ := by
        rw [hpre]
        simp only [hL]

/-- A continuous `g ≥ 0` that is positive at a relative-interior point `p` of the face
`latticeFace ρ F` (`ρ > 0`) has positive integral over the face: by
`br_latticeFace_setIntegral_eq_cube` the integral is `∫_{[0,ρ]^n} g(ι(s)) ds`, the point
`s₀ = (p_{α(j)} − ρ z_{α(j)})_j` lies in the open cube `(0,ρ)^n` with `ι(s₀) = p`, and
`support (g ∘ ι) ∩ (0,ρ)^n` is open and nonempty, hence of positive Lebesgue measure. -/
theorem Submission.fiw_tb_lcc_face_integral_pos : ∀ (n N : ℕ) (ρ : ℝ) (F : LatticeFaceIndex n N) (g : Eucl N → ℝ) (p : Eucl N), 0 < ρ → Continuous g → (∀ x, 0 ≤ g x) → 0 < g p → (∀ i : Fin N, (i ∈ range F.2 → ρ * (F.1 i : ℝ) < p i ∧ p i < ρ * ((F.1 i : ℝ) + 1)) ∧ (i ∉ range F.2 → p i = ρ * (F.1 i : ℝ))) → 0 < ∫ x in latticeFace ρ F, g x ∂(μHE[n] : Measure (Eucl N)) := by
  intro n N ρ F g p hρ hg hg0 hgp hp
  rw [Submission.br_latticeFace_setIntegral_eq_cube N n ρ F g]
  -- the affine parametrization of the face
  set ι : (Fin n → ℝ) → Eucl N := fun s =>
    ∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
      ∑ j, s j • EuclideanSpace.single (F.2 j) (1 : ℝ) with hι
  have hιc : Continuous ι := by
    rw [hι]
    fun_prop
  have hcoord : ∀ (s : Fin n → ℝ) (l : Fin N),
      ι s l = ρ * (F.1 l : ℝ) + ∑ j, if l = F.2 j then s j else 0 := by
    intro s l
    simp [hι, Pi.single_apply]
  set s₀ : Fin n → ℝ := fun j => p (F.2 j) - ρ * (F.1 (F.2 j) : ℝ) with hs₀
  have hιs₀ : ι s₀ = p := by
    ext l
    rw [hcoord]
    by_cases hl : l ∈ range F.2
    · obtain ⟨j, rfl⟩ := hl
      simp [hs₀, F.2.injective.eq_iff]
    · have hne : ∀ j, l ≠ F.2 j := fun j h => hl ⟨j, h.symm⟩
      simp [hne, (hp l).2 hl]
  have hs₀mem : s₀ ∈ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ) := by
    intro j _
    obtain ⟨h1, h2⟩ := (hp (F.2 j)).1 ⟨j, rfl⟩
    constructor <;> simp only [hs₀] <;> linarith
  have hh : Continuous fun s => g (ι s) := hg.comp hιc
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun s => hg0 _)
    (hh.continuousOn.integrableOn_compact isCompact_Icc)]
  have hopen : IsOpen (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
    hh.isOpen_support.inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hne : (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)).Nonempty :=
    ⟨s₀, by simp only [Function.mem_support, hιs₀]; exact hgp.ne', hs₀mem⟩
  calc (0 : ℝ≥0∞) < volume (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
        hopen.measure_pos volume hne
    _ ≤ volume (Function.support (fun s => g (ι s)) ∩ Icc (0 : Fin n → ℝ) (fun _ => ρ)) := by
        refine measure_mono (inter_subset_inter_right _ fun s hs => ⟨fun j => ?_, fun j => ?_⟩)
        · exact (hs j (mem_univ j)).1.le
        · exact (hs j (mem_univ j)).2.le

/-- Local isolating form for a lattice face: near any point `x` of the face `F₀ = ρ (z + F_α)`
and inside any open `W ∋ x` there is a test form `ω = (ψ φ) • dx^α` on `ℝ^N` with
`tsupport ω ⊆ W`, `[[F]](ω) = 0` for every other face `F ≠ F₀` and `[[F₀]](ω) > 0`. -/
theorem Submission.fiw_tb_lcc_local_isolating_form : ∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ F₀ x W hρ hx hW hxW
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the centre `c` of the face.
  set c : Eucl N := WithLp.toLp 2 (fun i => if i ∈ range α then ρ * ((z i : ℝ) + 1 / 2)
    else ρ * (z i : ℝ)) with hc
  -- Step 2: a point `p = x + t (c - x)`, `0 < t ≤ 1`, of `W`.
  have hcont : Continuous fun t : ℝ => x + t • (c - x) := by fun_prop
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x + t • (c - x)) ⁻¹' W := by simpa using hxW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW.preimage hcont) 0 h0
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set p : Eucl N := x + t • (c - x) with hp
  have hpW : p ∈ W :=
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε)
  have hpcoord : ∀ i, p i = x i + t * (c i - x i) := fun i => by simp [hp]
  -- Step 3: `p` lies in the shrunken face `K_{t/2}`, hence in the open face.
  have hpK : ∀ i : Fin N, (i ∈ range α → ρ * ((z i : ℝ) + t / 2) ≤ p i ∧
      p i ≤ ρ * ((z i : ℝ) + 1 - t / 2)) ∧ (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    constructor
    · intro hi
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      have hci : c i = ρ * ((z i : ℝ) + 1 / 2) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci]
      constructor <;> nlinarith
    · intro hi
      have hci : c i = ρ * (z i : ℝ) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci, (hx i).2 hi]
      ring
  have hpopen : ∀ i : Fin N, (i ∈ range α → ρ * (z i : ℝ) < p i ∧ p i < ρ * ((z i : ℝ) + 1)) ∧
      (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    refine ⟨fun hi => ?_, (hpK i).2⟩
    obtain ⟨h1, h2⟩ := (hpK i).1 hi
    constructor <;> nlinarith
  -- Step 4: a bump `ψ` at `p` supported in `W`, the cut-off `φ` of the face, `dx^α`.
  obtain ⟨ψ, hψW, hψc, hψs, hψr, hψp⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hW.mem_nhds hpW)
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ (t / 2) z α hρ (half_pos ht0)
  obtain ⟨hηα, hηne, -⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  -- Step 5: the test form `ω = (ψ φ) • dx^α`.
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y * φ y) := hψs.mul hφs
  have hgc : HasCompactSupport (fun y => ψ y * φ y) := hψc.mul_right
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ y, (ω : DifferentialForm (Eucl N) n) y = (ψ y * φ y) • η :=
    ⟨⟨fun y => (ψ y * φ y) • η, ⟨hgs.smul contDiff_const, hgc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ y (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) y v = ψ y * φ y * η v :=
    fun y v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ?_, ?_, ?_⟩
  -- Step 6: `tsupport ω ⊆ tsupport ψ ⊆ W`.
  · have hω : (ω : DifferentialForm (Eucl N) n) = fun y => (ψ y * φ y) • η := funext hωx
    rw [hω]
    exact (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hψW)
  -- Step 7: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hωv, hφ0 z' hz y (by rwa [hα] at hy), mul_zero, zero_mul]
    · simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Step 8: `[[F₀]](ω) = ∫_{F₀} ψ φ dHⁿ > 0`.
  · have hval : latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N)
          (ω : DifferentialForm (Eucl N) n) =
        ∫ y in latticeFace ρ ((z, α) : LatticeFaceIndex n N), ψ y * φ y
          ∂(μHE[n] : Measure (Eucl N)) := by
      simp only [latticeFaceAction, hωv, hηα, mul_one]
    rw [hval]
    refine Submission.fiw_tb_lcc_face_integral_pos n N ρ (z, α) (fun y => ψ y * φ y) p hρ
      hgs.continuous (fun y => mul_nonneg (hψr ⟨y, rfl⟩).1 (hφ01 y).1) ?_ hpopen
    rw [hψp, hφ1 p hpK, one_mul]
    exact one_pos

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
