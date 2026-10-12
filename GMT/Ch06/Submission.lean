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

/-- Unit simple `n`-vectors orienting the same `n`-plane agree up to sign (the orientations
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of Simon Ch. 6, 3.1), given the simple `n`-vector algebra
`‖v₁ ∧ ⋯ ∧ vₙ‖² = det(⟨vᵢ, vⱼ⟩)` and `(∑ⱼ B₁ⱼ τⱼ) ∧ ⋯ ∧ (∑ⱼ Bₙⱼ τⱼ) = det B · τ₁ ∧ ⋯ ∧ τₙ`.
An orthonormal `σ` has Gram matrix `1`, so `‖σ₁ ∧ ⋯ ∧ σₙ‖ = 1`.  If `σ, σ'` span the same
plane, then `σ'ᵢ = ∑ⱼ Bᵢⱼ σⱼ`, so `σ'₁ ∧ ⋯ ∧ σ'ₙ = det B · σ₁ ∧ ⋯ ∧ σₙ`, and taking norms
gives `|det B| = 1`. -/
theorem Submission.lpf_pi_simple_unit_facts :
    ((∀ (P n : ℕ) (v : Fin n → Eucl P),
        ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧
      ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
        simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) →
    (∀ (Q n : ℕ) (σ : Fin n → Eucl Q), Orthonormal ℝ σ → ‖simpleNVector σ‖ = 1) ∧
      ∀ (Q n : ℕ) (σ σ' : Fin n → Eucl Q), Orthonormal ℝ σ → Orthonormal ℝ σ' →
        Submodule.span ℝ (range σ) = Submodule.span ℝ (range σ') →
          simpleNVector σ' = simpleNVector σ ∨ simpleNVector σ' = -simpleNVector σ := by
  rintro ⟨hgram, hdet⟩
  -- An orthonormal family has Gram matrix `1`, so `‖σ₁ ∧ ⋯ ∧ σₙ‖² = det 1 = 1`.
  have hunit : ∀ (Q n : ℕ) (σ : Fin n → Eucl Q), Orthonormal ℝ σ → ‖simpleNVector σ‖ = 1 := by
    intro Q n σ hσ
    have hG : (Matrix.of fun i j => inner ℝ (σ i) (σ j)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hσ i j]
    have h := hgram Q n σ
    rw [hG, Matrix.det_one] at h
    exact (pow_eq_one_iff_of_nonneg (ContinuousLinearMap.opNorm_nonneg _) two_ne_zero).mp h
  refine ⟨hunit, fun Q n σ σ' hσ hσ' hspan => ?_⟩
  -- `‖c • w‖ = |c| ‖w‖` for `n`-vectors, from `opNorm_smul_le` for `c` and `c⁻¹`
  -- (instance search does not find `NormSMulClass ℝ (NVector _ n)`, so no `norm_smul`).
  have hnorm_smul : ∀ (c : ℝ) (w : NVector (Eucl Q) n), ‖c • w‖ = |c| * ‖w‖ := by
    intro c w
    apply le_antisymm
    · simpa [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c w
    · rcases eq_or_ne c 0 with rfl | hc
      · rw [abs_zero, zero_mul]
        exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • w)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv, Real.norm_eq_abs] at h
        exact (le_inv_mul_iff₀ (abs_pos.mpr hc)).mp h
  -- Expand `σ'ᵢ = ∑ⱼ Bᵢⱼ σⱼ` in the common span: `σ'₁ ∧ ⋯ ∧ σ'ₙ = det B · σ₁ ∧ ⋯ ∧ σₙ`.
  have hmem : ∀ i, σ' i ∈ Submodule.span ℝ (range σ) := fun i => by
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose B hB using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem i)
  have hexp : (fun i => ∑ j, B i j • σ j) = σ' := funext hB
  have key : simpleNVector σ' = Matrix.det B • simpleNVector σ := by
    rw [← hexp]
    exact hdet Q n B σ
  -- Taking norms, `|det B| = 1`, so `det B = ±1`.
  have habs : |Matrix.det B| = 1 :=
    calc |Matrix.det B| = |Matrix.det B| * ‖simpleNVector σ‖ := by rw [hunit Q n σ hσ, mul_one]
      _ = ‖simpleNVector σ'‖ := by rw [key, hnorm_smul]
      _ = 1 := hunit Q n σ' hσ'
  rcases (abs_eq zero_le_one).mp habs with h | h
  · left
    rw [key, h, one_smul]
  · right
    rw [key, h]
    exact neg_one_smul ℝ (simpleNVector σ)
/-- Images of open sets under `C¹` maps `ℝⁿ → ℝ^Q` are countably `n`-rectifiable.  `O` is a
countable union of compact sets `C j ⊆ O`; `G` is locally Lipschitz on `O`, hence Lipschitz on
each `C j`, and extends to a Lipschitz `g j : ℝⁿ → ℝ^Q`; then `G '' O ⊆ ⋃ j, range (g j)`. -/
theorem Submission.lpf_pi_chart_image_rectifiable :
    ∀ (Q n : ℕ) (G : Eucl n → Eucl Q) (O : Set (Eucl n)), IsOpen O → ContDiffOn ℝ 1 G O →
      CountablyRectifiable n (G '' O) := by
  intro Q n G O hO hG
  -- The subspace `O` is locally compact and second countable, hence σ-compact.
  have : LocallyCompactSpace O := hO.locallyCompactSpace
  obtain ⟨K, hKc, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := O)
  set C : ℕ → Set (Eucl n) := fun j => ((↑) : O → Eucl n) '' K j
  have hCc : ∀ j, IsCompact (C j) := fun j => (hKc j).image continuous_subtype_val
  have hCO : ∀ j, C j ⊆ O := by
    rintro j _ ⟨y, -, rfl⟩
    exact y.2
  -- `G` is `C¹`, hence Lipschitz, near each point of `O`; so it is Lipschitz on each `C j`.
  have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzOnWith L G (C j) := by
    intro j
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hCc j)
    intro x hx
    obtain ⟨L, t, ht, hGt⟩ := (hG.contDiffAt (hO.mem_nhds (hCO j hx))).exists_lipschitzOnWith
    exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hGt⟩
  choose L hL using hLip
  -- Lipschitz extensions `g j : ℝⁿ → ℝ^Q` of `G|C j` (finite-dimensional target).
  choose g hgLip hgEq using fun j => (hL j).extend_finite_dimension
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun j => range (g j))
    fun j => Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hgLip j)).mono ?_
  rintro y ⟨x, hxO, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hKcover.symm ▸ mem_univ (⟨x, hxO⟩ : O))
  exact mem_iUnion.mpr ⟨j, x, (hgEq j ⟨⟨x, hxO⟩, hj, rfl⟩).symm⟩

/-- Integer multiplicity from an integer chart-oriented density (parent Steps 7, 8, 10, 11).
Let `S(ω) = ∫_Y ⟨ω, Ψ⟩ dHⁿ`, where for `Hⁿ`-a.e. `y ∈ Y`, `Ψ(y) = ∑ᵢ aᵢ σᵢ₁ ∧ ⋯ ∧ σᵢₙ` with
`aᵢ ∈ ℤ` and `σᵢ` an orthonormal frame of `DG_{kᵢ}(wᵢ)(ℝⁿ)`, `G_{kᵢ}(wᵢ) = y`.  By (WTC) for
`(Y, 1)` all these planes are the approximate tangent plane of `Y` at `y`, so sign rigidity gives
`Ψ(y) = c(y) σ₁ ∧ ⋯ ∧ σₙ` with `c(y) ∈ ℤ` and `‖Ψ(y)‖ = |c(y)|`.  Off a null set, `S = τ(M′, θ′, ξ′)`
with `M′ = {Ψ ≠ 0}`, `θ′ = ‖Ψ‖` and `ξ′ = Ψ/‖Ψ‖`; (WTC) for `(M′, θ′)` orients `ξ′`. -/
theorem Submission.lpf_pi_im_of_chart_density : (∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen V → M ⊆ V → NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict (M ∩ Φ '' Ω)), ∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt n M θ y (LinearMap.range (fderiv ℝ Φ w).toLinearMap)) → ((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → ∀ (Q n : ℕ) (V Y : Set (Eucl Q)) (Ψ : Eucl Q → NVector (Eucl Q) n) (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)) (S : GeometricCurrentOn V n), IsOpen V → (∀ k, IsOpen (O k)) → (∀ k, ContDiff ℝ 1 (G k)) → (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) → Y ⊆ V → NullMeasurableSet Y (μHE[n] : Measure (Eucl Q)) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → (μHE[n] : Measure (Eucl Q)) (Y ∩ K) < ∞) → AEStronglyMeasurable Ψ ((μHE[n] : Measure (Eucl Q)).restrict Y) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) (μHE[n] : Measure (Eucl Q))) → (∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ) (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q), (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧ Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧ Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)) → (∀ ω : TestFormOn V n, S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂(μHE[n] : Measure (Eucl Q))) → IsIntegerMultiplicity S := by
  intro hWTC hSNA Q n V Y Ψ G O S hV hO hG hanti hYV hY hYfin hΨm hΨint hfam hS
  obtain ⟨hunit, hsign⟩ := Submission.lpf_pi_simple_unit_facts hSNA
  set μ : Measure (Eucl Q) := (μHE[n] : Measure (Eucl Q)) with hμdef
  -- Step 1: tangent planes of (Y, 1) on each chart
  let TY : ℕ → Eucl Q → Prop := fun k y => ∀ w ∈ O k, G k w = y →
      HasWeightedApproximateTangentSpaceAt n Y (fun _ => (1:ℝ)) y
        (LinearMap.range (fderiv ℝ (G k) w).toLinearMap)
  have hWY : ∀ k, ∀ᵐ y ∂(μ.restrict (Y ∩ G k '' O k)), TY k y := by
    intro k
    exact hWTC Q n V Y (fun _ => (1:ℝ)) (G k) (O k) hV hYV hY (fun _ _ => one_pos)
      (fun K hK hKV => integrableOn_const (hYfin K hK hKV).ne) (hO k) (hG k) (hanti k)
  let Ek : ℕ → Set (Eucl Q) := fun k => {y | ¬ TY k y} ∩ (Y ∩ G k '' O k)
  have hEk : ∀ k, μ (Ek k) = 0 := by
    intro k
    have h1 : μ.restrict (Y ∩ G k '' O k) {y | ¬ TY k y} = 0 := ae_iff.mp (hWY k)
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans h1.le) bot_le
  let Fam : Eucl Q → Prop := fun y => ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ)
      (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q),
      (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧
        Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧
      Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)
  let E0 : Set (Eucl Q) := {y | ¬ Fam y} ∩ Y
  have hE0 : μ E0 = 0 := by
    have h1 : μ.restrict Y {y | ¬ Fam y} = 0 := ae_iff.mp hfam
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans h1.le) bot_le
  let E : Set (Eucl Q) := E0 ∪ ⋃ k, Ek k
  have hE : μ E = 0 := measure_union_null hE0 (measure_iUnion_null hEk)
  -- Step 2: common plane and integer coefficient
  have key : ∀ y ∈ Y, y ∉ E → Ψ y ≠ 0 → ∃ (c : ℤ) (k₀ : ℕ) (w₀ : Eucl n) (σ₀ : Fin n → Eucl Q),
      w₀ ∈ O k₀ ∧ G k₀ w₀ = y ∧ Orthonormal ℝ σ₀ ∧
      Submodule.span ℝ (range σ₀) = LinearMap.range (fderiv ℝ (G k₀) w₀).toLinearMap ∧
      Ψ y = (c : ℝ) • simpleNVector σ₀ := by
    intro y hyY hyE hΨ0
    have hFam : Fam y := by
      by_contra hc
      exact hyE (Or.inl ⟨hc, hyY⟩)
    obtain ⟨m, a, k, w, σ, hi, hΨy⟩ := hFam
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact (hΨ0 (by simpa using hΨy)).elim
    · let i₀ : Fin m := ⟨0, hm⟩
      have htan : ∀ i, HasWeightedApproximateTangentSpaceAt n Y (fun _ => (1:ℝ)) y
          (LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) := by
        intro i
        have hyEk : y ∉ Ek (k i) := fun h => hyE (Or.inr (mem_iUnion.mpr ⟨k i, h⟩))
        have hmem : y ∈ Y ∩ G (k i) '' O (k i) := ⟨hyY, w i, (hi i).1, (hi i).2.1⟩
        have hT : TY (k i) y := by
          by_contra hc
          exact hyEk ⟨hc, hmem⟩
        exact hT (w i) (hi i).1 (hi i).2.1
      have hspan : ∀ i, Submodule.span ℝ (range (σ i₀)) = Submodule.span ℝ (range (σ i)) := by
        intro i
        rw [(hi i₀).2.2.2, (hi i).2.2.2]
        exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
          (by simp) (htan i₀) (htan i)
      have hε : ∀ i, ∃ e : ℤ, simpleNVector (σ i) = (e : ℝ) • simpleNVector (σ i₀) := by
        intro i
        rcases hsign Q n (σ i₀) (σ i) (hi i₀).2.2.1 (hi i).2.2.1 (hspan i) with h | h
        · exact ⟨1, by rw [h, Int.cast_one, one_smul]⟩
        · exact ⟨-1, by rw [h, Int.cast_neg, Int.cast_one]; exact (neg_one_smul ℝ (simpleNVector (σ i₀))).symm⟩
      choose e he using hε
      refine ⟨∑ i, a i * e i, k i₀, w i₀, σ i₀, (hi i₀).1, (hi i₀).2.1, (hi i₀).2.2.1,
        (hi i₀).2.2.2, ?_⟩
      rw [hΨy, Int.cast_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [he i, smul_smul, Int.cast_mul]
  -- Step 3: the new triple
  let M' : Set (Eucl Q) := (Y ∩ {y | ‖Ψ y‖ ≠ 0}) \ E
  let θ' : Eucl Q → ℝ := fun y => ‖Ψ y‖
  let ξ' : Eucl Q → NVector (Eucl Q) n := fun y => ‖Ψ y‖⁻¹ • Ψ y
  have hM'Y : M' ⊆ Y := fun y hy => hy.1.1
  have hM'mem : ∀ y ∈ M', y ∈ Y ∧ y ∉ E ∧ Ψ y ≠ 0 :=
    fun y hy => ⟨hy.1.1, hy.2, fun h0 => (show ‖Ψ y‖ ≠ 0 from hy.1.2) (by rw [h0]; exact ContinuousLinearMap.opNorm_zero)⟩
  have hdata : ∀ y ∈ M', ∃ (c : ℤ) (k₀ : ℕ) (w₀ : Eucl n) (σ₀ : Fin n → Eucl Q),
      w₀ ∈ O k₀ ∧ G k₀ w₀ = y ∧ Orthonormal ℝ σ₀ ∧
      Submodule.span ℝ (range σ₀) = LinearMap.range (fderiv ℝ (G k₀) w₀).toLinearMap ∧
      θ' y = (c.natAbs : ℝ) ∧ (ξ' y = simpleNVector σ₀ ∨ ξ' y = -simpleNVector σ₀) := by
    intro y hy
    obtain ⟨hyY, hyE, hΨ0⟩ := hM'mem y hy
    obtain ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, hσ₀, hspan₀, hΨc⟩ := key y hyY hyE hΨ0
    have hnorm : ‖Ψ y‖ = |(c : ℝ)| := by
      have : NormSMulClass ℝ (NVector (Eucl Q) n) :=
        @NormedSpace.toNormSMulClass ℝ (NVector (Eucl Q) n) _ _ _
      rw [hΨc, norm_smul, hunit Q n σ₀ hσ₀, mul_one, Real.norm_eq_abs]
    have hc0 : (c : ℝ) ≠ 0 := by
      intro h; apply hΨ0; rw [hΨc, h, zero_smul]
    refine ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, hσ₀, hspan₀, ?_, ?_⟩
    · show ‖Ψ y‖ = _
      rw [hnorm, Nat.cast_natAbs, Int.cast_abs]
    · show ‖Ψ y‖⁻¹ • Ψ y = _ ∨ ‖Ψ y‖⁻¹ • Ψ y = _
      rw [hnorm, hΨc, smul_smul]
      rcases lt_or_gt_of_ne hc0 with hneg | hpos
      · right
        rw [abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hc0]; exact neg_one_smul ℝ (simpleNVector σ₀)
      · left
        rw [abs_of_pos hpos, inv_mul_cancel₀ hc0, one_smul]
  -- nullMeasurableSet
  have hnormΨ : AEStronglyMeasurable (fun y => ‖Ψ y‖) (μ.restrict Y) :=
    (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΨm
  have hM'nm : NullMeasurableSet M' μ := by
    have hg := hnormΨ.aemeasurable
    have hgm : Measurable (hg.mk _) := hg.measurable_mk
    have hae : ∀ᵐ y ∂μ, y ∈ Y → ‖Ψ y‖ = hg.mk _ y := (ae_restrict_iff'₀ hY).mp hg.ae_eq_mk
    have h1 : NullMeasurableSet (Y ∩ (hg.mk _) ⁻¹' {0}ᶜ) μ :=
      hY.inter (hgm (measurableSet_singleton 0).compl).nullMeasurableSet
    have h2 : NullMeasurableSet (Y ∩ {y | ‖Ψ y‖ ≠ 0}) μ := by
      refine h1.congr ?_
      filter_upwards [hae] with y hy
      change (y ∈ Y ∧ hg.mk _ y ≠ 0) = (y ∈ Y ∧ ‖Ψ y‖ ≠ 0)
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hy h1]⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← hy h1]⟩
    exact h2.diff (NullMeasurableSet.of_null hE)
  -- countablyRectifiable
  have hM'cov : M' ⊆ ⋃ k, G k '' O k := by
    intro y hy
    obtain ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, -⟩ := hdata y hy
    exact mem_iUnion.mpr ⟨k₀, w₀, hw₀, hGw₀⟩
  have hCR : CountablyRectifiable n M' :=
    (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ (fun k =>
      Submission.lpf_pi_chart_image_rectifiable Q n (G k) (O k) (hO k) (hG k).contDiffOn)).mono hM'cov
  have hθ'pos : ∀ y ∈ M', 0 < θ' y := fun y hy => show 0 < ‖Ψ y‖ from
    lt_of_le_of_ne (norm_nonneg (Ψ y)) (Ne.symm (show ‖Ψ y‖ ≠ 0 from hy.1.2))
  have hθ'int : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn θ' (M' ∩ K) μ :=
    fun K hK hKV => (hΨint K hK hKV).mono_set (inter_subset_inter_left _ hM'Y)
  have hξ' : AEStronglyMeasurable ξ' (μ.restrict M') :=
    ((hnormΨ.aemeasurable.inv.aestronglyMeasurable).smul hΨm).mono_measure
      (Measure.restrict_mono hM'Y le_rfl)
  -- orients
  let TM : ℕ → Eucl Q → Prop := fun k y => ∀ w ∈ O k, G k w = y →
      HasWeightedApproximateTangentSpaceAt n M' θ' y (LinearMap.range (fderiv ℝ (G k) w).toLinearMap)
  have hWM : ∀ k, ∀ᵐ y ∂(μ.restrict (M' ∩ G k '' O k)), TM k y := fun k =>
    hWTC Q n V M' θ' (G k) (O k) hV (hM'Y.trans hYV) hM'nm hθ'pos hθ'int (hO k) (hG k) (hanti k)
  let E'k : ℕ → Set (Eucl Q) := fun k => {y | ¬ TM k y} ∩ (M' ∩ G k '' O k)
  have hE'k : ∀ k, μ (E'k k) = 0 := by
    intro k
    have h1 : μ.restrict (M' ∩ G k '' O k) {y | ¬ TM k y} = 0 := ae_iff.mp (hWM k)
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans h1.le) bot_le
  have hE' : μ (⋃ k, E'k k) = 0 := measure_iUnion_null hE'k
  have horients : ∀ᵐ y ∂(μ.restrict M'), ∃ τ : Fin n → Eucl Q, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M' θ' y (Submodule.span ℝ (range τ)) ∧
      (ξ' y = simpleNVector τ ∨ ξ' y = -simpleNVector τ) := by
    have h1 : ∀ᵐ y ∂(μ.restrict M'), y ∉ ⋃ k, E'k k :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hE')
    filter_upwards [h1, ae_restrict_mem₀ hM'nm] with y hyE' hyM'
    obtain ⟨c, k₀, w₀, σ₀, hw₀, hGw₀, hσ₀, hspan₀, -, hξ⟩ := hdata y hyM'
    refine ⟨σ₀, hσ₀, ?_, hξ⟩
    have hT : TM k₀ y := by
      by_contra hc
      exact hyE' (mem_iUnion.mpr ⟨k₀, hc, hyM', w₀, hw₀, hGw₀⟩)
    rw [hspan₀]
    exact hT w₀ hw₀ hGw₀
  -- representation
  have hrep : ∀ ω : TestFormOn V n, S ω = tauAction n M' θ' ξ' ω := by
    intro ω
    rw [hS ω]
    unfold tauAction
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hY hM'Y ?_]
    · refine setIntegral_congr_fun₀ hM'nm ?_
      intro y hy
      have hne : ‖Ψ y‖ ≠ 0 := hy.1.2
      show Ψ y _ = ‖Ψ y‖ * ((‖Ψ y‖⁻¹ • Ψ y) _)
      rw [_root_.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hE] with y hyE hy
      have h0 : ‖Ψ y‖ = 0 := by
        by_contra hc
        exact hy.2 ⟨⟨hy.1, hc⟩, hyE⟩
      have hΨ0 : Ψ y = 0 := (norm_eq_zero (E := NVector (Eucl Q) n) (a := Ψ y)).mp h0
      rw [hΨ0]
      rfl
  refine ⟨M', θ', ξ', ⟨hM'Y.trans hYV, hM'nm, hCR, hθ'pos, hθ'int, hξ', horients⟩, ?_, hrep⟩
  intro y hy
  obtain ⟨c, -, -, -, -, -, -, -, hθc, -⟩ := hdata y hy
  exact ⟨c.natAbs, hθc⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
