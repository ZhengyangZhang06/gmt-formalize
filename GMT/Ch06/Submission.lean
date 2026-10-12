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

set_option maxHeartbeats 400000 in
set_option maxSynthPendingDepth 3 in
/-- **Simon Ch. 6, Remark 8.3(1) (p. 176).**  Assuming the slicing theorem, Theorem 8.2 on an
open `U ⊆ ℝ^P` follows from its case for currents in `ℝ^P` supported in a fixed compact set.
Near each `ξ₀ ∈ U`: slice the `T_j` by `|x - ξ₀|`; choose (Fatou, Helly) a radius `r` with
integer multiplicity slices of bounded mass along a subsequence on which
`T_j ⌞ B_r(ξ₀) ⇀ T ⌞ B_r(ξ₀)`; extend these integral currents to `ℝ^P` by a cutoff, apply the
compact case and restrict back to `U`.  Then `T = T ⌞ B_r(ξ₀)` near `ξ₀`, and the local
representations patch together (`iwl_im_patching`).  All auxiliary facts are local steps. -/
theorem Submission.iwl_localization : ∀ (P m : ℕ), SlicingTheorem → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, ((Tj j).mass + (Tj j).boundary.mass)) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → (∀ (U : Set (Eucl P)), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) := by
  /- (P0) Multiplying a test form on `U` by a smooth function gives a test form on `U`. -/
  have smul_mem : ∀ {P k : ℕ} {U : Set (Eucl P)} (φ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (ζ : TestFormOn U k),
      (fun x => φ x • (ζ : DifferentialForm (Eucl P) k) x) ∈ TestFormOn U k := by
    intro P k U φ hφ ζ
    have hζ : IsTestForm (ζ : DifferentialForm (Eucl P) k) ∧
        tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ U := ζ.property
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hφ.smul hζ.1.1
    · refine hζ.1.2.mono ?_
      intro x hx
      by_contra h
      apply hx
      simp only
      rw [Function.notMem_support.1 h, smul_zero]
    · exact (tsupport_smul_subset_right _ _).trans hζ.2
  /- (F2) Locality: a current only sees a test form near its support. -/
  have locality : ∀ (P k : ℕ) (U N : Set (Eucl P)) (Y : GeometricCurrentOn U k)
      (η η' : TestFormOn U k), IsOpen N → Y.support ⊆ N →
      (∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = (η' : DifferentialForm (Eucl P) k) x) →
      Y η = Y η' := by
    intro P k U N Y η η' hN hsupp hagree
    suffices h : Y (η - η') = 0 by
      have hsub : Y (η - η') = Y η - Y η' := map_sub Y.toCurrent η η'
      linarith
    set ζ : TestFormOn U k := η - η' with hζdef
    have hζN : ∀ x ∈ N, (ζ : DifferentialForm (Eucl P) k) x = 0 := by
      intro x hx
      simp [hζdef, hagree x hx]
    have hζsupp : tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ Y.zeroRegion := by
      intro x hx
      have hxU : x ∈ U := ζ.property.2 hx
      have hxN : x ∉ N := by
        intro hxN
        have : (ζ : DifferentialForm (Eucl P) k) =ᶠ[𝓝 x] 0 :=
          Filter.eventually_of_mem (hN.mem_nhds hxN) fun y hy => hζN y hy
        exact (notMem_tsupport_iff_eventuallyEq.2 this) hx
      by_contra hxZ
      exact hxN (hsupp ⟨hxU, hxZ⟩)
    have hK : IsCompact (tsupport (ζ : DifferentialForm (Eucl P) k)) := ζ.property.1.2
    set 𝒲 : Set (Set (Eucl P)) := {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧
      Y.VanishesOn W} with h𝒲
    have hcov : tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ ⋃ W : 𝒲, (W : Set (Eucl P)) := by
      intro x hx
      obtain ⟨W, hW, hxW⟩ := mem_sUnion.1 (hζsupp hx)
      exact mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun W : 𝒲 => (W : Set (Eucl P)))
      (fun W => W.2.1) hcov
    have hcov' : tsupport (ζ : DifferentialForm (Eucl P) k) ⊆
        ⋃ i : t, ((i : 𝒲) : Set (Eucl P)) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
    obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
      (I := modelWithCornersSelf ℝ (Eucl P))
      (isClosed_tsupport _) (fun i : t => ((i : 𝒲) : Set (Eucl P))) (fun i => (i : 𝒲).2.1) hcov'
    have hpiece : ∀ i : t, (fun x => (f i : Eucl P → ℝ) x • (ζ : DifferentialForm (Eucl P) k) x) ∈
        TestFormOn U k := fun i => smul_mem _ (f i).contMDiff.contDiff ζ
    have hsum : ζ = ∑ i : t, (⟨_, hpiece i⟩ : TestFormOn U k) := by
      apply Subtype.ext
      funext x
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only
      by_cases hx : x ∈ tsupport (ζ : DifferentialForm (Eucl P) k)
      · rw [← Finset.sum_smul]
        have h1 := f.sum_eq_one hx
        rw [finsum_eq_sum_of_fintype] at h1
        rw [h1, one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    rw [hsum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact (i : 𝒲).2.2.2.2 _ ((tsupport_smul_subset_left _ _).trans (hf i))
  /- (F4, second half) `spt ∂Z ⊆ spt Z`. -/
  have boundary_support : ∀ (P k : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (k + 1)),
      Z.boundary.support ⊆ Z.support := by
    intro P k U Z x hx
    refine ⟨hx.1, fun hxZ => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxZ
    exact ⟨W, ⟨hWo, hWc, hWU, fun ω hω => by
      rw [GeometricCurrentOn.boundary_apply]
      exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hω)⟩, hxW⟩
  have h_iwl_loc_support_locality : (∀ (P k : ℕ) (U N : Set (Eucl P))
      (Y : GeometricCurrentOn U k) (η η' : TestFormOn U k), IsOpen N → Y.support ⊆ N →
      (∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = (η' : DifferentialForm (Eucl P) k) x) →
      Y η = Y η') ∧ (∀ (P k : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (k + 1)),
      Z.boundary.support ⊆ Z.support) :=
    ⟨locality, boundary_support⟩
  /- Steps 4–5: Fatou and the choice of a good radius. -/
  have h_iwl_loc_good_radius : ∀ (a b : ℝ), a < b → ∀ (g : ℕ → ℝ → ℝ≥0∞) (Λ : ℝ≥0∞)
      (E : Set ℝ) (Q : ℕ → ℝ → Prop), (∀ j, Measurable (g j)) →
      (∀ j, ∫⁻ t in Ioo a b, g j t ≤ Λ) → Λ < ∞ → E.Countable →
      (∀ j, ∀ᵐ t ∂(volume : Measure ℝ), Q j t) → ∃ r ∈ Ioo a b, r ∉ E ∧ (∀ j, Q j r) ∧
      ∃ (C : ℝ≥0∞) (σ : ℕ → ℕ), C < ∞ ∧ StrictMono σ ∧ ∀ j, g (σ j) r ≤ C := by
    intro a b hab g Λ E Q hgm hgint hΛ hE hQ
    set h : ℝ → ℝ≥0∞ := fun t => liminf (fun j => g j t) atTop with hh
    have hhm : Measurable h := Measurable.liminf hgm
    have hfatou : ∫⁻ t in Ioo a b, h t ≤ Λ := by
      calc ∫⁻ t in Ioo a b, h t ≤ liminf (fun j => ∫⁻ t in Ioo a b, g j t) atTop :=
            lintegral_liminf_le hgm
        _ ≤ Λ := liminf_le_of_le (by isBoundedDefault) fun c hc => by
            obtain ⟨j, hj⟩ := hc.exists
            exact hj.trans (hgint j)
    have hfin : ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t < ∞ :=
      ae_lt_top hhm (ne_of_lt (lt_of_le_of_lt hfatou hΛ))
    have hEnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ E := hE.ae_notMem _
    have hQall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j, Q j t := ae_all_iff.2 hQ
    have hall : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
        t ∈ Ioo a b ∧ t ∉ E ∧ (∀ j, Q j t) ∧ h t < ∞ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hEnull,
        ae_restrict_of_ae hQall, hfin] with t h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    have hne : (volume.restrict (Ioo a b)) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo]
      simpa using hab
    have : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.2 hne
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hall.exists
    refine ⟨r, hr1, hr2, hr3, h r + 1, ?_⟩
    have hlt : liminf (fun j => g j r) atTop < h r + 1 :=
      ENNReal.lt_add_right hr4.ne one_ne_zero
    have hfreq : ∃ᶠ j in atTop, g j r < h r + 1 :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    obtain ⟨σ, hσ, hσP⟩ := extraction_of_frequently_atTop hfreq
    exact ⟨σ, ENNReal.add_lt_top.2 ⟨hr4, ENNReal.one_lt_top⟩, hσ, fun j => (hσP j).le⟩
  /- (F4) and Step 10: a restriction agrees with the current on forms vanishing off `A`, and
  is supported in `closure A`. -/
  have h_iwl_loc_restriction_local : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (X : GeometricCurrentOn U k) (A : Set (Eucl P)) (S : GeometricCurrentOn U k),
      IsRestriction X A S → (∀ ω : TestFormOn U k,
        (∀ x, x ∉ A → (ω : DifferentialForm (Eucl P) k) x = 0) → S ω = X ω) ∧
      S.support ⊆ closure A := by
    intro P k U hU X A S hS
    obtain ⟨hA, μ, v, hrep, hSω⟩ := hS
    constructor
    · intro ω hω
      rw [hSω ω, (hrep ω).2]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [hω x hx, map_zero]
    · intro x hx
      by_contra hxA
      obtain ⟨hxU, hxZ⟩ := hx
      have hopen : IsOpen (U ∩ (closure A)ᶜ) := hU.inter isClosed_closure.isOpen_compl
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen x ⟨hxU, hxA⟩
      apply hxZ
      refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
      · rw [closure_ball _ (by positivity)]; exact isCompact_closedBall _ _
      · rw [closure_ball _ (by positivity)]
        exact fun y hy => (hεsub (closedBall_subset_ball (by linarith) hy)).1
      · intro ω hω
        rw [hSω ω]
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro y hy
        have : y ∉ tsupport (ω : DifferentialForm (Eucl P) k) := fun hyt =>
          (hεsub (ball_subset_ball (by linarith) (hω hyt))).2 (subset_closure hy)
        rw [image_eq_zero_of_notMem_tsupport this, map_zero]
  /- Steps 7(v) and 9: weighted tangent spaces are unchanged under null changes of the
  carrier and under intersection with an open set containing the point. -/
  have blowUp_null : ∀ {P n : ℕ} (x : Eucl P) (r : ℝ) (S : Set (Eucl P)),
      (μHE[n] : Measure (Eucl P)) S = 0 →
      (μHE[n] : Measure (Eucl P)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro P n x r S hS
    have hlip : LipschitzWith ‖r⁻¹‖₊
        (Poincare.SimonGMT.Chapter03.blowUpMap x r : Eucl P → Eucl P) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dist_eq_norm, ← smul_sub,
        sub_sub_sub_cancel_right, norm_smul, coe_nnnorm]
      exact le_rfl
    rw [Measure.euclideanHausdorffMeasure_def] at hS ⊢
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hS ⊢
    have hle := hlip.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n) S
    rcases mul_eq_zero.1 hS with h | h
    · rw [h, zero_mul]
    · have : (μH[n] : Measure (Eucl P)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 :=
        nonpos_iff_eq_zero.mp (hle.trans (by rw [h, mul_zero]))
      rw [this, mul_zero]
  have h_iwl_loc_weighted_tangent_congr : (∀ (P n : ℕ) (M M' : Set (Eucl P)) (θ : Eucl P → ℝ)
      (x : Eucl P) (Q : Submodule ℝ (Eucl P)), (μHE[n] : Measure (Eucl P)) (M \ M') = 0 →
      (μHE[n] : Measure (Eucl P)) (M' \ M) = 0 →
      (HasWeightedApproximateTangentSpaceAt n M θ x Q ↔
        HasWeightedApproximateTangentSpaceAt n M' θ x Q)) ∧
      (∀ (P n : ℕ) (M V : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P)
      (Q : Submodule ℝ (Eucl P)), IsOpen V → x ∈ V →
      (HasWeightedApproximateTangentSpaceAt n (M ∩ V) θ x Q ↔
        HasWeightedApproximateTangentSpaceAt n M θ x Q)) := by
    constructor
    · intro P n M M' θ x Q h1 h2
      unfold HasWeightedApproximateTangentSpaceAt
      apply and_congr_right
      intro _
      apply forall_congr'
      intro f
      apply tendsto_congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      apply setIntegral_congr_set
      rw [ae_eq_set]
      exact ⟨measure_mono_null (subset_image_sdiff _ _ _) (blowUp_null x r _ h1),
        measure_mono_null (subset_image_sdiff _ _ _) (blowUp_null x r _ h2)⟩
    · intro P n M V θ x Q hV hxV
      unfold HasWeightedApproximateTangentSpaceAt
      apply and_congr_right
      intro _
      apply forall_congr'
      intro f
      apply tendsto_congr'
      obtain ⟨R, hR⟩ : ∃ R, tsupport (f : Eucl P → ℝ) ⊆ closedBall 0 R :=
        f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
      set R' : ℝ := max R 1 with hR'
      have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
      have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r * R' < δ := by
        have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
        have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ / R' :=
          nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
        filter_upwards [h1, h2] with r hr1 hr2
        exact ⟨hr1, by rwa [lt_div_iff₀ hR'pos] at hr2⟩
      filter_upwards [hev] with r ⟨hr, hrR⟩
      have hinj : Function.Injective
          (Poincare.SimonGMT.Chapter03.blowUpMap x r : Eucl P → Eucl P) := by
        intro y z hyz
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap] at hyz
        have := congrArg (fun w => r • w) hyz
        simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at this
        simpa using this
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ V) =
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' V ∩
            Poincare.SimonGMT.Chapter03.blowUpMap x r '' M := by
        rw [image_inter hinj, inter_comm]
      have hVimg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' V =
          (fun y => x + r • y) ⁻¹' V := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simp only [Poincare.SimonGMT.Chapter03.blowUpMap, mem_preimage, smul_smul,
            mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
          exact hz
        · intro hy
          refine ⟨x + r • y, hy, ?_⟩
          simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
      have hVmeas : MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' V) := by
        rw [hVimg]
        exact (hV.preimage (by fun_prop)).measurableSet
      rw [himg, ← Measure.restrict_restrict hVmeas]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hyt : y ∉ tsupport (f : Eucl P → ℝ) := by
        intro hyt
        apply hy
        rw [hVimg]
        apply hδV
        have hy' : ‖y‖ ≤ R' := by
          have := hR hyt
          rw [mem_closedBall, dist_zero_right] at this
          exact this.trans (le_max_left _ _)
        rw [mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        calc r * ‖y‖ ≤ r * R' := mul_le_mul_of_nonneg_left hy' hr.le
          _ < δ := hrR
      rw [image_eq_zero_of_notMem_tsupport hyt, zero_mul]
  /- Step 7(v), core: a `τ`-current vanishing on test forms supported in an open `O` has an
  `Hᵏ`-null carrier in `O`. -/
  have covector_finiteDimensional : ∀ (P k : ℕ), FiniteDimensional ℝ (Covector (Eucl P) k) := by
    intro P k
    let Φ : Covector (Eucl P) k →ₗ[ℝ] ((Fin k → Fin P) → ℝ) :=
      { toFun := fun α J => α (fun i => EuclideanSpace.single (J i) (1 : ℝ))
        map_add' := by intro α β; ext J; simp
        map_smul' := by intro c α; ext J; simp }
    refine FiniteDimensional.of_injective Φ ?_
    intro α β h
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
    intro v _
    have := congrFun h v
    simpa [Φ] using this
  have abs_apply_orthonormal_le : ∀ {P k : ℕ} {τ : Fin k → Eucl P}, Orthonormal ℝ τ →
      ∀ (α : Covector (Eucl P) k), |α τ| ≤ ‖α‖ := by
    intro P k τ hτ α
    have h1 := α.le_opNorm τ
    have h2 : ∏ j, ‖τ j‖ = 1 := Finset.prod_eq_one (fun j _ => hτ.1 j)
    rw [h2, mul_one, Real.norm_eq_abs] at h1
    exact h1
  have wedge_inner_apply_orthonormal : ∀ {P k : ℕ} {τ : Fin k → Eucl P}, Orthonormal ℝ τ →
      wedgeCovectors k (fun i => (innerSL ℝ (τ i) : Eucl P →L[ℝ] ℝ)) τ = 1 := by
    intro P k τ hτ
    rw [wedgeCovectors_apply_det]
    have hM : (Matrix.of fun i j => (innerSL ℝ (τ i) : Eucl P →L[ℝ] ℝ) (τ j)) = 1 := by
      ext i j
      rw [Matrix.of_apply, innerSL_apply_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.1 hτ i j
    rw [hM, Matrix.det_one]
  have h_iwl_loc_tau_carrier_null : ∀ (P k : ℕ) (U O M : Set (Eucl P)) (θ : Eucl P → ℝ)
      (ξ : Eucl P → NVector (Eucl P) k), IsOpen O → O ⊆ U → IsRectifiableTriple U k M θ ξ →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M θ ξ (ω : DifferentialForm (Eucl P) k) = 0) →
      (μHE[k] : Measure (Eucl P)) (M ∩ O) = 0 := by
    intro P k U O M θ ξ hO hOU hT hvan
    have : FiniteDimensional ℝ (Covector (Eucl P) k) := covector_finiteDimensional P k
    let b := Module.finBasis ℝ (Covector (Eucl P) k)
    have hbound : ∀ i, ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
        |ξ x (b i)| ≤ ‖b i‖ := by
      intro i
      filter_upwards [hT.orients] with x hx
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      have key := abs_apply_orthonormal_le hτ (b i)
      rcases hξ with h | h
      · rw [h, simpleNVector_apply]; exact key
      · rw [h, neg_apply, simpleNVector_apply, abs_neg]; exact key
    have hne : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ξ x ≠ 0 := by
      filter_upwards [hT.orients] with x hx
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      intro h0
      have h1 := wedge_inner_apply_orthonormal hτ
      set α := wedgeCovectors k (fun i => (innerSL ℝ (τ i) : Eucl P →L[ℝ] ℝ)) with hα
      rcases hξ with h | h
      · have h2 : ξ x α = simpleNVector τ α := by rw [h]
        rw [h0, simpleNVector_apply, h1] at h2
        simp at h2
      · have h2 : ξ x α = (-simpleNVector τ) α := by rw [h]
        rw [h0, neg_apply, simpleNVector_apply, h1] at h2
        simp at h2
    have hzero : ∀ i, ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
        x ∈ O → θ x * ξ x (b i) = 0 := by
      intro i
      refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (f := fun x => θ x * ξ x (b i)) ?_ ?_
      · rw [locallyIntegrableOn_iff hO.isLocallyClosed]
        intro K hKO hK
        have hθK : Integrable θ (((μHE[k] : Measure (Eucl P)).restrict M).restrict K) := by
          rw [Measure.restrict_restrict hK.measurableSet, inter_comm]
          exact hT.integrableOn K hK (hKO.trans hOU)
        have hc : Continuous (fun L : NVector (Eucl P) k => L (b i)) :=
          (ContinuousLinearMap.apply ℝ ℝ (b i)).continuous
        show Integrable _ _
        refine Integrable.mono' (hθK.norm.mul_const ‖b i‖) ?_ ?_
        · exact hθK.aestronglyMeasurable.mul
            (hc.comp_aestronglyMeasurable hT.aestronglyMeasurable.restrict)
        · filter_upwards [ae_restrict_of_ae (hbound i)] with x hx
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      · intro g hg hgc hgO
        let ω : DifferentialForm (Eucl P) k := fun x => g x • b i
        have hsupp : Function.support ω ⊆ Function.support g := by
          intro x hx
          rw [Function.mem_support] at hx ⊢
          intro hgx
          apply hx
          simp [ω, hgx]
        have hωO : tsupport ω ⊆ O := (closure_mono hsupp).trans hgO
        have hωmem : ω ∈ TestFormOn U k := by
          show (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω ∧ HasCompactSupport ω) ∧ tsupport ω ⊆ U
          exact ⟨⟨hg.smul contDiff_const, hgc.mono hsupp⟩, hωO.trans hOU⟩
        have h := hvan ⟨ω, hωmem⟩ hωO
        have heq : (fun x => g x • (θ x * ξ x (b i))) = fun x => θ x * ξ x (ω x) := by
          funext x
          simp only [ω, map_smul, smul_eq_mul]
          ring
        calc ∫ x, g x • (θ x * ξ x (b i)) ∂((μHE[k] : Measure (Eucl P)).restrict M)
            = ∫ x, θ x * ξ x (ω x) ∂((μHE[k] : Measure (Eucl P)).restrict M) := by rw [heq]
          _ = 0 := h
    have hmem : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), x ∈ M :=
      ae_restrict_mem₀ hT.nullMeasurableSet
    have hnot : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), x ∉ O := by
      have hall := ae_all_iff.2 hzero
      filter_upwards [hall, hne, hmem] with x hx hxne hxM hxO
      apply hxne
      have hθ : 0 < θ x := hT.pos x hxM
      have hvan' : ∀ i, ξ x (b i) = 0 := fun i => by
        rcases mul_eq_zero.1 (hx i hxO) with h | h
        · exact absurd h hθ.ne'
        · exact h
      have hlin : (ξ x : Covector (Eucl P) k →ₗ[ℝ] ℝ) = 0 :=
        b.ext (fun i => by simpa using hvan' i)
      ext α
      simpa using LinearMap.congr_fun hlin α
    have h0 : ((μHE[k] : Measure (Eucl P)).restrict M) O = 0 :=
      measure_eq_zero_iff_ae_notMem.2 hnot
    rw [Measure.restrict_apply hO.measurableSet] at h0
    rwa [inter_comm]
  /- Step 7: Leibniz bound (Mathlib's `ContDiff.Bounds` is outside the frozen imports). -/
  have leibniz_aux : ∀ {Du Eu Fu Gu : Type} [NormedAddCommGroup Du] [NormedSpace ℝ Du]
      [NormedAddCommGroup Eu] [NormedSpace ℝ Eu] [NormedAddCommGroup Fu] [NormedSpace ℝ Fu]
      [NormedAddCommGroup Gu] [NormedSpace ℝ Gu]
      (B : Eu →L[ℝ] Fu →L[ℝ] Gu) {f : Du → Eu} {g : Du → Fu} {n : ℕ} {s : Set Du} {x : Du},
      ContDiffOn ℝ n f s → ContDiffOn ℝ n g s → UniqueDiffOn ℝ s → x ∈ s →
      ‖iteratedFDerivWithin ℝ n (fun y => B (f y) (g y)) s x‖ ≤
        ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
          ‖iteratedFDerivWithin ℝ (n - i) g s x‖ := by
    intro Du Eu Fu Gu _ _ _ _ _ _ _ _ B f g n s x hf hg hs hx
    induction n generalizing Eu Fu Gu with
    | zero =>
      simp only [norm_iteratedFDerivWithin_zero, zero_add, Finset.range_one,
        Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
      apply B.le_opNorm₂
    | succ n IH =>
      have In : (n : WithTop ℕ∞) + 1 ≤ n.succ := by simp only [Nat.cast_succ, le_refl]
      have I1 :
          ‖iteratedFDerivWithin ℝ n
              (fun y : Du => B.precompR Du (f y) (fderivWithin ℝ g s y)) s x‖ ≤
            ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin ℝ i f s x‖ *
              ‖iteratedFDerivWithin ℝ (n + 1 - i) g s x‖ := by
        calc
          ‖iteratedFDerivWithin ℝ n
              (fun y : Du => B.precompR Du (f y) (fderivWithin ℝ g s y)) s x‖ ≤
              ‖B.precompR Du‖ * ∑ i ∈ Finset.range (n + 1),
                n.choose i * ‖iteratedFDerivWithin ℝ i f s x‖ *
                  ‖iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ g s) s x‖ :=
            IH _ (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
          _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin ℝ i f s x‖ *
                ‖iteratedFDerivWithin ℝ (n - i) (fderivWithin ℝ g s) s x‖ := by
              gcongr; exact B.norm_precompR_le Du
          _ = _ := by
            congr 1
            apply Finset.sum_congr rfl fun i hi => ?_
            rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
              ← norm_iteratedFDerivWithin_fderivWithin hs hx]
      have I2 :
          ‖iteratedFDerivWithin ℝ n
              (fun y : Du => B.precompL Du (fderivWithin ℝ f s y) (g y)) s x‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i *
            ‖iteratedFDerivWithin ℝ (i + 1) f s x‖ * ‖iteratedFDerivWithin ℝ (n - i) g s x‖ :=
        calc
          ‖iteratedFDerivWithin ℝ n
              (fun y : Du => B.precompL Du (fderivWithin ℝ f s y) (g y)) s x‖ ≤
              ‖B.precompL Du‖ * ∑ i ∈ Finset.range (n + 1),
                n.choose i * ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f s) s x‖ *
                  ‖iteratedFDerivWithin ℝ (n - i) g s x‖ :=
            IH _ (hf.fderivWithin hs In) (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
          _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f s) s x‖ *
                ‖iteratedFDerivWithin ℝ (n - i) g s x‖ := by
            gcongr; exact B.norm_precompL_le Du
          _ = _ := by
            congr 1
            apply Finset.sum_congr rfl fun i _ => ?_
            rw [← norm_iteratedFDerivWithin_fderivWithin hs hx]
      have J : iteratedFDerivWithin ℝ n
          (fun y : Du => fderivWithin ℝ (fun y : Du => B (f y) (g y)) s y) s x =
            iteratedFDerivWithin ℝ n (fun y => B.precompR Du (f y)
              (fderivWithin ℝ g s y) + B.precompL Du (fderivWithin ℝ f s y) (g y)) s x := by
        apply iteratedFDerivWithin_congr (fun y hy => ?_) hx
        exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) y hy)
          (hg.differentiableOn (by positivity) y hy) (hs y hy)
      rw [← norm_iteratedFDerivWithin_fderivWithin hs hx, J]
      have A : ContDiffOn ℝ n (fun y => B.precompR Du (f y) (fderivWithin ℝ g s y)) s :=
        (B.precompR Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
          (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
      have A' : ContDiffOn ℝ n (fun y => B.precompL Du (fderivWithin ℝ f s y) (g y)) s :=
        (B.precompL Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
          (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
      rw [fun_iteratedFDerivWithin_add_apply (A.contDiffWithinAt hx) (A'.contDiffWithinAt hx)
        hs hx]
      apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq ?_))
      simp_rw [← mul_add, mul_assoc]
      congr 1
      exact (Finset.sum_choose_succ_mul
        (fun i j => ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ j g s x‖) n).symm
  have leibniz_smul : ∀ {D F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
      [NormedAddCommGroup F] [NormedSpace ℝ F] {f : D → ℝ} {g : D → F} {n : ℕ},
      ContDiff ℝ n f → ContDiff ℝ n g → ∀ (x : D),
      ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ := by
    intro D F _ _ _ _ f g n hf hg x
    have h := leibniz_aux
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) hf.contDiffOn hg.contDiffOn
      uniqueDiffOn_univ (mem_univ x)
    simp only [iteratedFDerivWithin_univ, ContinuousLinearMap.lsmul_apply] at h
    refine h.trans ?_
    exact mul_le_of_le_one_left (by positivity) ContinuousLinearMap.opNorm_lsmul_le
  /- Step 7: a smooth cutoff `χ`, `0 ≤ χ ≤ 1`, `χ = 1` near `K`, `tsupport χ ⊆ U` compact. -/
  have exists_cutoff : ∀ {P : ℕ} {U K : Set (Eucl P)}, IsOpen U → IsCompact K → K ⊆ U →
      ∃ χ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
        ∃ N : Set (Eucl P), IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, χ x = 1 := by
    intro P U K hU hK hKU
    obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
    obtain ⟨f, hf, hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
      (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
    have htsupp : tsupport f ⊆ cthickening δ K := by
      rw [tsupport, hsupp]
      exact closure_thickening_subset_cthickening δ K
    refine ⟨f, hf, ?_, htsupp.trans hδU, fun x => hrange (mem_range_self x),
      thickening (δ / 2) K, isOpen_thickening, self_subset_thickening (half_pos hδ) K,
      fun x hx => (hone x).1 (thickening_subset_cthickening _ _ hx)⟩
    exact hK.cthickening.of_isClosed_subset (isClosed_tsupport f) htsupp
  have covectorEuclideanNorm_smul_le : ∀ {P n : ℕ} {t : ℝ}, (0 ≤ t ∧ t ≤ 1) →
      ∀ (α : Covector (Eucl P) n), covectorEuclideanNorm (t • α) ≤ covectorEuclideanNorm α := by
    intro P n t ht α
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro I _
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      have h1 : t ^ 2 ≤ 1 := by nlinarith
      have h2 : 0 ≤ (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 := sq_nonneg _
      nlinarith
    · exact le_refl _
  have cut_mem : ∀ {P j : ℕ} {U : Set (Eucl P)} (χ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ U →
      ∀ (w : TestFormOn (univ : Set (Eucl P)) j),
      (fun x => χ x • (w : DifferentialForm (Eucl P) j) x) ∈ TestFormOn U j := by
    intro P j U χ hχ hχU w
    have hw : IsTestForm (w : DifferentialForm (Eucl P) j) ∧
        tsupport (w : DifferentialForm (Eucl P) j) ⊆ univ := w.property
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hχ.smul hw.1.1
    · refine hw.1.2.mono ?_
      intro x hx
      by_contra h
      apply hx
      simp only
      rw [Function.notMem_support.1 h, smul_zero]
    · exact (tsupport_smul_subset_left _ _).trans hχU
  have eventually_norm_iteratedFDeriv_lt : ∀ {P j : ℕ}
      (ws : ℕ → TestFormOn (univ : Set (Eucl P)) j), TestFormOnConverges ws 0 → ∀ (i : ℕ)
      (δ : ℝ), 0 < δ →
      ∀ᶠ l in atTop, ∀ x, ‖iteratedFDeriv ℝ i (ws l : DifferentialForm (Eucl P) j) x‖ < δ := by
    intro P j ws h i δ hδ
    obtain ⟨K', -, -, hsupp, -, hder⟩ := h
    have hu := (Metric.tendstoUniformlyOn_iff.1 (hder i)) δ hδ
    filter_upwards [hu] with l hl x
    by_cases hx : x ∈ K'
    · have hlx := hl x hx
      have h0 : ((0 : TestFormOn (univ : Set (Eucl P)) j) : DifferentialForm (Eucl P) j) = 0 :=
        rfl
      rw [h0, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left] at hlx
      exact hlx
    · have : iteratedFDeriv ℝ i (ws l : DifferentialForm (Eucl P) j) x = 0 := by
        by_contra hne
        exact hx (hsupp l (support_iteratedFDeriv_subset i hne))
      rw [this, norm_zero]
      exact hδ
  /- Step 7 (i)–(iv) and Step 8: the zero extension `Z̃(ω) = Z(χω)` of a current on `U`
  supported in the compact `K ⊆ U`. -/
  have h_iwl_loc_zero_extension : ∀ (P k : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K →
      K ⊆ U → ∃ E : GeometricCurrentOn U (k + 1) →
        GeometricCurrentOn (univ : Set (Eucl P)) (k + 1),
      (∀ Z : GeometricCurrentOn U (k + 1), Z.support ⊆ K → ∀ ω : TestFormOn U (k + 1),
        E Z (testFormOnInclusion (subset_univ U) (k + 1) ω) = Z ω) ∧
      (∀ Z : GeometricCurrentOn U (k + 1), Z.support ⊆ K → ∀ ω : TestFormOn U k,
        (E Z).boundary (testFormOnInclusion (subset_univ U) k ω) = Z.boundary ω) ∧
      (∀ Z : GeometricCurrentOn U (k + 1), Z.support ⊆ K → (E Z).support ⊆ K) ∧
      (∀ Z : GeometricCurrentOn U (k + 1), (E Z).mass ≤ Z.mass) ∧
      (∀ Z : GeometricCurrentOn U (k + 1), Z.support ⊆ K →
        (E Z).boundary.mass ≤ Z.boundary.mass) ∧
      (∀ (Zj : ℕ → GeometricCurrentOn U (k + 1)) (Z : GeometricCurrentOn U (k + 1)),
        WeaklyConvergesOn Zj Z → WeaklyConvergesOn (fun j => E (Zj j)) (E Z)) := by
    intro P k U K hU hK hKU
    obtain ⟨χ, hχ, hχc, hχU, hχ01, N, hN, hKN, hχN⟩ := exists_cutoff hU hK hKU
    -- multiplication by the cutoff, `𝒟ʲ(ℝ^P) → 𝒟ʲ(U)`
    obtain ⟨cutMul, hcoe⟩ : ∃ cutMul : ∀ j : ℕ,
        TestFormOn (univ : Set (Eucl P)) j →ₗ[ℝ] TestFormOn U j,
        ∀ (j : ℕ) (w : TestFormOn (univ : Set (Eucl P)) j),
          ((cutMul j w : TestFormOn U j) : DifferentialForm (Eucl P) j) =
            fun x => χ x • (w : DifferentialForm (Eucl P) j) x :=
      ⟨fun j =>
        { toFun := fun w => ⟨fun x => χ x • (w : DifferentialForm (Eucl P) j) x,
            cut_mem χ hχ hχU w⟩
          map_add' := fun w η => by
            apply Subtype.ext
            funext x
            simp [smul_add]
          map_smul' := fun c w => by
            apply Subtype.ext
            funext x
            simp [smul_smul, mul_comm] }, fun _ _ => rfl⟩
    -- sequential continuity of `cutMul`
    have hle : ∀ i : ℕ, ((i : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun i =>
      WithTop.coe_le_coe.2 le_top
    have cutMul_converges : ∀ (j : ℕ) (ws : ℕ → TestFormOn (univ : Set (Eucl P)) j),
        TestFormOnConverges ws 0 → TestFormOnConverges (fun l => cutMul j (ws l)) 0 := by
      intro j ws h
      refine ⟨tsupport χ, hχc, hχU, fun l => ?_, ?_, fun q => ?_⟩
      · rw [hcoe]
        exact tsupport_smul_subset_left _ _
      · have h0 : ((0 : TestFormOn U j) : DifferentialForm (Eucl P) j) = 0 := rfl
        rw [h0, tsupport_zero]
        exact empty_subset _
      · have h0 : ((0 : TestFormOn U j) : DifferentialForm (Eucl P) j) = 0 := rfl
        simp only [h0, iteratedFDeriv_zero, Pi.zero_apply]
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hb : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ C := fun i =>
          (hχ.continuous_iteratedFDeriv (hle i)).bounded_above_of_compact_support
            (hχc.iteratedFDeriv i)
        choose C hC using hb
        set A : ℝ := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |C i| with hA
        have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => by positivity)
        have hA1 : 0 < A + 1 := by linarith
        set δ : ℝ := ε / (A + 1) with hδ
        have hδpos : 0 < δ := div_pos hε hA1
        have hev : ∀ᶠ l in atTop, ∀ i ∈ Finset.range (q + 1), ∀ x,
            ‖iteratedFDeriv ℝ i (ws l : DifferentialForm (Eucl P) j) x‖ < δ :=
          (Filter.eventually_all_finset _).2
            (fun i _ => eventually_norm_iteratedFDeriv_lt ws h i δ hδpos)
        filter_upwards [hev] with l hl x _
        rw [dist_zero_left, hcoe]
        have hwsl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ws l : DifferentialForm (Eucl P) j) :=
          (ws l).property.1.1
        have hL := leibniz_smul (n := q) (hχ.of_le (hle q)) (hwsl.of_le (hle q)) x
        calc ‖iteratedFDeriv ℝ q (fun y => χ y • (ws l : DifferentialForm (Eucl P) j) y) x‖
            ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
                ‖iteratedFDeriv ℝ (q - i) (ws l : DifferentialForm (Eucl P) j) x‖ := hL
          _ ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |C i| * δ := by
              apply Finset.sum_le_sum
              intro i hi
              have h1 : ‖iteratedFDeriv ℝ i χ x‖ ≤ |C i| := (hC i x).trans (le_abs_self _)
              have h2 : ‖iteratedFDeriv ℝ (q - i) (ws l : DifferentialForm (Eucl P) j) x‖ ≤ δ :=
                (hl (q - i) (Finset.mem_range.2 (by omega)) x).le
              have h3 : (0 : ℝ) ≤ (q.choose i : ℝ) := by positivity
              gcongr
          _ = A * δ := by rw [hA, Finset.sum_mul]
          _ < ε := by
              rw [hδ, mul_div_assoc', div_lt_iff₀ hA1]
              nlinarith
    -- the extension `E Z := Z ∘ (χ • ·)`
    obtain ⟨Ex, hExapply⟩ : ∃ Ex : GeometricCurrentOn U (k + 1) →
        GeometricCurrentOn (univ : Set (Eucl P)) (k + 1),
        ∀ (Z : GeometricCurrentOn U (k + 1)) (w : TestFormOn (univ : Set (Eucl P)) (k + 1)),
          Ex Z w = Z (cutMul (k + 1) w) :=
      ⟨fun Z =>
        { toCurrent := Z.toCurrent ∘ₗ cutMul (k + 1)
          continuous' := fun ws h => Z.continuous' _ (cutMul_converges (k + 1) ws h) },
        fun _ _ => rfl⟩
    have cutMul_admissible : ∀ {j : ℕ} {W : Set (Eucl P)}
        (w : TestFormOn (univ : Set (Eucl P)) j), w ∈ massAdmissibleOn univ j W →
        cutMul j w ∈ massAdmissibleOn U j U := by
      intro j W w hw
      refine ⟨?_, fun x => ?_⟩
      · rw [hcoe]
        exact (tsupport_smul_subset_left _ _).trans hχU
      · rw [hcoe]
        exact (covectorEuclideanNorm_smul_le (hχ01 x) _).trans (hw.2 x)
    have key1 : ∀ Z : GeometricCurrentOn U (k + 1), Z.support ⊆ K →
        ∀ w : TestFormOn U (k + 1),
        Ex Z (testFormOnInclusion (subset_univ U) (k + 1) w) = Z w := by
      intro Z hZ w
      rw [hExapply]
      apply h_iwl_loc_support_locality.1 P (k + 1) U N Z _ _ hN (hZ.trans hKN)
      intro x hx
      rw [hcoe]
      simp only [testFormOnInclusion_coe, hχN x hx, one_smul]
    refine ⟨Ex, key1, ?_, ?_, ?_, ?_, ?_⟩
    · -- (2) boundary
      intro Z hZ w
      have hd : exteriorDerivativeTestOn (univ : Set (Eucl P)) k
          (testFormOnInclusion (subset_univ U) k w) =
          testFormOnInclusion (subset_univ U) (k + 1) (exteriorDerivativeTestOn U k w) :=
        Subtype.ext rfl
      simp only [GeometricCurrentOn.boundary_apply]
      rw [hd, key1 Z hZ]
    · -- (3) support
      intro Z hZ x hx
      by_contra hxK
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hxK
      have hε2 : 0 < ε / 2 := half_pos hε
      have hcb : closedBall x (ε / 2) ⊆ Kᶜ :=
        (closedBall_subset_ball (half_lt_self hε)).trans hball
      have hx2 : x ∉ (Ex Z).zeroRegion := hx.2
      apply hx2
      unfold GeometricCurrentOn.zeroRegion
      refine Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩,
        mem_ball_self hε2⟩
      · rw [closure_ball x hε2.ne']
        exact isCompact_closedBall x (ε / 2)
      · intro w hw
        rw [hExapply]
        have hloc := h_iwl_loc_support_locality.1 P (k + 1) U (closedBall x (ε / 2))ᶜ Z
          (cutMul (k + 1) w) 0 isClosed_closedBall.isOpen_compl
          (fun y hy hyb => hcb hyb (hZ hy)) ?_
        · rw [hloc]
          exact map_zero Z.toCurrent
        · intro y hy
          have hwy : (w : DifferentialForm (Eucl P) (k + 1)) y = 0 := by
            by_contra hne
            exact hy (ball_subset_closedBall (hw (subset_tsupport _ hne)))
          rw [hcoe]
          show χ y • (w : DifferentialForm (Eucl P) (k + 1)) y = 0
          rw [hwy, smul_zero]
    · -- (4) mass
      intro Z
      show (Ex Z).massOn univ ≤ Z.massOn U
      refine sSup_le ?_
      rintro _ ⟨w, hw, rfl⟩
      show ENNReal.ofReal (Ex Z w) ≤ Z.massOn U
      rw [hExapply]
      exact Z.le_massOn (cutMul_admissible w hw)
    · -- (5) boundary mass
      intro Z hZ
      show (Ex Z).boundary.massOn univ ≤ Z.boundary.massOn U
      refine sSup_le ?_
      rintro _ ⟨w, hw, rfl⟩
      have hkey : (Ex Z).boundary w = Z.boundary (cutMul k w) := by
        rw [GeometricCurrentOn.boundary_apply, hExapply, GeometricCurrentOn.boundary_apply]
        apply h_iwl_loc_support_locality.1 P (k + 1) U N Z _ _ hN (hZ.trans hKN)
        intro x hx
        have hev : (fun y => χ y • (w : DifferentialForm (Eucl P) k) y) =ᶠ[𝓝 x]
            (w : DifferentialForm (Eucl P) k) := by
          filter_upwards [hN.mem_nhds hx] with y hy
          rw [hχN y hy, one_smul]
        rw [hcoe]
        show χ x • extDeriv (w : DifferentialForm (Eucl P) k) x =
          extDeriv ((cutMul k w : TestFormOn U k) : DifferentialForm (Eucl P) k) x
        rw [hcoe, hev.extDeriv_eq, hχN x hx, one_smul]
      show ENNReal.ofReal ((Ex Z).boundary w) ≤ Z.boundary.massOn U
      rw [hkey]
      exact Z.boundary.le_massOn (cutMul_admissible w hw)
    · -- (6) weak convergence
      intro Zj Z h w
      simp only [hExapply]
      exact h _
  /- Step 7(v): the extension of an integer multiplicity current is integer multiplicity. -/
  have h_iwl_loc_extension_im : ∀ (P k : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K →
      K ⊆ U → ∀ (Z : GeometricCurrentOn U k) (Y : GeometricCurrentOn (univ : Set (Eucl P)) k),
      IsIntegerMultiplicity Z → Y.support ⊆ K →
      (∀ ω : TestFormOn U k, Y (testFormOnInclusion (subset_univ U) k ω) = Z ω) →
      IsIntegerMultiplicity Y := by
    intro P k U K hU hK hKU Z Y hZ hYK hYZ
    obtain ⟨M, θ, ξ, hT, hθ, hZτ⟩ := hZ
    have hvan : ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U \ K →
        tauAction k M θ ξ (ω : DifferentialForm (Eucl P) k) = 0 := by
      intro ω hω
      rw [← hZτ ω, ← hYZ ω]
      have h0 : Y (testFormOnInclusion (subset_univ U) k ω) = Y 0 := by
        refine h_iwl_loc_support_locality.1 P k univ
          (tsupport (ω : DifferentialForm (Eucl P) k))ᶜ Y _ 0 (isClosed_tsupport _).isOpen_compl
          ?_ ?_
        · intro x hx hx'
          exact (hω hx').2 (hYK hx)
        · intro x hx
          rw [testFormOnInclusion_coe]
          exact image_eq_zero_of_notMem_tsupport hx
      rw [h0, map_zero]
    have hnull : (μHE[k] : Measure (Eucl P)) (M \ K) = 0 := by
      have h := h_iwl_loc_tau_carrier_null P k U (U \ K) M θ ξ (hU.sdiff hK.isClosed)
        sdiff_subset hT hvan
      have heq : M ∩ (U \ K) = M \ K := by
        ext x
        constructor
        · rintro ⟨hM, -, hK'⟩
          exact ⟨hM, hK'⟩
        · rintro ⟨hM, hK'⟩
          exact ⟨hM, hT.subset hM, hK'⟩
      rwa [heq] at h
    obtain ⟨χ, hχ, -, hχU, -, N, hN, hKN, hχN⟩ := exists_cutoff hU hK hKU
    have hsub : M ∩ K ⊆ M := inter_subset_left
    have hMK : NullMeasurableSet (M ∩ K) (μHE[k] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
    have h1 : (μHE[k] : Measure (Eucl P)) ((M ∩ K) \ M) = 0 := by
      rw [sdiff_eq_empty.2 hsub]
      exact measure_empty
    have h2 : (μHE[k] : Measure (Eucl P)) (M \ (M ∩ K)) = 0 := by
      rw [sdiff_self_inter]
      exact hnull
    have hY : ∀ ω : TestFormOn (univ : Set (Eucl P)) k,
        Y ω = tauAction k (M ∩ K) θ ξ (ω : DifferentialForm (Eucl P) k) := by
      intro ω
      let ζ : TestFormOn U k :=
        ⟨fun x => χ x • (ω : DifferentialForm (Eucl P) k) x, cut_mem χ hχ hχU ω⟩
      have hωζ : Y ω = Y (testFormOnInclusion (subset_univ U) k ζ) := by
        refine h_iwl_loc_support_locality.1 P k univ N Y ω _ hN (hYK.trans hKN) ?_
        intro x hx
        rw [testFormOnInclusion_coe]
        show (ω : DifferentialForm (Eucl P) k) x = χ x • (ω : DifferentialForm (Eucl P) k) x
        rw [hχN x hx, one_smul]
      rw [hωζ, hYZ ζ, hZτ ζ]
      unfold tauAction
      have hae : M =ᵐ[(μHE[k] : Measure (Eucl P))] (M ∩ K) := ae_eq_set.2 ⟨h2, h1⟩
      rw [setIntegral_congr_set hae]
      refine setIntegral_congr_fun₀ hMK ?_
      intro x hx
      show θ x * ξ x (χ x • (ω : DifferentialForm (Eucl P) k) x) =
        θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)
      rw [hχN x (hKN hx.2), one_smul]
    have hT' : IsRectifiableTriple (univ : Set (Eucl P)) k (M ∩ K) θ ξ := by
      refine ⟨subset_univ _, hMK, hT.countablyRectifiable.mono hsub,
        fun x hx => hT.pos x hx.1, ?_, ?_, ?_⟩
      · intro K' _ _
        exact (hT.integrableOn K hK hKU).mono_set inter_subset_left
      · exact hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hT.orients] with x hx
        obtain ⟨τ, hτ, htan, hξ⟩ := hx
        exact ⟨τ, hτ, (h_iwl_loc_weighted_tangent_congr.1 P k (M ∩ K) M θ x _ h1 h2).2 htan, hξ⟩
    exact ⟨M ∩ K, θ, ξ, hT', fun x hx => hθ x hx.1, hY⟩
  /- Step 9: restricting an integer multiplicity current to an open subdomain. -/
  have h_iwl_loc_restrict_domain_im : ∀ (P k : ℕ) (U V : Set (Eucl P)) (hVU : V ⊆ U), IsOpen V →
      ∀ (Y : GeometricCurrentOn U k) (X : GeometricCurrentOn V k), IsIntegerMultiplicity Y →
      (∀ ω : TestFormOn V k, X ω = Y (testFormOnInclusion hVU k ω)) →
      IsIntegerMultiplicity X := by
    intro P k U V hVU hV Y X hY hXY
    obtain ⟨M, θ, ξ, hT, hθint, hYω⟩ := hY
    have hMV : NullMeasurableSet (M ∩ V) (μHE[k] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hV.measurableSet.nullMeasurableSet
    refine ⟨M ∩ V, θ, ξ, ?_, fun x hx => hθint x hx.1, ?_⟩
    · refine
        { subset := fun x hx => hx.2
          nullMeasurableSet := hMV
          countablyRectifiable := hT.countablyRectifiable.mono inter_subset_left
          pos := fun x hx => hT.pos x hx.1
          integrableOn := fun K hK hKV =>
            (hT.integrableOn K hK (hKV.trans hVU)).mono_set
              (fun x hx => ⟨hx.1.1, hx.2⟩)
          aestronglyMeasurable :=
            hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
          orients := ?_ }
      have h1 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M ∩ V ⊆ M) hT.orients
      have h2 := ae_restrict_mem₀ hMV
      filter_upwards [h1, h2] with x hx hxMV
      obtain ⟨τ, hτ, htan, hξ⟩ := hx
      exact ⟨τ, hτ, (h_iwl_loc_weighted_tangent_congr.2 P k M V θ x _ hV hxMV.2).mpr htan, hξ⟩
    · intro ω
      rw [hXY ω, hYω]
      have hsupp : ∀ x, x ∉ V → θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x) = 0 := by
        intro x hx
        have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (ω.property.2 h))
        rw [h0, map_zero, mul_zero]
      show ∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)
          ∂(μHE[k] : Measure (Eucl P)) =
        ∫ x in M ∩ V, θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)
          ∂(μHE[k] : Measure (Eucl P))
      rw [inter_comm M V, ← Measure.restrict_restrict hV.measurableSet,
        setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  /- Steps 1–11: the assembly. -/
  intro P m hSlice hCpt U hU Tj T hTj hbd hconv
  have hSptBd := h_iwl_loc_support_locality.2
  have hRest := h_iwl_loc_restriction_local
  have hExt := h_iwl_loc_zero_extension
  have hExtIM := h_iwl_loc_extension_im
  have hRD := h_iwl_loc_restrict_domain_im
  have hGood := h_iwl_loc_good_radius
  obtain ⟨-, -, hR2⟩ := Submission.iwl_restriction_theory
  obtain ⟨-, hIMb, hIMc⟩ := Submission.iwl_im_closure
  have hRWL := Submission.iwl_restriction_weak_limit
  -- local finiteness of the masses of `T_j`, `∂T_j` and `T`
  have hTjfin : ∀ j, ∀ W, CompactlyContainedOpen W U →
      (Tj j).massOn W < ∞ ∧ (Tj j).boundary.massOn W < ∞ := by
    intro j W hW
    have hle : (Tj j).massOn W + (Tj j).boundary.massOn W ≤
        ⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W) :=
      le_iSup (fun j => (Tj j).massOn W + (Tj j).boundary.massOn W) j
    have hlt := lt_of_le_of_lt hle (hbd W hW)
    exact ⟨lt_of_le_of_lt le_self_add hlt, lt_of_le_of_lt le_add_self hlt⟩
  have hTfin : ∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ := by
    intro W hW
    refine lt_of_le_of_lt (hconv.massOn_le_liminf W) (lt_of_le_of_lt ?_ (hbd W hW))
    exact (Filter.liminf_le_limsup (u := fun j => (Tj j).massOn W) (f := atTop)).trans
      (limsup_le_iSup.trans (iSup_mono fun j => le_self_add))
  apply Submission.iwl_im_patching P (m + 1) U hU T
  intro ξ₀ hξ₀
  -- Step 1: the radius `r₀`, the function `d₀` and the set `W₀`
  obtain ⟨ε, hε, hballU⟩ := Metric.isOpen_iff.mp hU ξ₀ hξ₀
  set r₀ : ℝ := ε / 3 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  set d₀ : Eucl P → ℝ := fun x => dist x ξ₀ with hd₀
  set W₀ : Set (Eucl P) := ball ξ₀ (2 * r₀) with hW₀
  have hcW₀U : closedBall ξ₀ (2 * r₀) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hballU
  have hW₀U : W₀ ⊆ U := ball_subset_closedBall.trans hcW₀U
  have hW₀cc : CompactlyContainedOpen W₀ U := by
    refine ⟨isOpen_ball, ?_, ?_⟩
    · rw [closure_ball _ (by positivity)]; exact isCompact_closedBall _ _
    · rw [closure_ball _ (by positivity)]; exact hcW₀U
  set Λ₀ := ⨆ j, ((Tj j).massOn W₀ + (Tj j).boundary.massOn W₀) with hΛ₀
  have hΛ₀fin : Λ₀ < ∞ := hbd W₀ hW₀cc
  have hd₀lip : LipschitzWith 1 d₀ := LipschitzWith.dist_left ξ₀
  have hd₀cont : Continuous d₀ := hd₀lip.continuous
  have hfderiv : ∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ U → ‖fderiv ℝ d₀ x‖₊ ≤ (1 : ℝ≥0) :=
    Eventually.of_forall fun x _ => by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hd₀lip
      rw [← NNReal.coe_le_coe]; simpa using this
  -- Step 2: slices of every `T_j` by `d₀`
  have hS := fun j => hSlice P m U hU (Tj j) (hTjfin j) d₀ 1 hd₀lip.lipschitzOnWith
  choose S hSslice hSsupp hSim hSmass using hS
  -- mass measures and restrictions of `T_j` and `∂T_j` (Simon 2.7–2.9)
  have hMM := fun j => hR2 P (m + 1) U hU (Tj j) (fun W hW => (hTjfin j W hW).1)
  choose μ hμmass hμex hμid using hMM
  have hMMb := fun j => hR2 P m U hU (Tj j).boundary (fun W hW => (hTjfin j W hW).2)
  choose μ' hμ'mass hμ'ex hμ'id using hMMb
  have hmeasLt : ∀ s : ℝ, MeasurableSet {x | x ∈ U ∧ d₀ x < s} := fun s =>
    hU.measurableSet.inter (measurableSet_lt hd₀cont.measurable measurable_const)
  -- the slice mass bound on `(r₀/2, r₀)` with `W := U`, `L_W := 1`
  have hg : ∀ j, ∃ g : ℝ → ℝ≥0∞, Measurable g ∧
      (∀ t ∈ Ioo (r₀ / 2) r₀, (S j t).massOn U ≤ g t) ∧
      ∫⁻ t in Ioo (r₀ / 2) r₀, g t ≤ Λ₀ := by
    intro j
    have hmeasA : MeasurableSet {x | x ∈ U ∧ r₀ / 2 < d₀ x ∧ d₀ x < r₀} :=
      hU.measurableSet.inter ((measurableSet_lt measurable_const hd₀cont.measurable).inter
        (measurableSet_lt hd₀cont.measurable measurable_const))
    obtain ⟨R, hR⟩ := hμex j _ hmeasA
    obtain ⟨g, hgm, hgle, hgint⟩ :=
      hSmass j U hU subset_rfl 1 hfderiv (r₀ / 2) r₀ (by linarith) R hR
    refine ⟨g, hgm, hgle, hgint.trans ?_⟩
    rw [hμid j _ R hR U hU subset_rfl]
    calc ((1 : ℝ≥0) : ℝ≥0∞) * μ j (U ∩ {x | x ∈ U ∧ r₀ / 2 < d₀ x ∧ d₀ x < r₀})
        = μ j (U ∩ {x | x ∈ U ∧ r₀ / 2 < d₀ x ∧ d₀ x < r₀}) := by simp
      _ ≤ μ j W₀ := by
          apply measure_mono
          intro x hx
          have : d₀ x < r₀ := hx.2.2.2
          simp only [hW₀, mem_ball]
          show dist x ξ₀ < 2 * r₀
          linarith
      _ = (Tj j).massOn W₀ := (hμmass j).2 W₀ hW₀cc
      _ ≤ (Tj j).massOn W₀ + (Tj j).boundary.massOn W₀ := le_self_add
      _ ≤ Λ₀ := le_iSup (fun j => (Tj j).massOn W₀ + (Tj j).boundary.massOn W₀) j
  choose g hgm hgle hgint using hg
  -- Step 3: Helly selection for the restrictions to the balls `{d₀ < s}`
  have hsupW₀ : (⨆ j, (Tj j).massOn W₀) < ∞ :=
    lt_of_le_of_lt (iSup_mono fun j => le_self_add) hΛ₀fin
  obtain ⟨ψ, E, hψ, hEc, hRWLprop⟩ :=
    hRWL P (m + 1) U hU Tj T W₀ d₀ hconv isOpen_ball hW₀U hsupW₀ hd₀cont.continuousOn
  -- Steps 4–5: Fatou and the choice of a good radius `r`
  obtain ⟨r, hrI, hrE, hrIM, C, σ, hCfin, hσ, hgC⟩ :=
    hGood (r₀ / 2) r₀ (by linarith) (fun j => g (ψ j)) Λ₀ E
      (fun j t => IsIntegerMultiplicity (S (ψ j) t)) (fun j => hgm (ψ j))
      (fun j => hgint (ψ j)) hΛ₀fin hEc (fun j => hSim (ψ j) (hTj (ψ j)).1)
  -- Step 6: the localized currents
  have hsl := fun j => hSslice (ψ j) r
  choose R' B' hR' hB' hSAB using hsl
  obtain ⟨μT, hμTmass, hμTex, hμTid⟩ := hR2 P (m + 1) U hU T hTfin
  obtain ⟨A, hA⟩ := hμTex {x | x ∈ U ∧ d₀ x < r} (hmeasLt r)
  set K₀ : Set (Eucl P) := closedBall ξ₀ r with hK₀
  have hK₀c : IsCompact K₀ := isCompact_closedBall ξ₀ r
  have hK₀W₀ : K₀ ⊆ W₀ := closedBall_subset_ball (by linarith [hrI.2])
  have hK₀U : K₀ ⊆ U := hK₀W₀.trans hW₀U
  have hlevel : {x | x ∈ U ∧ d₀ x ≤ r} ⊆ K₀ := fun x hx => by
    simp only [hK₀, mem_closedBall]; exact hx.2
  have hR'conv : WeaklyConvergesOn R' A :=
    (hRWLprop r hrE R' A hR' hA).2 K₀ hK₀c hK₀W₀ hlevel
  set Aj : ℕ → GeometricCurrentOn U (m + 1) := fun j => R' (σ j) with hAj
  have hAjconv : WeaklyConvergesOn Aj A := fun ω => (hR'conv ω).comp hσ.tendsto_atTop
  have hclos : closure {x | x ∈ U ∧ d₀ x < r} ⊆ K₀ :=
    closure_minimal (fun x hx => by simp only [hK₀, mem_closedBall]; exact le_of_lt hx.2)
      isClosed_closedBall
  have hAjsupp : ∀ j, (Aj j).support ⊆ K₀ := fun j =>
    ((hRest P (m + 1) U hU _ _ _ (hR' (σ j))).2).trans hclos
  have hAsupp : A.support ⊆ K₀ := ((hRest P (m + 1) U hU _ _ _ hA).2).trans hclos
  -- (a) integrality of `A_j` and `∂A_j`
  have hAjim : ∀ j, IsIntegerMultiplicity (Aj j) := fun j =>
    hIMb P (m + 1) U hU _ _ _ (hTj (ψ (σ j))).1 (hR' (σ j))
  have hBjim : ∀ j, IsIntegerMultiplicity (B' (σ j)) := fun j =>
    hIMb P m U hU _ _ _ (hTj (ψ (σ j))).2 (hB' (σ j))
  have hAjbim : ∀ j, IsIntegerMultiplicity (Aj j).boundary := fun j =>
    hIMc P m U hU (S (ψ (σ j)) r) (B' (σ j)) (Aj j).boundary 1 1 (hrIM (σ j)) (hBjim j)
      (fun ω => by have := hSAB (σ j) ω; simp only [hAj, Int.cast_one, one_mul]; linarith)
  -- (c) mass bounds
  have hball_sub : U ∩ {x | x ∈ U ∧ d₀ x < r} ⊆ W₀ := fun x hx => by
    have : d₀ x < r := hx.2.2
    simp only [hW₀, mem_ball]; show dist x ξ₀ < 2 * r₀; linarith [hrI.2]
  have hAjmass : ∀ j, (Aj j).mass ≤ Λ₀ := fun j => by
    calc (Aj j).mass = μ (ψ (σ j)) (U ∩ {x | x ∈ U ∧ d₀ x < r}) :=
          hμid (ψ (σ j)) _ _ (hR' (σ j)) U hU subset_rfl
      _ ≤ μ (ψ (σ j)) W₀ := measure_mono hball_sub
      _ = (Tj (ψ (σ j))).massOn W₀ := (hμmass (ψ (σ j))).2 W₀ hW₀cc
      _ ≤ (Tj (ψ (σ j))).massOn W₀ + (Tj (ψ (σ j))).boundary.massOn W₀ := le_self_add
      _ ≤ Λ₀ := le_iSup (fun j => (Tj j).massOn W₀ + (Tj j).boundary.massOn W₀) (ψ (σ j))
  have hBjmass : ∀ j, (B' (σ j)).mass ≤ Λ₀ := fun j => by
    calc (B' (σ j)).mass = μ' (ψ (σ j)) (U ∩ {x | x ∈ U ∧ d₀ x < r}) :=
          hμ'id (ψ (σ j)) _ _ (hB' (σ j)) U hU subset_rfl
      _ ≤ μ' (ψ (σ j)) W₀ := measure_mono hball_sub
      _ = (Tj (ψ (σ j))).boundary.massOn W₀ := (hμ'mass (ψ (σ j))).2 W₀ hW₀cc
      _ ≤ (Tj (ψ (σ j))).massOn W₀ + (Tj (ψ (σ j))).boundary.massOn W₀ := le_add_self
      _ ≤ Λ₀ := le_iSup (fun j => (Tj j).massOn W₀ + (Tj j).boundary.massOn W₀) (ψ (σ j))
  have hSjmass : ∀ j, (S (ψ (σ j)) r).mass ≤ C := fun j =>
    (hgle (ψ (σ j)) r hrI).trans (hgC j)
  have hAjbmass : ∀ j, (Aj j).boundary.mass ≤ C + Λ₀ := fun j => by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have heq : (Aj j).boundary ω = S (ψ (σ j)) r ω + B' (σ j) ω := by
      have := hSAB (σ j) ω; simp only [hAj]; linarith
    show ENNReal.ofReal ((Aj j).boundary ω) ≤ C + Λ₀
    rw [heq]
    exact (ENNReal.ofReal_add_le).trans (add_le_add
      (((S (ψ (σ j)) r).le_massOn hω).trans (hSjmass j))
      (((B' (σ j)).le_massOn hω).trans (hBjmass j)))
  -- Steps 7–8: extension to `ℝ^P` and the compact case
  obtain ⟨Ex, hEx1, hEx1b, hExsupp, hExmass, hExbmass, hExconv⟩ := hExt P m U K₀ hU hK₀c hK₀U
  set Xj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1) := fun j => Ex (Aj j) with hXj
  have hXint : ∀ j, IsIntegralCurrent (Xj j) := fun j =>
    ⟨hExtIM P (m + 1) U K₀ hU hK₀c hK₀U (Aj j) (Xj j) (hAjim j) (hExsupp _ (hAjsupp j))
        (hEx1 _ (hAjsupp j)),
      hExtIM P m U K₀ hU hK₀c hK₀U (Aj j).boundary (Xj j).boundary (hAjbim j)
        ((hSptBd P m univ (Xj j)).trans (hExsupp _ (hAjsupp j))) (hEx1b _ (hAjsupp j))⟩
  have hXsupp : ∀ j, (Xj j).support ⊆ K₀ := fun j => hExsupp _ (hAjsupp j)
  have hXbd : (⨆ j, ((Xj j).mass + (Xj j).boundary.mass)) < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun j => add_le_add ((hExmass _).trans (hAjmass j))
      ((hExbmass _ (hAjsupp j)).trans (hAjbmass j))) ?_
    exact ENNReal.add_lt_top.2 ⟨hΛ₀fin, ENNReal.add_lt_top.2 ⟨hCfin, hΛ₀fin⟩⟩
  have hXconv : WeaklyConvergesOn Xj (Ex A) := hExconv Aj A hAjconv
  have hExAim : IsIntegerMultiplicity (Ex A) := hCpt K₀ hK₀c Xj (Ex A) hXint hXsupp hXbd hXconv
  -- Step 9: back to `U`
  have hAim : IsIntegerMultiplicity A :=
    hRD P (m + 1) univ U (subset_univ U) hU (Ex A) A hExAim (fun ω => (hEx1 A hAsupp ω).symm)
  -- Steps 10–11: local agreement on `B_r(ξ₀)`, then patching
  refine ⟨ball ξ₀ r, isOpen_ball, mem_ball_self (by linarith [hrI.1]),
    ball_subset_closedBall.trans hK₀U, A, hAim, ?_⟩
  intro ω hω
  refine ((hRest P (m + 1) U hU T _ A hA).1 ω (fun x hx => ?_)).symm
  have hxω : x ∉ tsupport (ω : DifferentialForm (Eucl P) (m + 1)) := by
    intro hxt
    have hxb := hω hxt
    exact hx ⟨hK₀U (ball_subset_closedBall hxb), by simpa [d₀, mem_ball] using hxb⟩
  exact image_eq_zero_of_notMem_tsupport hxω

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
