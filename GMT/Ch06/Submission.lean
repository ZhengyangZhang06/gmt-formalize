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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
