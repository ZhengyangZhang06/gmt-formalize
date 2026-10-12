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

/-- Closed Egorov theorem on `ℝⁿ` (Simon Ch. 2, proof of Theorem 1.5): if Borel `f k` converge
pointwise on a Borel set `C` to a Borel `g`, then for every `ε > 0` there is a closed `A ⊆ C` with
`Lⁿ(C \ A) < ε` such that `f k → g` uniformly on every bounded part `A ∩ B̄_R(0)`. -/
theorem Submission.lpf_c1r_egoroff_closed : ∀ (n : ℕ) (C : Set (Eucl n)) (f : ℕ → Eucl n → ℝ) (g : Eucl n → ℝ), MeasurableSet C → (∀ k, Measurable (f k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => f k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Eucl n), IsClosed A ∧ A ⊆ C ∧ (volume : Measure (Eucl n)) (C \ A) < ε ∧ ∀ R : ℝ, TendstoUniformlyOn f g atTop (A ∩ closedBall 0 R) := by
  intro n C f g hC hf hg hfg ε hε
  -- Step 1: positive budgets `δ j` with `∑ j, δ j < ε` (this also covers `ε = ∞`).
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  -- Step 2: the bounded annuli `S j = {x : j ≤ ‖x‖ < j + 1}` partition `ℝⁿ`.
  set S : ℕ → Set (Eucl n) := fun j => ball 0 ((j : ℝ) + 1) \ ball 0 j
  have hSle : ∀ j, ∀ x ∈ S j, (j : ℝ) ≤ ‖x‖ := fun j x hx => by
    simpa [mem_ball_zero_iff] using hx.2
  have hScov : ∀ x : Eucl n, x ∈ S ⌊‖x‖⌋₊ := fun x => by
    simp only [S, Set.mem_sdiff, mem_ball_zero_iff, not_lt]
    exact ⟨Nat.lt_floor_add_one _, Nat.floor_le (norm_nonneg x)⟩
  -- Step 3: on each `C ∩ S j` (finite measure), Egorov gives `t` with `Lⁿ(t) ≤ δ j / 2` and
  -- uniform convergence on `(C ∩ S j) \ t`; inner regularity gives a closed `F ⊆ (C ∩ S j) \ t`
  -- with defect `< δ j / 2`.
  have key : ∀ j, ∃ F : Set (Eucl n), F ⊆ C ∩ S j ∧ IsClosed F ∧
      (volume : Measure (Eucl n)) ((C ∩ S j) \ F) < δ j ∧ TendstoUniformlyOn f g atTop F := by
    intro j
    have hm : MeasurableSet (C ∩ S j) := hC.inter (measurableSet_ball.diff measurableSet_ball)
    have hfin : (volume : Measure (Eucl n)) (C ∩ S j) ≠ ∞ :=
      ((measure_mono (inter_subset_right.trans sdiff_subset)).trans_lt measure_ball_lt_top).ne
    have hδ2 : (0 : ℝ≥0∞) < (δ j : ℝ≥0∞) / 2 := ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos j).ne')
    obtain ⟨t, -, htm, htμ, htu⟩ := tendstoUniformlyOn_of_ae_tendsto (μ := volume)
      (fun k => (hf k).stronglyMeasurable) hg.stronglyMeasurable hm hfin
      (Eventually.of_forall fun x hx => hfg x hx.1) hδ2
    obtain ⟨F, hF, hFc, hFμ⟩ := (hm.diff htm).exists_isClosed_sdiff_lt (μ := volume)
      (ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)) hδ2.ne'
    refine ⟨F, hF.trans sdiff_subset, hFc, ?_, htu.mono hF⟩
    calc (volume : Measure (Eucl n)) ((C ∩ S j) \ F)
        ≤ volume (t ∪ ((C ∩ S j) \ t) \ F) := measure_mono fun x hx => by
          by_cases hxt : x ∈ t
          · exact Or.inl hxt
          · exact Or.inr ⟨⟨hx.1, hxt⟩, hx.2⟩
      _ ≤ volume t + volume (((C ∩ S j) \ t) \ F) := measure_union_le _ _
      _ < (δ j : ℝ≥0∞) / 2 + (δ j : ℝ≥0∞) / 2 :=
          (add_le_add htμ le_rfl).trans_lt (ENNReal.add_lt_add_left
            (ENNReal.div_ne_top ENNReal.coe_ne_top two_ne_zero) hFμ)
      _ = δ j := ENNReal.add_halves _
  choose F hFsub hFc hFμ hFu using key
  refine ⟨⋃ j, F j, ?_, iUnion_subset fun j => (hFsub j).trans inter_subset_left, ?_, ?_⟩
  · -- Step 4: `ball x 1` meets `F j ⊆ S j` only for `j < ‖x‖ + 1`, so the family is locally
    -- finite and its union is closed.
    refine LocallyFinite.isClosed_iUnion (fun x => ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩) hFc
    refine (finite_Iio ⌈‖x‖ + 1⌉₊).subset fun j ⟨y, hyF, hyx⟩ => ?_
    have h1 := hSle j y (hFsub j hyF).2
    have h2 := norm_sub_norm_le y x
    have h3 := mem_ball_iff_norm.1 hyx
    exact Nat.lt_ceil.2 (by linarith)
  · -- Step 5: `C \ ⋃ j, F j ⊆ ⋃ j, (C ∩ S j) \ F j`, of measure `≤ ∑ j, δ j < ε`.
    calc (volume : Measure (Eucl n)) (C \ ⋃ j, F j)
        ≤ volume (⋃ j, (C ∩ S j) \ F j) := measure_mono fun x hx =>
          mem_iUnion.2 ⟨⌊‖x‖⌋₊, ⟨hx.1, hScov x⟩, fun h => hx.2 (mem_iUnion.2 ⟨_, h⟩)⟩
      _ ≤ ∑' j, volume ((C ∩ S j) \ F j) := measure_iUnion_le _
      _ ≤ ∑' j, (δ j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => (hFμ j).le
      _ < ε := hδsum
  · -- Step 6: `(⋃ j, F j) ∩ B̄_R(0)` lies in the finite union of `F j`, `j ≤ ⌈R⌉₊`, on each of
    -- which the convergence is uniform.
    intro R u hu
    filter_upwards [(Finset.range (⌈R⌉₊ + 1)).eventually_all.2 fun j _ => hFu j u hu]
      with k hk x hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx.1
    refine hk j (Finset.mem_range.2 (Nat.lt_succ_of_le ?_)) x hj
    have h1 := hSle j x (hFsub j hj).2
    have h2 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx.2
    exact_mod_cast (h1.trans h2).trans (Nat.le_ceil R)

/-- Simon Ch. 2, proof of Theorem 1.5 (C¹ Approximation Theorem, p. 44), the `η_k` step.  Let
`g : ℝⁿ → ℝ` be Lipschitz and `C` closed, with `g` differentiable at every point of `C` and `Dg`
continuous on `C`.  Then there is a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε` on which the remainder
`R(x, y) = (g(y) − g(x) − Dg(x)(y − x)) / |y − x|` tends to `0` as `y → x` in `A`, uniformly for
`x` in each compact `L ⊆ A` (Whitney's condition 1.6 (‡)).  The functions
`η_k(x) = sup ({0} ∪ {|R(x, y)| : y ∈ C, 0 < |y − x| < 1/(k+1)})` (`η_k = 0` off `C`) are Borel
and tend to `0` on `C`, so Egoroff (`lpf_c1r_egoroff_closed`) makes the convergence uniform on the
bounded parts of a closed `A ⊆ C`. -/
theorem Submission.lpf_c1r_uniform_remainder :
    ∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ C : Set (Eucl n), IsClosed C →
      (∀ x ∈ C, DifferentiableAt ℝ g x) → ContinuousOn (fderiv ℝ g) C → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ A : Set (Eucl n), IsClosed A ∧ A ⊆ C ∧ (volume : Measure (Eucl n)) (C \ A) < ε ∧
        ∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ δ * ‖y - x‖ := by
  intro n g K hg C hC hdiff hDg ε hε
  -- `q x y = |R(x, y)|`.
  obtain ⟨q, hq⟩ : ∃ q : Eucl n → Eucl n → ℝ,
      ∀ x y, q x y = ‖g y - g x - fderiv ℝ g x (y - x)‖ / ‖y - x‖ := ⟨_, fun _ _ => rfl⟩
  -- Step 2: `|R(x, y)| ≤ 2K`, as `‖Dg(x)‖ ≤ K`.
  have hq_le : ∀ x y, q x y ≤ 2 * K := by
    intro x y
    have h1 : ‖g y - g x‖ ≤ K * ‖y - x‖ := by simpa only [dist_eq_norm] using hg.dist_le_mul y x
    have h2 : ‖fderiv ℝ g x (y - x)‖ ≤ K * ‖y - x‖ :=
      ((fderiv ℝ g x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hg) (norm_nonneg _))
    rw [hq]
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ ‖g y - g x‖ + ‖fderiv ℝ g x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ K * ‖y - x‖ + K * ‖y - x‖ := add_le_add h1 h2
      _ = 2 * K * ‖y - x‖ := by ring
  -- Step 1: `σ r x = sup ({0} ∪ {|R(x, y)| : y ∈ C, 0 < |y − x| < r})`, a real number in
  -- `[0, 2K]`, so that `η_k = 1_C · σ (1/(k+1))`.
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → Eucl n → ℝ, ∀ r x,
      σ r x = sSup (insert 0 (q x '' {y | y ∈ C ∧ 0 < ‖y - x‖ ∧ ‖y - x‖ < r})) :=
    ⟨_, fun _ _ => rfl⟩
  have hbdd : ∀ r x,
      BddAbove (insert (0 : ℝ) (q x '' {y | y ∈ C ∧ 0 < ‖y - x‖ ∧ ‖y - x‖ < r})) := by
    refine fun r x => ⟨2 * (K : ℝ), ?_⟩
    rintro a (rfl | ⟨y, -, rfl⟩)
    · positivity
    · exact hq_le x y
  have hσ_nonneg : ∀ r x, 0 ≤ σ r x := by
    intro r x
    rw [hσ]
    exact le_csSup (hbdd r x) (Set.mem_insert _ _)
  have hσ_ge : ∀ r x y, y ∈ C → 0 < ‖y - x‖ → ‖y - x‖ < r → q x y ≤ σ r x := by
    intro r x y hy h0 hr
    rw [hσ]
    exact le_csSup (hbdd r x) (Or.inr ⟨y, ⟨hy, h0, hr⟩, rfl⟩)
  have hσ_le : ∀ r x c, 0 ≤ c → (∀ y, y ∈ C → 0 < ‖y - x‖ → ‖y - x‖ < r → q x y ≤ c) →
      σ r x ≤ c := by
    intro r x c hc h
    rw [hσ]
    refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
    rintro a (rfl | ⟨y, ⟨hy, h0, hr⟩, rfl⟩)
    · exact hc
    · exact h y hy h0 hr
  have hσ_lt : ∀ r x t, 0 ≤ t → t < σ r x →
      ∃ y, y ∈ C ∧ 0 < ‖y - x‖ ∧ ‖y - x‖ < r ∧ t < q x y := by
    intro r x t ht h
    rw [hσ] at h
    obtain ⟨a, ha, hta⟩ := exists_lt_of_lt_csSup ⟨0, Set.mem_insert _ _⟩ h
    rcases ha with rfl | ⟨y, ⟨hy, h0, hr⟩, rfl⟩
    · exact absurd hta (not_lt.mpr ht)
    · exact ⟨y, hy, h0, hr, hta⟩
  -- Step 3: `σ (1/(k+1)) x → 0` for `x ∈ C`, since `g` is differentiable at `x`.
  have htend : ∀ x ∈ C, Tendsto (fun k : ℕ => σ (1 / ((k : ℝ) + 1)) x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro γ hγ
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp
      (Asymptotics.isLittleO_iff.mp (hdiff x hx).hasFDerivAt.isLittleO (half_pos hγ))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
    have hle : σ (1 / ((k : ℝ) + 1)) x ≤ γ / 2 := by
      refine hσ_le _ x _ (half_pos hγ).le fun y _ _ hr => ?_
      rw [hq]
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos hγ).le
        (hball (by rw [dist_eq_norm]; linarith))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hσ_nonneg _ x)]
    linarith
  -- Step 4 (Route 1): `1_C · σ r` is Borel.  For `t ≥ 0`, `{1_C · σ r > t}` is
  -- `C ∩ ⋃_{y ∈ C} (U_y ∩ O_y)`, where `U_y = {x : 0 < |y − x| < r}` and `O_y` is open with
  -- `O_y ∩ C ∩ U_y = {x ∈ C ∩ U_y : |R(x, y)| > t}`; `O_y` exists because `x ↦ |R(x, y)|` is
  -- continuous on `C ∩ U_y` (`Dg` is continuous on `C`).
  have hmeas : ∀ r, Measurable (C.indicator (σ r)) := by
    intro r
    let U : Eucl n → Set (Eucl n) := fun y => {x | 0 < ‖y - x‖ ∧ ‖y - x‖ < r}
    have hU : ∀ y, IsOpen (U y) := fun y =>
      (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).inter
        (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const)
    have hcont : ∀ y, ContinuousOn (fun x => q x y) (C ∩ U y) := by
      intro y
      simp only [hq]
      refine ContinuousOn.div ?_ (continuous_const.sub continuous_id).norm.continuousOn
        fun x hx => hx.2.1.ne'
      exact ((continuous_const.sub hg.continuous).continuousOn.sub
        ((hDg.mono Set.inter_subset_left).clm_apply
          (continuous_const.sub continuous_id).continuousOn)).norm
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · have huniv : C.indicator (σ r) ⁻¹' Ioi t = univ := Set.eq_univ_of_forall fun x =>
        ht.trans_le (Set.indicator_nonneg (fun x _ => hσ_nonneg r x) x)
      rw [huniv]
      exact MeasurableSet.univ
    · choose O hOo hOeq using fun y => _root_.continuousOn_iff'.mp (hcont y) (Ioi t) isOpen_Ioi
      have hset : C.indicator (σ r) ⁻¹' Ioi t = C ∩ ⋃ y ∈ C, (U y ∩ O y) := by
        ext x
        constructor
        · intro hx
          by_cases hxC : x ∈ C
          · rw [Set.mem_preimage, Set.indicator_of_mem hxC, Set.mem_Ioi] at hx
            obtain ⟨y, hyC, h0, hr, hty⟩ := hσ_lt r x t ht hx
            have hxO : x ∈ (fun x => q x y) ⁻¹' Ioi t ∩ (C ∩ U y) := ⟨hty, hxC, h0, hr⟩
            rw [hOeq y] at hxO
            exact ⟨hxC, Set.mem_biUnion hyC ⟨⟨h0, hr⟩, hxO.1⟩⟩
          · rw [Set.mem_preimage, Set.indicator_of_notMem hxC, Set.mem_Ioi] at hx
            exact absurd hx (not_lt.mpr ht)
        · rintro ⟨hxC, hx⟩
          obtain ⟨y, hyC, hxU, hxO⟩ := Set.mem_iUnion₂.mp hx
          have hxO' : x ∈ O y ∩ (C ∩ U y) := ⟨hxO, hxC, hxU⟩
          rw [← hOeq y] at hxO'
          rw [Set.mem_preimage, Set.indicator_of_mem hxC, Set.mem_Ioi]
          exact hxO'.1.trans_le (hσ_ge r x y hyC hxU.1 hxU.2)
      rw [hset]
      exact hC.measurableSet.inter (isOpen_biUnion fun y _ => (hU y).inter (hOo y)).measurableSet
  -- Step 5: Egoroff on `C` (sibling `egoroff_closed`) for `η_k = 1_C · σ (1/(k+1)) → 0`.
  obtain ⟨η, hη⟩ : ∃ η : ℕ → Eucl n → ℝ, ∀ k, η k = C.indicator (σ (1 / ((k : ℝ) + 1))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hAc, hAC, hCA, hunif⟩ := Submission.lpf_c1r_egoroff_closed n C η 0
    hC.measurableSet (fun k => by rw [hη]; exact hmeas _) measurable_const
    (fun x hx => (htend x hx).congr fun k => by rw [hη, Set.indicator_of_mem hx]) ε hε
  refine ⟨A, hAc, hAC, hCA, fun L hL hLA δ hδ => ?_⟩
  -- Step 6: `L ⊆ A ∩ B̄_R(0)` for some `R`, so `η_k < δ` on `L` for some `k`; take `ρ = 1/(k+1)`.
  obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp
    ((hunif R).mono (fun x hx => ⟨hLA hx, hR hx⟩ : L ⊆ A ∩ closedBall 0 R)) δ hδ).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hxL y hyA hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have hxC : x ∈ C := hAC (hLA hxL)
  have h0 : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hr : ‖y - x‖ < 1 / ((k : ℝ) + 1) := by rwa [← dist_eq_norm, dist_comm]
  have hσδ : σ (1 / ((k : ℝ) + 1)) x < δ := by
    have hkx := hk x hxL
    rw [Pi.zero_apply, hη, Set.indicator_of_mem hxC, dist_zero_left, Real.norm_eq_abs] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hqδ := (hσ_ge _ x y (hAC hyA) h0 hr).trans_lt hσδ
  rw [hq, div_lt_iff₀ h0] at hqδ
  exact hqδ.le

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
