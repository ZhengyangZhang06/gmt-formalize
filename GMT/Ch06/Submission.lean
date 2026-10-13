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

/-- Smooth cutoff: for a compact `K` inside an open `U ⊆ ℝ^P` there is a `C^∞` function
`0 ≤ χ ≤ 1` with compact support in `U` that equals `1` on an open neighbourhood `N` of `K`. -/
theorem Submission.fiw_tb_ext_cutoff :
    ∀ (P : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U →
      ∃ (χ : Eucl P → ℝ) (N : Set (Eucl P)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ IsOpen N ∧ K ⊆ N ∧
        ∀ x ∈ N, χ x = 1 := by
  intro P U K hU hK hKU
  -- Compact `L₁, L` with `K ⊆ interior L₁ ⊆ L₁ ⊆ interior L ⊆ L ⊆ U`.
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L₁, hL₁, hKL₁, hL₁L⟩ := exists_compact_between hK isOpen_interior hKL
  -- Smooth Urysohn: `f` is `C^∞`, `0 ≤ f ≤ 1`, `support f = interior L`, `f = 1` exactly on `L₁`.
  obtain ⟨f, hf, hfr, hfs, hf1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) isOpen_interior hL₁.isClosed hL₁L
  -- `L` is closed, so `tsupport f = closure (interior L) ⊆ L`; hence it is compact and `⊆ U`.
  have htsupp : tsupport f ⊆ L :=
    closure_minimal (hfs.symm ▸ interior_subset) hL.isClosed
  refine ⟨f, interior L₁, hf, fun x => hfr (mem_range_self x), ?_, htsupp.trans hLU,
    isOpen_interior, hKL₁, fun x hx => (hf1 x).mp (interior_subset hx)⟩
  exact hL.of_isClosed_subset (isClosed_tsupport _) htsupp
/-- Products with a cutoff (Simon Ch. 6, §2): if `χ` is `C^∞` with `tsupport χ ⊆ W`, then
`ω ↦ χ ω` is a linear map `𝒟^q(V) → 𝒟^q(W)`, acting pointwise on the underlying forms. -/
theorem Submission.fiw_tb_ext_smul_testForm :
    ∀ (P q : ℕ) (V W : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ →
      tsupport χ ⊆ W → ∃ L : TestFormOn V q →ₗ[ℝ] TestFormOn W q, ∀ (ω : TestFormOn V q)
        (x : Eucl P), (L ω : DifferentialForm (Eucl P) q) x =
          χ x • (ω : DifferentialForm (Eucl P) q) x := by
  intro P q V W χ hχ hχW
  -- `χ ω` is smooth, its support lies in the compact `tsupport ω` and in `tsupport χ ⊆ W`.
  have hmem : ∀ ω : TestFormOn V q,
      (fun x => χ x • (ω : DifferentialForm (Eucl P) q) x) ∈ TestFormOn W q := by
    intro ω
    obtain ⟨⟨hs, hc⟩, -⟩ := ω.property
    refine ⟨⟨hχ.smul hs, ?_⟩, (tsupport_smul_subset_left _ _).trans hχW⟩
    exact hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)
  -- Additivity and homogeneity hold pointwise on the underlying forms.
  refine ⟨{ toFun := fun ω => ⟨_, hmem ω⟩, map_add' := ?_, map_smul' := ?_ }, fun ω x => rfl⟩
  · intro a b
    apply Subtype.ext
    funext x
    change χ x • ((a : DifferentialForm (Eucl P) q) x + (b : DifferentialForm (Eucl P) q) x) = _
    rw [smul_add]
    rfl
  · intro c a
    apply Subtype.ext
    funext x
    change χ x • (c • (a : DifferentialForm (Eucl P) q) x) =
      c • (χ x • (a : DifferentialForm (Eucl P) q) x)
    rw [smul_comm]
/-- Locality of a current (cf. the support `spt T`, Simon Ch. 6, 2.11): if `Z` vanishes on every
test form whose support misses `K`, and `η = ω` on an open `N ⊇ K`, then `Z(η) = Z(ω)`.  The difference
`η - ω` vanishes on `N`, so its support lies in the closed set `ℝ^P ∖ N`, which misses `K`; by
linearity `Z(η) - Z(ω) = Z(η - ω) = 0`. -/
theorem Submission.fiw_tb_ext_apply_eq_of_eqOn : ∀ (P q : ℕ) (V K N : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen N → K ⊆ N → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → ∀ ω η : TestFormOn V q, (∀ x ∈ N, (η : DifferentialForm (Eucl P) q) x = (ω : DifferentialForm (Eucl P) q) x) → Z η = Z ω := by
  intro P q V K N Z hN hKN hZ ω η hηω
  -- `η - ω` vanishes on the open set `N`, so its support lies in the closed set `Nᶜ`.
  have hsupp : tsupport ((η - ω : TestFormOn V q) : DifferentialForm (Eucl P) q) ⊆ Nᶜ := by
    apply closure_minimal _ hN.isClosed_compl
    intro x hx hxN
    apply hx
    change (η : DifferentialForm (Eucl P) q) x - (ω : DifferentialForm (Eucl P) q) x = 0
    rw [hηω x hxN, sub_self]
  -- `Nᶜ` misses `K ⊆ N`, so `Z(η - ω) = 0`; conclude by linearity.
  have h0 : Z (η - ω) = 0 :=
    hZ _ (Disjoint.mono_left hsupp (disjoint_compl_left.mono_right hKN))
  have h1 : Z (η - ω) = Z η - Z ω := Z.toCurrent.map_sub η ω
  rw [h1] at h0
  exact sub_eq_zero.mp h0
/-- **Support of a current vanishing off a closed set (Simon Ch. 6, 2.11).**  If `Z ∈ 𝒟_q(V)`,
`V` open, kills every test form whose support misses the closed set `K`, then `spt Z ⊆ K`.  A point
`x ∈ V \ K` has a ball `B_ε(x) ⊆ V \ K`; `W = B_{ε/2}(x)` is open with compact closure
`closure W ⊆ B_ε(x) ⊆ V`, and `Z` vanishes on `W`, so `x` lies in the zero region of `Z`. -/
theorem Submission.fiw_tb_ext_support_subset : ∀ (P q : ℕ) (V K : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen V → IsClosed K → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → Z.support ⊆ K := by
  intro P q V K Z hV hK hZ x hx
  by_contra hxK
  obtain ⟨hxV, hxz⟩ := hx
  -- `V \ K` is an open neighbourhood of `x`: pick `B_ε(x) ⊆ V \ K`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hV.sdiff hK) x ⟨hxV, hxK⟩
  -- `W = B_{ε/2}(x)` is one of the open sets whose union is the zero region of `Z`.
  apply hxz
  refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (half_pos hε)⟩
  · exact (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  · exact (closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (half_lt_self hε))).trans (hball.trans sdiff_subset)
  · -- a test form supported in `W ⊆ B_ε(x)` has support disjoint from `K`
    intro ω hω
    apply hZ
    rw [Set.disjoint_left]
    intro y hy hyK
    exact (hball (ball_subset_ball (half_le_self hε.le) (hω hy))).2 hyK
/-- Homogeneity of the Euclidean coefficient norm (Simon Ch. 6, 1.15, 2.4–2.5):
`|c α| = |c| |α|`.  Every coefficient of `c • α` on an increasing tuple of basis vectors is
`c` times that of `α`, so each squared coefficient gains the factor `c²`; pull `c²` out of the
finite sum and use `√(c² s) = √(c²) √s = |c| √s`. -/
theorem Submission.fiw_tb_ext_covectorNorm_smul : ∀ (P q : ℕ) (c : ℝ) (α : Covector (Eucl P) q), covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
  intro P q c α
  unfold covectorEuclideanNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs
  · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
  · simp
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Y) < ∞` and `|ω(x)| ≤ C` everywhere (Euclidean
coefficient norm) with `C > 0`, then `|Y(ω)| ≤ C · M(Y)`. -/
theorem Submission.br_la_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U n) (ω : TestFormOn U n) (C : ℝ),
      0 < C → (∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      Y.mass ≠ ∞ → |Y ω| ≤ C * Y.mass.toReal := by
  intro P n U Y ω C hC hω hY
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
  -- If `|η| ≤ C` pointwise, then `C⁻¹ η` is mass-admissible, hence `Y(η) ≤ C · M(Y)`.
  have hone : ∀ η : TestFormOn U n,
      (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ C) →
        Y η ≤ C * Y.mass.toReal := by
    intro η hη
    have hadm : C⁻¹ • η ∈ massAdmissibleOn U n U := by
      refine ⟨(C⁻¹ • η).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (C⁻¹ • (η : DifferentialForm (Eucl P) n) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hC), inv_mul_le_iff₀ hC, mul_one]
      exact hη x
    have hle : ENNReal.ofReal (Y (C⁻¹ • η)) ≤ Y.mass := Y.le_massOn hadm
    rwa [ENNReal.ofReal_le_iff_le_toReal hY, map_smul, smul_eq_mul, inv_mul_le_iff₀ hC] at hle
  -- Apply this to `ω` and to `-ω`, using `|-ω(x)| = |ω(x)|` and `Y(-ω) = -Y(ω)`.
  have hneg := hone (-ω) fun x => by
    change covectorEuclideanNorm (-(ω : DifferentialForm (Eucl P) n) x) ≤ C
    rw [covectorEuclideanNorm_neg]
    exact hω x
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hneg
  exact abs_le.mpr ⟨by linarith, hone ω hω⟩
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Z) < ∞` and `|η(x)| ≤ c` everywhere (Euclidean
coefficient norm) with `c > 0`, then `|Z(η)| ≤ c · M(Z)`. -/
theorem Submission.fiw_tb_te_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U n) (η : TestFormOn U n) (c : ℝ),
      0 < c → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ c) →
      Z.mass ≠ ∞ → |Z η| ≤ c * Z.mass.toReal := by
  intro P n U Z η c hc hη hZ
  -- Homogeneity of the Euclidean coefficient norm: `|t β| = |t| |β|`.
  have hsmul : ∀ (t : ℝ) (β : Covector (Eucl P) n),
      covectorEuclideanNorm (t • β) = |t| * covectorEuclideanNorm β := by
    intro t β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- If `|θ| ≤ c` pointwise, then `c⁻¹ θ` is mass-admissible, hence `Z(θ) ≤ c · M(Z)`.
  have hone : ∀ θ : TestFormOn U n,
      (∀ x, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) n) x) ≤ c) →
        Z θ ≤ c * Z.mass.toReal := by
    intro θ hθ
    have hadm : c⁻¹ • θ ∈ massAdmissibleOn U n U := by
      refine ⟨(c⁻¹ • θ).property.2, fun x => ?_⟩
      change covectorEuclideanNorm (c⁻¹ • (θ : DifferentialForm (Eucl P) n) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ hc, mul_one]
      exact hθ x
    have hle : ENNReal.ofReal (Z (c⁻¹ • θ)) ≤ Z.mass := Z.le_massOn hadm
    rwa [ENNReal.ofReal_le_iff_le_toReal hZ, map_smul, smul_eq_mul, inv_mul_le_iff₀ hc] at hle
  -- Apply this to `η` and to `-η`, using `|-η(x)| = |η(x)|` and `Z(-η) = -Z(η)`.
  have hneg := hone (-η) fun x => by
    change covectorEuclideanNorm (-(η : DifferentialForm (Eucl P) n) x) ≤ c
    rw [covectorEuclideanNorm_neg]
    exact hη x
  have hZneg : Z (-η) = -Z η := map_neg Z.toCurrent η
  rw [hZneg] at hneg
  exact abs_le.mpr ⟨by linarith, hone η hη⟩
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
/-- If `M ⊆ U` is `μ`-null on every open `W ⊂⊂ U` on which `T` vanishes, then `μ(M ∖ spt T) = 0`:
`M ∖ spt T` lies in the zero region (Simon 2.11), a countable union of such `W` (Lindelöf). -/
theorem Submission.lpf_rsn_null_diff_support_of_local_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0 := by
  intro P n U T M μ hMU hloc
  -- Countably many of the open sets whose union is `T.zeroRegion` already cover it.
  obtain ⟨S, hSc, hSsub, hSeq⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Eucl P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- As `M ⊆ U`, every point of `M ∖ spt T` lies in `T.zeroRegion = ⋃₀ S`.
  have hsub : M \ T.support ⊆ ⋃ W ∈ S, M ∩ W := by
    rintro x ⟨hxM, hxs⟩
    have hxZ : x ∈ ⋃₀ S := by
      rw [hSeq]
      by_contra hxZ
      exact hxs ⟨hMU hxM, hxZ⟩
    obtain ⟨W, hWS, hxW⟩ := hxZ
    exact mem_biUnion hWS ⟨hxM, hxW⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hSc).2 fun W hWS => ?_)
  obtain ⟨hWo, hWc, hWU, hWv⟩ := hSsub hWS
  exact hloc W hWo hWc hWU hWv
/-- Finitely many `n`-covectors separate `n`-vectors (Simon Ch. 6, §1; used for Lemma 3.9 to show
that a representation `τ(M, θ, ξ)` of `T` lives on `spt T` up to an `Hⁿ`-null set).  Evaluation on
tuples of standard basis vectors, `Φ(α)(r) = α(e_{r(1)}, …, e_{r(n)})`, embeds `Λⁿ(ℝ^P)` linearly
into `ℝ^(Fin n → Fin P)`, since a multilinear map is determined by its values on basis vectors.
So `Λⁿ(ℝ^P)` is finite-dimensional, and an `n`-vector vanishing on a basis `b₁, …, b_N` is zero. -/
theorem Submission.lpf_rsn_covector_separating_family : ∀ (P n : ℕ), ∃ (N : ℕ) (b : Fin N → Covector (Eucl P) n), ∀ w : NVector (Eucl P) n, (∀ i, w (b i) = 0) → w = 0 := by
  intro P n
  -- Step 1: evaluation on `n`-tuples of standard basis vectors of `ℝ^P` is linear.
  let e : Module.Basis (Fin P) ℝ (Eucl P) := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  let Φ : Covector (Eucl P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α r => α (fun i => e (r i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Step 2: `Φ` is injective, as a multilinear map is determined by its values on basis vectors.
  have hΦ : Function.Injective Φ := by
    intro α β h
    have hm : α.toContinuousMultilinearMap.toMultilinearMap =
        β.toContinuousMultilinearMap.toMultilinearMap :=
      Module.Basis.ext_multilinear (fun _ => e) (fun r => congrFun h r)
    ext v
    exact congrArg (fun m : MultilinearMap ℝ (fun _ : Fin n => Eucl P) ℝ => m v) hm
  -- Step 3: hence `Λⁿ(ℝ^P)` is finite-dimensional; take a basis `b₁, …, b_N`.
  have : FiniteDimensional ℝ (Covector (Eucl P) n) := FiniteDimensional.of_injective Φ hΦ
  let b := Module.finBasis ℝ (Covector (Eucl P) n)
  refine ⟨Module.finrank ℝ (Covector (Eucl P) n), b, ?_⟩
  -- Step 4: a linear functional vanishing on a basis is zero.
  intro w hw
  have hlin : (w : Covector (Eucl P) n →ₗ[ℝ] ℝ) = 0 := b.ext (fun i => by simpa using hw i)
  ext α
  simpa using congrArg (fun l : Covector (Eucl P) n →ₗ[ℝ] ℝ => l α) hlin
/-- **Fundamental lemma of the calculus of variations with a positive weight** (a step of the
proof that a rectifiable `τ(M, θ, ξ)` lives on its support, Simon Ch. 6, 3.9).  If `θ > 0` on `M`,
`θ` is `μ`-integrable on `M ∩ W` with `W` open, `g` is a.e.-strongly measurable and a.e. bounded
for `μ ⌞ M`, and `∫_M θ φ g dμ = 0` for every smooth compactly supported `φ` with
`tsupport φ ⊆ W`, then `g = 0` `μ ⌞ M`-a.e. on `W`.  Mathlib's fundamental lemma applied to `θ g`,
which is integrable on `W` for `μ ⌞ M`, gives `θ g = 0` there; divide by `θ`. -/
theorem Submission.lpf_rsn_weighted_fundamental_lemma : ∀ (P : ℕ) (μ : Measure (Eucl P)) (M W : Set (Eucl P)) (θ g : Eucl P → ℝ) (C : ℝ), IsOpen W → NullMeasurableSet M μ → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) μ → AEStronglyMeasurable g (μ.restrict M) → (∀ᵐ x ∂(μ.restrict M), |g x| ≤ C) → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W → ∫ x in M, θ x * (φ x * g x) ∂μ = 0) → ∀ᵐ x ∂(μ.restrict M), x ∈ W → g x = 0 := by
  intro P μ M W θ g C hW hM hpos hθ hg hgC hint
  -- Step 1: `θ g` is integrable on `W` for `μ ⌞ M`, as `(μ ⌞ M) ⌞ W = μ ⌞ (M ∩ W)`.
  have hfint : IntegrableOn (fun x => θ x * g x) W (μ.restrict M) := by
    rw [IntegrableOn, Measure.restrict_restrict hW.measurableSet, Set.inter_comm]
    have hθ' : Integrable θ (μ.restrict (M ∩ W)) := hθ
    have hg' : AEStronglyMeasurable g (μ.restrict (M ∩ W)) :=
      hg.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hgC' : ∀ᵐ x ∂(μ.restrict (M ∩ W)), ‖g x‖ ≤ C := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hgC] with x hx
      simpa [Real.norm_eq_abs] using hx
    exact hθ'.mul_bdd hg' hgC'
  -- Steps 2–3: the tests `∫ φ • (θ g) d(μ ⌞ M)` vanish, so `θ g = 0` `μ ⌞ M`-a.e. on `W`.
  have hzero := hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint.locallyIntegrableOn
    (fun φ hφ hφc hφW => by
      rw [← hint φ hφ hφc hφW]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring)
  -- Step 4: `μ ⌞ M`-a.e. point lies in `M`, where `θ > 0`.
  filter_upwards [hzero, ae_restrict_mem₀ hM] with x hx hxM hxW
  rcases mul_eq_zero.mp (hx hxW) with h | h
  · exact absurd h (hpos x hxM).ne'
  · exact h

/-- **A representation is null where the current vanishes (steps 5–8 of (P2) in Simon Ch. 6,
Lemma 3.9).**  If `T = τ(M, θ, ξ)` with `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`, `T` vanishes on the open set
`W ⊆ U` and `θ` is integrable on `M ∩ W`, then `Hⁿ(M ∩ W) = 0`.  Testing `T` with `φ α`
(`φ ∈ C_c^∞(W)`, `α` an `n`-covector) gives `∫_M θ φ ⟨α, ξ⟩ dHⁿ = 0`, so `⟨α, ξ⟩ = 0` a.e. on
`M ∩ W` (`lpf_rsn_weighted_fundamental_lemma`).  Finitely many covectors separate `n`-vectors
(`lpf_rsn_covector_separating_family`), so `ξ = 0` a.e. on `M ∩ W`; as `‖ξ‖ = 1` a.e. on `M`,
the set `M ∩ W` is null. -/
theorem Submission.lpf_rsn_local_null : ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsOpen W → W ⊆ U → T.VanishesOn W → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) (μHE[n] : Measure (Eucl P)) → AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ = 1) → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M ∩ W) = 0 := by
  intro P n U W T M θ ξ hW hWU hvan hM hpos hθ hξm hξ1 hrep
  -- Each coordinate `x ↦ ξ x α` is bounded by `‖α‖` and vanishes a.e. on `M ∩ W`.
  have key : ∀ α : Covector (Eucl P) n,
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ W → ξ x α = 0 := by
    intro α
    refine Submission.lpf_rsn_weighted_fundamental_lemma P (μHE[n] : Measure (Eucl P)) M W θ
      (fun x => ξ x α) ‖α‖ hW hM hpos hθ ?_ ?_ ?_
    · exact (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable hξm
    · filter_upwards [hξ1] with x hx
      calc |ξ x α| = ‖ξ x α‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ξ x‖ * ‖α‖ := (ξ x).le_opNorm α
        _ = ‖α‖ := by rw [hx, one_mul]
    · -- `ω = φ α` is a test form supported in `W`, so `T ω = 0`.
      intro φ hφ hφc hφW
      let ω : DifferentialForm (Eucl P) n := fun x => φ x • α
      have hωs : IsSmoothForm ω := hφ.smul contDiff_const
      have hωc : HasCompactSupport ω := hφc.smul_right
      have hωW : tsupport ω ⊆ W := (tsupport_smul_subset_left φ (fun _ => α)).trans hφW
      let ωU : TestFormOn U n := ⟨ω, ⟨hωs, hωc⟩, hωW.trans hWU⟩
      have h0 : T ωU = 0 := hvan ωU hωW
      rw [hrep ωU] at h0
      simpa [tauAction, ωU, ω, map_smul, smul_eq_mul] using h0
  -- A finite separating family of covectors gives `ξ = 0` a.e. on `M ∩ W`, where `‖ξ‖ = 1`.
  obtain ⟨N, b, hb⟩ := Submission.lpf_rsn_covector_separating_family P n
  have hall : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ i, x ∈ W → ξ x (b i) = 0 :=
    ae_all_iff.mpr fun i => key (b i)
  have hnotW : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∉ W := by
    filter_upwards [hall, hξ1] with x hx h1 hxW
    rw [hb (ξ x) fun i => hx i hxW, ContinuousLinearMap.opNorm_zero] at h1
    exact zero_ne_one h1
  have hres : (μHE[n] : Measure (Eucl P)).restrict M W = 0 := by
    rw [ae_iff] at hnotW
    simpa using hnotW
  rwa [Measure.restrict_apply hW.measurableSet, Set.inter_comm] at hres
/-- **Simple `n`-vectors (step (P1) of Simon Ch. 6, Lemma 3.9).**  The operator norm of
`v₁ ∧ ⋯ ∧ vₙ = simpleNVector v` is the square root of the Gram determinant `det (⟪vᵢ, vⱼ⟫)`, and a
change of frame `τ ↦ Bτ` multiplies `simpleNVector τ` by `det B`.  The second identity is the
uniqueness of alternating forms on `ℝⁿ` (`AlternatingMap.eq_smul_basis_det`).  A dependent `v`
makes both sides of the first vanish.  An independent `v` is `Bτ` for an orthonormal basis `τ` of
`span v`, so `G(v) = B Bᵀ`; `|α τ| ≤ ‖α‖` and the covector `u ↦ det (⟪τᵢ, uⱼ⟫)` (norm `≤ 1` by
Hadamard's and Bessel's inequalities, value `1` at `τ`) give `‖simpleNVector v‖ = |det B|`. -/
theorem Submission.lpf_simple_nvector_algebra : (∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
  -- Change of frame: `α(Bτ) = det B · α(τ)` for every `n`-covector `α`, since
  -- `B ↦ α(Bτ)` is alternating in the rows of `B` (`AlternatingMap.eq_smul_basis_det`).
  have hframe : ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
      simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
    intro P n B τ
    ext α
    simp only [simpleNVector_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    set f : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ :=
      α.toAlternatingMap.compLinearMap (Fintype.linearCombination ℝ τ) with hf
    have h1 : f (fun i j => B i j) = α (fun i => ∑ j, B i j • τ j) := by
      simp [hf, Fintype.linearCombination_apply]
    have h2 : f (Pi.basisFun ℝ (Fin n)) = α τ := by
      simp [hf, Fintype.linearCombination_apply_single]
    rw [← h1, AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) f,
      AlternatingMap.smul_apply, h2, Pi.basisFun_det, smul_eq_mul, mul_comm]
    rfl
  refine ⟨fun P n v => ?_, hframe⟩
  by_cases hv : LinearIndependent ℝ v
  · -- Independent family: `v = Bτ` for an orthonormal basis `τ` of `W = span v`,
    -- `B i j = ⟪v i, τ j⟫`, so `G(v) = B Bᵀ` and `simpleNVector v = det B • simpleNVector τ`.
    set W := Submodule.span ℝ (Set.range v) with hW_def
    have hW : Module.finrank ℝ W = n := by rw [finrank_span_eq_card hv, Fintype.card_fin]
    set b : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
    set τ : Fin n → Eucl P := fun j => (b j : Eucl P) with hτ_def
    have hτ : Orthonormal ℝ τ := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hvW : ∀ i, v i ∈ W := fun i => Submodule.subset_span (Set.mem_range_self i)
    set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => inner ℝ (v i) (τ j) with hB_def
    have hvB : (fun i => ∑ j, B i j • τ j) = v := by
      funext i
      have h := congrArg Subtype.val (b.sum_repr' ⟨v i, hvW i⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
      simpa [hB_def, hτ_def, real_inner_comm] using h
    have hgram : (Matrix.of fun i j => inner ℝ (v i) (v j)) = B * B.transpose := by
      ext i k
      have h := b.sum_inner_mul_inner ⟨v i, hvW i⟩ ⟨v k, hvW k⟩
      simp only [Submodule.coe_inner] at h
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hB_def]
      rw [← h]
      simp [hτ_def, real_inner_comm]
    have hsv : ∀ α : Covector (Eucl P) n, simpleNVector v α = B.det * α τ := by
      intro α
      rw [← hvB, hframe]
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, simpleNVector_apply]
    -- Upper bound: `|α τ| ≤ ‖α‖ ∏ ‖τ i‖ = ‖α‖`.
    have hup : ∀ α : Covector (Eucl P) n, |α τ| ≤ ‖α‖ := by
      intro α
      have h := α.le_opNorm τ
      simp only [hτ.1, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    -- Lower bound: the calibrating covector `α₀(u) = det (⟪τ i, u j⟫)` has `α₀ τ = 1` and
    -- `‖α₀‖ ≤ 1` by Hadamard's inequality for the columns `c j = (⟪τ i, u j⟫)ᵢ` together with
    -- Bessel's inequality `‖c j‖ ≤ ‖u j‖`.
    set α₀ : Covector (Eucl P) n := wedgeCovectors n fun i => innerSL ℝ (τ i) with hα₀_def
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀_def, wedgeCovectors_apply_det]
      have h : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) = 1 := by
        ext i j
        simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
      rw [h, Matrix.det_one]
    have hα₀ : ‖α₀‖ ≤ 1 := by
      refine ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one fun u => ?_
      rw [one_mul, hα₀_def, wedgeCovectors_apply_det, Real.norm_eq_abs]
      set c : Fin n → EuclideanSpace ℝ (Fin n) :=
        fun j => WithLp.toLp 2 fun i => inner ℝ (τ i) (u j) with hc
      set e := EuclideanSpace.basisFun (Fin n) ℝ
      have hdet : (Matrix.of fun i j => innerSL ℝ (τ i) (u j)).det = e.toBasis.det c := by
        rw [Module.Basis.det_apply]
        congr 1
      have hHad : |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := by
        have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
          ⟨finrank_euclideanSpace_fin⟩
        rw [← e.toBasis.orientation.volumeForm_robust' e c]
        exact e.toBasis.orientation.abs_volumeForm_apply_le c
      have hBessel : ∀ j, ‖c j‖ ≤ ‖u j‖ := by
        intro j
        rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (u j))]
        apply Real.sqrt_le_sqrt
        simpa [hc] using hτ.sum_inner_products_le (u j) (s := Finset.univ)
      rw [hdet]
      calc |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := hHad
        _ ≤ ∏ j, ‖u j‖ := by gcongr with j; exact hBessel j
    -- Hence `‖simpleNVector v‖ = |det B|`.
    have hnorm : ‖simpleNVector v‖ = |B.det| := by
      apply le_antisymm
      · refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun α => ?_
        rw [hsv, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hup α) (abs_nonneg _)
      · calc |B.det| = ‖simpleNVector v α₀‖ := by rw [hsv, hα₀τ, mul_one, Real.norm_eq_abs]
          _ ≤ ‖simpleNVector v‖ * ‖α₀‖ := (simpleNVector v).le_opNorm α₀
          _ ≤ ‖simpleNVector v‖ * 1 :=
            mul_le_mul_of_nonneg_left hα₀ (ContinuousLinearMap.opNorm_nonneg _)
          _ = ‖simpleNVector v‖ := mul_one _
    rw [hnorm, hgram, Matrix.det_mul, Matrix.det_transpose, sq_abs, sq]
  · -- Dependent family: every alternating map vanishes on `v`, and `G(v) g = 0` for a
    -- nontrivial relation `∑ g j • v j = 0`, so both sides vanish.
    have h0 : ‖simpleNVector v‖ = 0 := by
      refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun α => ?_)
        (ContinuousLinearMap.opNorm_nonneg _)
      have hα : α v = 0 := α.toAlternatingMap.map_linearDependent v hv
      rw [simpleNVector_apply, hα, norm_zero, zero_mul]
    obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hv
    have hdet : (Matrix.of fun i j => inner ℝ (v i) (v j)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨g, fun h => hi₀ (congrFun h i₀), ?_⟩
      funext i
      have h := congrArg (inner ℝ (v i)) hg
      simp only [inner_sum, inner_smul_right, inner_zero_right] at h
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
    rw [h0, hdet, sq, mul_zero]

/-- **A rectifiable representation lives on the support (step (P2) of Simon Ch. 6, Lemma 3.9).**
If `T = τ(M, θ, ξ)` then `Hⁿ(M \ spt T) = 0`.  An orthonormal frame `τ` has Gram matrix `1`, so
`‖simpleNVector τ‖ = 1` by `lpf_simple_nvector_algebra` and `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`
(`orients`).  Hence `Hⁿ(M ∩ W) = 0` for every open `W ⊂⊂ U` on which `T` vanishes
(`lpf_rsn_local_null`), and countably many such `W` cover the zero region of `T`
(`lpf_rsn_null_diff_support_of_local_null`). -/
theorem Submission.lpf_rectifiable_support_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := by
  intro P n U T M θ ξ hM hT
  -- Unit norm: `ξ x = ±simpleNVector τ` with `τ` orthonormal for `Hⁿ`-a.e. `x ∈ M`, and
  -- `‖simpleNVector τ‖ ^ 2 = det (⟪τᵢ, τⱼ⟫) = det 1 = 1`.
  have hξ : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ = 1 := by
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, -, hξx⟩ := hx
    have hgram : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = 1 := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
    have hτ1 : ‖simpleNVector τ‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (ContinuousLinearMap.opNorm_nonneg _) two_ne_zero).mp ?_
      rw [Submission.lpf_simple_nvector_algebra.1, hgram, Matrix.det_one]
    rcases hξx with h | h
    · rw [h, hτ1]
    · rw [h, ContinuousLinearMap.opNorm_neg, hτ1]
  -- It suffices that `Hⁿ(M ∩ W) = 0` for each open `W ⊂⊂ U` on which `T` vanishes; there `θ` is
  -- integrable on `M ∩ W ⊆ M ∩ closure W`.
  refine Submission.lpf_rsn_null_diff_support_of_local_null P n U T M _ hM.subset
    fun W hW hWc hWU hTW => ?_
  exact Submission.lpf_rsn_local_null P n U W T M θ ξ hW (subset_closure.trans hWU) hTW
    hM.nullMeasurableSet hM.pos
    ((hM.integrableOn _ hWc hWU).mono_set (Set.inter_subset_inter_right M subset_closure))
    hM.aestronglyMeasurable hξ hT
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the
proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to
`Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets, `V ∋ x` open.  If `B_δ(x) ⊆ V` and
`f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off
`W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and
`(M', θ')` agree for all small `r`. -/
theorem Submission.br_weightedTangent_congr :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P) (V : Set (Eucl P)),
      IsOpen V → x ∈ V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ y = θ' y) → θ x = θ' x →
      ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k M' θ' x L := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k M M' θ θ' x V hV hxV hMM' hθθ' hθx L hL
  -- `η_r(y) = r⁻¹ (y - x)` maps `Hᵏ`-null sets to `Hᵏ`-null sets: `Hᵏ(η_r Z) = r⁻ᵏ Hᵏ(Z)`.
  have hnull : ∀ r : ℝ, r ≠ 0 → ∀ Z : Set (Eucl P), (μHE[k] : Measure (Eucl P)) Z = 0 →
      (μHE[k] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- A measurable `N ⊇ {θ ≠ θ'}` with `Hᵏ(N ∩ M ∩ V) = 0`.
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hθθ')
  rw [Measure.restrict_apply hNmeas] at hN0
  refine ⟨hL.1, fun f => ?_⟩
  rw [← hθx]
  refine (hL.2 f).congr' ?_
  -- `f = 0` off `B_R(0)` and `B_δ(x) ⊆ V`; the blow-up integrals agree for `0 < r < δ / R`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hcont : Continuous fun y : Eucl P => x + r • y :=
    continuous_const.add (continuous_const_smul r)
  -- `W = η_r(V)` is open and the integrands `f(y) g(x + r y)` vanish off `W`.
  set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' V with hW
  have hWmeas : MeasurableSet W := (hV.preimage hcont).measurableSet
  have hvan : ∀ g : Eucl P → ℝ, ∀ y, y ∉ W → f y * g (x + r • y) = 0 := by
    intro g y hy
    have hfy : f y = 0 := by
      apply hfR
      have h1 : x + r • y ∉ ball x δ := fun h => hy (hδV h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, not_lt] at h1
      rw [lt_div_iff₀ hR] at hrR
      exact le_of_lt (lt_of_mul_lt_mul_left (hrR.trans_le h1) hr0.le)
    rw [hfy, zero_mul]
  -- Cutting by `W`: `∫_{η_r(S)} = ∫_{W ∩ η_r(S)}`.
  have hcut : ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ y in W ∩ blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
    intro S g
    rw [← Measure.restrict_restrict hWmeas,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan g)]
  -- `W ∩ η_r(M) = W ∩ η_r(M')` up to the null set `η_r((M ∆ M') ∩ V)`.
  have hset : W ∩ blowUpMap x r '' M =ᵐ[(μHE[k] : Measure (Eucl P))] W ∩ blowUpMap x r '' M' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inl ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inr ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
  -- `θ(x + r y) = θ'(x + r y)` a.e. on `W ∩ η_r(M)`, off the null set `η_r(N ∩ M ∩ V)`.
  have hae : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (W ∩ blowUpMap x r '' M)),
      f y * θ (x + r • y) = f y * θ' (x + r • y) := by
    have hN'meas : MeasurableSet ((fun y => x + r • y) ⁻¹' N) :=
      hNmeas.preimage hcont.measurable
    rw [ae_iff]
    refine measure_mono_null (t := (fun y => x + r • y) ⁻¹' N) ?_ ?_
    · intro y hy
      by_contra hyN
      apply hy
      have hθy : θ (x + r • y) = θ' (x + r • y) := by
        by_contra hne
        exact hyN (hNsub hne)
      rw [hθy]
    · rw [Measure.restrict_apply hN'meas]
      refine measure_mono_null ?_ (hnull r hr0.ne' _ hN0)
      rintro y ⟨hyN, hyW, z, hzM, rfl⟩
      refine ⟨z, ⟨?_, hzM, ?_⟩, rfl⟩
      · simpa [hinv r hr0.ne' z] using hyN
      · simpa [hW, hinv r hr0.ne' z] using hyW
  calc ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P))
      = ∫ y in W ∩ blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        hcut M θ
    _ = ∫ y in W ∩ blowUpMap x r '' M, f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        integral_congr_ae hae
    _ = ∫ y in W ∩ blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
        rw [Measure.restrict_congr_set hset]
    _ = ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        (hcut M' θ').symm

/-- **Cut-off of a finite-mass current (Simon Ch. 6, 2.1, 2.4).**  If `χ` is smooth with
`tsupport χ ⊆ U` and `|χ| ≤ 1`, and `X ∈ 𝒟_q(U)` has `M(X) < ∞`, then `Y(ω) = X(χ ω)` is a
current in `ℝ^P`.  If `ω_j → 0` in `𝒟^q(ℝ^P)`, eventually `|χ ω_j(x)| ≤ |ω_j(x)| ≤ δ` for every
`x` (`Submission.fiw_ims_sc_converges_zero_small`), so `|Y(ω_j)| ≤ δ · M(X)` by
`Submission.br_la_abs_apply_le_mul_mass`. -/
theorem Submission.fiw_tb_ext_cutoff_current : ∀ (P q : ℕ) (U : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ U → (∀ x, |χ x| ≤ 1) → ∀ X : GeometricCurrentOn U q, X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) q, ∀ (ω : TestFormOn (univ : Set (Eucl P)) q) (η : TestFormOn U q), (∀ x, (η : DifferentialForm (Eucl P) q) x = χ x • (ω : DifferentialForm (Eucl P) q) x) → Y ω = X η := by
  intro P q U χ hχ hχU hχ1 X hX
  -- `L ω = χ ω` is a linear map `𝒟^q(ℝ^P) → 𝒟^q(U)`, and `Y = X ∘ L`.
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q (univ : Set (Eucl P)) U χ hχ hχU
  refine ⟨⟨X.toCurrent.comp L, ?_⟩, ?_⟩
  · intro ωs hωs
    obtain ⟨_, -, -, -, hsmall⟩ := Submission.fiw_ims_sc_converges_zero_small P q univ ωs hωs
    rw [Metric.tendsto_atTop]
    intro ε hε
    set μX := X.mass.toReal
    have hμ0 : 0 ≤ μX := ENNReal.toReal_nonneg
    have hδ : 0 < ε / (μX + 1) := by positivity
    -- Eventually `|ω_j(x)| ≤ δ := ε / (M(X) + 1)` for every `x`.
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hsmall (ε / (μX + 1)) hδ)
    refine ⟨j₀, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero]
    -- Then `|χ ω_j(x)| = |χ(x)| |ω_j(x)| ≤ δ`, as `|χ| ≤ 1`.
    have hbound : ∀ x, covectorEuclideanNorm
        ((L (ωs j) : DifferentialForm (Eucl P) q) x) ≤ ε / (μX + 1) := by
      intro x
      rw [hL, Submission.fiw_tb_ext_covectorNorm_smul]
      calc |χ x| * covectorEuclideanNorm ((ωs j : DifferentialForm (Eucl P) q) x)
          ≤ 1 * (ε / (μX + 1)) :=
            mul_le_mul (hχ1 x) (hj₀ j hj x) (covectorEuclideanNorm_nonneg _) zero_le_one
        _ = ε / (μX + 1) := one_mul _
    -- The mass estimate gives `|Y(ω_j)| ≤ δ · M(X) < ε`.
    have hY := Submission.br_la_abs_apply_le_mul_mass P q U X (L (ωs j)) _ hδ hbound hX
    change |X (L (ωs j))| < ε
    calc |X (L (ωs j))| ≤ ε / (μX + 1) * μX := hY
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  · -- `L ω = η` whenever `η = χ ω` pointwise.
    intro ω η hη
    change X (L ω) = X η
    congr 1
    exact Subtype.ext (funext fun x => by rw [hL, hη])

/-- **Mass does not drop under restriction near the support (Simon Ch. 6, 2.4–2.5).**  If
`Z ∈ 𝒟_q(ℝ^P)` vanishes on every test form whose support misses a compact `K ⊆ U` (`U` open),
then `M(Z) ≤ M(Z|_U)` for `Z|_U = Z.restrictDomain`.  With a cutoff `χ` (`0 ≤ χ ≤ 1`,
`tsupport χ ⊆ U`, `χ = 1` on an open `N ⊇ K`), every `ω` admissible for `M(Z)` gives the form
`χ ω ∈ 𝒟^q(U)`, admissible for `M(Z|_U)` as `|χ ω| = χ |ω| ≤ 1`, and `χ ω = ω` on `N`, so
`Z(ω) = Z(χ ω) = Z|_U(χ ω) ≤ M(Z|_U)`. -/
theorem Submission.fiw_tb_ext_mass_le_restrictDomain : ∀ (P q : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) q, (∀ ω : TestFormOn (univ : Set (Eucl P)) q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → Z.mass ≤ (Z.restrictDomain (subset_univ U)).mass := by
  intro P q U K hU hK hKU Z hZ
  obtain ⟨χ, N, hχ, hχ01, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  -- `L ω = χ ω`, a test form in `U`.
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q univ U χ hχ hχU
  -- `M(Z)` is the supremum of `Z(ω)` over the admissible `ω`.
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  have hadm : L ω ∈ massAdmissibleOn U q U := by
    refine ⟨(L ω).property.2, fun x => ?_⟩
    rw [hL, Submission.fiw_tb_ext_covectorNorm_smul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hω.2 x)
  -- `L ω = ω` on `N ⊇ K`, so `Z` cannot tell them apart.
  have hval : Z ω = Z.restrictDomain (subset_univ U) (L ω) := by
    rw [GeometricCurrentOn.restrictDomain_apply]
    refine (Submission.fiw_tb_ext_apply_eq_of_eqOn P q univ K N Z hN hKN hZ ω
      (testFormOnInclusion (subset_univ U) q (L ω)) fun x hx => ?_).symm
    rw [testFormOnInclusion_coe, hL, hχN x hx, one_smul]
  show ENNReal.ofReal (Z ω) ≤ _
  rw [hval]
  exact (Z.restrictDomain (subset_univ U)).le_massOn hadm
/-- **Integrality of the extension (Lemma B of the extension step in the proof of Simon Ch. 6,
Theorem 7.2).**  Let `U` be open, `K ⊆ U` compact and `Z ∈ 𝒟_q(ℝ^P)` vanish on test forms whose
support misses `K`.  If `Z|_U = τ(M, θ, ξ)` is integer multiplicity in `U`, then
`Z = τ(M ∩ K, θ, ξ)` is integer multiplicity in `ℝ^P`.  As `spt Z|_U ⊆ K`
(`fiw_tb_ext_support_subset`), `H^q(M ∖ K) = 0` (`lpf_rectifiable_support_null`), so
`(M ∩ K, θ, ξ)` is a rectifiable triple whose tangent spaces are those of `(M, θ)`
(`br_weightedTangent_congr`).  For `χ ∈ C_c^∞(U)` with `χ = 1` on an open `N ⊇ K`
(`fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`),
`Z(ω) = Z|_U(χ ω) = ∫_M θ ⟨χ ω, ξ⟩ dH^q = ∫_{M ∩ K} θ ⟨ω, ξ⟩ dH^q`. -/
theorem Submission.fiw_tb_ext_isIntegerMultiplicity : ∀ (P q : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) q, (∀ ω : TestFormOn (univ : Set (Eucl P)) q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → IsIntegerMultiplicity (Z.restrictDomain (subset_univ U)) → IsIntegerMultiplicity Z := by
  intro P q U K hU hK hKU Z hZ hIM
  obtain ⟨M, θ, ξ, htri, hθN, hrep⟩ := hIM
  -- (B1) `Z|_U` vanishes on test forms supported away from `K`, so `spt Z|_U ⊆ K`.
  have hZUv : ∀ ω : TestFormOn U q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K →
      (Z.restrictDomain (subset_univ U)) ω = 0 := fun ω hω => hZ _ hω
  have hsptU : (Z.restrictDomain (subset_univ U)).support ⊆ K :=
    Submission.fiw_tb_ext_support_subset P q U K _ hU hK.isClosed hZUv
  -- (B2) `H^q(M ∖ K) = 0`, hence `H^q ⌞ (M ∩ K) = H^q ⌞ M` and `H^q(M ∆ (M ∩ K)) = 0`.
  have hnull : (μHE[q] : Measure (Eucl P)) (M \ K) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hsptU)
      (Submission.lpf_rectifiable_support_null P q U _ M θ ξ htri hrep)
  have hae : (M ∩ K : Set (Eucl P)) =ᵐ[(μHE[q] : Measure (Eucl P))] M := by
    rw [ae_eq_set]
    constructor
    · exact measure_mono_null (fun x hx => (hx.2 hx.1.1).elim) measure_empty
    · simpa [sdiff_inter_self_eq_sdiff] using hnull
  have hrestr : (μHE[q] : Measure (Eucl P)).restrict (M ∩ K) =
      (μHE[q] : Measure (Eucl P)).restrict M := Measure.restrict_congr_set hae
  have hsymm : (μHE[q] : Measure (Eucl P)) (symmDiff M (M ∩ K) ∩ univ) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hnull
    rcases hx.1 with ⟨hxM, hxMK⟩ | ⟨hxMK, hxM⟩
    · exact ⟨hxM, fun hxK => hxMK ⟨hxM, hxK⟩⟩
    · exact absurd hxMK.1 hxM
  -- (B3)–(B4) `(M ∩ K, θ, ξ)` is a rectifiable triple in `ℝ^P`: `θ` is integrable on `M ∩ K`
  -- as `K ⊆ U` is compact, and the frames `τ` of `(M, θ)` still orient `(M ∩ K, θ)`.
  have htri' : IsRectifiableTriple (univ : Set (Eucl P)) q (M ∩ K) θ ξ :=
    { subset := subset_univ _
      nullMeasurableSet := htri.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
      countablyRectifiable := htri.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => htri.pos x hx.1
      integrableOn := fun K'' _ _ =>
        (htri.integrableOn K hK hKU).mono_set inter_subset_left
      aestronglyMeasurable := by rw [hrestr]; exact htri.aestronglyMeasurable
      orients := by
        rw [hrestr]
        filter_upwards [htri.orients] with x hx
        obtain ⟨τ, hτ, htan, hξ⟩ := hx
        exact ⟨τ, hτ, Submission.br_weightedTangent_congr P q M (M ∩ K) θ θ x univ isOpen_univ
          (mem_univ x) hsymm (ae_of_all _ fun _ => rfl) rfl _ htan, hξ⟩ }
  refine ⟨M ∩ K, θ, ξ, htri', fun x hx => hθN x hx.1, fun ω => ?_⟩
  -- (B5) A cutoff `χ ∈ C_c^∞(U)` with `χ = 1` on an open `N ⊇ K`; `Z(ω) = Z(χ ω)` as `χ ω = ω`
  -- on `N`, and `χ = 1` on `M ∩ K`.
  obtain ⟨χ, N, hχs, -, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q (univ : Set (Eucl P)) U χ hχs hχU
  have h1 : Z ω = Z (testFormOnInclusion (subset_univ U) q (L ω)) :=
    (Submission.fiw_tb_ext_apply_eq_of_eqOn P q univ K N Z hN hKN hZ ω _ (fun x hx => by
      change (L ω : DifferentialForm (Eucl P) q) x = _
      rw [hL, hχN x hx, one_smul])).symm
  rw [h1, ← GeometricCurrentOn.restrictDomain_apply, hrep]
  unfold tauAction
  rw [← hrestr]
  apply setIntegral_congr_fun₀ htri'.nullMeasurableSet
  intro x hx
  change θ x * ξ x ((L ω : DifferentialForm (Eucl P) q) x) = _
  rw [hL, hχN x (hKN hx.2), one_smul]
/-- Integer `L¹` density of a top-dimensional integer multiplicity current (Simon Ch. 6, proof
of 5.1, (27)–(28)).  Let `X ∈ 𝒟ₙ(ℝⁿ)` be integer multiplicity with `M(X) < ∞` such that (H) every
representation `X = τ(M, θ, ξ)` has `M(X) = ∫_M θ dHⁿ` and `Hⁿ(M ∖ spt X) = 0`.  Then
`X(ω) = ∫ u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` for a Borel integer-valued `u ∈ L¹(ℝⁿ)` with `∫ |u| = M(X)` and
`u = 0` a.e. off `spt X`.  With `Δ = dx¹ ∧ ⋯ ∧ dxⁿ`, every `n`-covector is `α = α(e) Δ` and
`Δ(τ) = ±1` for orthonormal `τ`, so `⟨ω, ξ⟩ = ω_e s` with `s = ⟨Δ, ξ⟩ = ±1` `Hⁿ`-a.e. on `M`;
`u` is a Borel integer-valued version of `1_{M'} θ s`, `M' ⊆ M` a measurable core of `M`. -/
theorem Submission.fiw_tb_tda_density : ∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → (∀ (M : Set (Eucl (m + 1))) (θ : Eucl (m + 1) → ℝ) (ξ : Eucl (m + 1) → NVector (Eucl (m + 1)) (m + 1)), IsRectifiableTriple (univ : Set (Eucl (m + 1))) (m + 1) M θ ξ → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = tauAction (m + 1) M θ ξ ω) → X.mass = ∫⁻ x in M, ENNReal.ofReal (θ x) ∂(μHE[m + 1] : Measure (Eucl (m + 1))) ∧ (μHE[m + 1] : Measure (Eucl (m + 1))) (M \ X.support) = 0) → ∃ u : Eucl (m + 1) → ℝ, Measurable u ∧ (∀ x, ∃ k : ℤ, u x = k) ∧ Integrable u ∧ ∫⁻ x, ENNReal.ofReal |u x| = X.mass ∧ (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∉ X.support → u x = 0) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  classical
  intro m X hX hXm hH
  let _ : MeasureSpace (Eucl (m + 1)) := measureSpaceOfInnerProductSpace
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  -- Step 1: the integer multiplicity triple, with (H) giving `M(X) = ∫_M θ` and
  -- `Hⁿ(M ∖ spt X) = 0`.
  obtain ⟨M, θ, ξ, hT, hθ, hXT⟩ := hX
  obtain ⟨hmass, hsupp⟩ := hH M θ ξ hT hXT
  -- Step 2: a measurable core `M' ⊆ M` with `M' = M` a.e.
  obtain ⟨M', hM'M, hM'm, hM'ae⟩ :=
    (hvol ▸ hT.nullMeasurableSet : NullMeasurableSet M volume).exists_measurable_subset_ae_eq
  have hrM : volume.restrict M' = volume.restrict M := Measure.restrict_congr_set hM'ae
  -- Step 3: the determinant covector `Δ = dx¹ ∧ ⋯ ∧ dxⁿ`: every `n`-covector is `α(e) Δ`, and
  -- `Δ(τ) = ±1` for orthonormal `τ`.
  obtain ⟨Δ, hΔ, hΔτ⟩ : ∃ Δ : Covector (Eucl (m + 1)) (m + 1),
      (∀ (α : Covector (Eucl (m + 1)) (m + 1)) v,
        α v = α (fun i => EuclideanSpace.single i (1 : ℝ)) * Δ v) ∧
      ∀ τ : Fin (m + 1) → Eucl (m + 1), Orthonormal ℝ τ → Δ τ = 1 ∨ Δ τ = -1 := by
    have hdet : ∀ v, wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j) v =
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.det v := by
      intro v
      rw [wedgeCovectors_apply_det, Module.Basis.det_apply]
      congr 1
    have hb : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis =
        fun i => EuclideanSpace.single i (1 : ℝ) := by
      funext i; simp
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), fun α v => ?_,
      fun τ hτ => ?_⟩
    · have := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis α.toAlternatingMap)
      simp only [AlternatingMap.smul_apply, ContinuousAlternatingMap.coe_toAlternatingMap,
        smul_eq_mul, hb] at this
      rw [hdet]; exact this
    · rw [hdet]
      have hsp := hτ.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
      have := OrthonormalBasis.det_to_matrix_orthonormalBasis_real
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (OrthonormalBasis.mk hτ hsp.ge)
      rwa [OrthonormalBasis.coe_mk] at this
  -- Step 4: `s = ξ(·)(Δ) = ±1` a.e. on `M`.
  have hor : ∀ᵐ x ∂(volume.restrict M'), ξ x Δ = 1 ∨ ξ x Δ = -1 := by
    have h := hT.orients
    rw [hvol, ← hrM] at h
    filter_upwards [h] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    rcases hξ with h | h <;> rw [h]
    · exact hΔτ τ hτ
    · rcases hΔτ τ hτ with h' | h' <;> simp [h']
  -- Step 5: measurability of `θ`, `s` and `u₀ = 1_{M'} θ s`.
  have hθm : AEStronglyMeasurable θ (volume.restrict M') := by
    have hU : M' = ⋃ k : ℕ, M' ∩ closedBall 0 k := by
      rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
    rw [hU, aestronglyMeasurable_iUnion_iff]
    intro k
    have h := hT.integrableOn _ (isCompact_closedBall 0 k) (subset_univ _)
    rw [hvol] at h
    exact (h.mono_set (inter_subset_inter_left _ hM'M)).1
  have hsm : AEStronglyMeasurable (fun x => ξ x Δ) (volume.restrict M') := by
    have h := hT.aestronglyMeasurable
    rw [hvol, ← hrM] at h
    exact (ContinuousLinearMap.apply ℝ ℝ Δ).continuous.comp_aestronglyMeasurable h
  have hu₀m : AEStronglyMeasurable (M'.indicator (fun x => θ x * ξ x Δ)) volume :=
    (aestronglyMeasurable_indicator_iff hM'm).2 (hθm.mul hsm)
  -- Step 6: `u₀` is integer valued a.e.
  have hu₀Z : ∀ᵐ x ∂volume, M'.indicator (fun x => θ x * ξ x Δ) x ∈
      Set.range (Int.cast : ℤ → ℝ) := by
    filter_upwards [(ae_restrict_iff' hM'm).1 hor] with x hx
    by_cases hxM : x ∈ M'
    · rw [indicator_of_mem hxM]
      obtain ⟨k, hk⟩ := hθ x (hM'M hxM)
      rcases hx hxM with h1 | h1 <;> rw [h1, hk]
      · exact ⟨k, by simp⟩
      · exact ⟨-k, by simp⟩
    · rw [indicator_of_notMem hxM]; exact ⟨0, by simp⟩
  -- Step 7: the Borel integer-valued representative `u`.
  have hũm : Measurable (hu₀m.mk _) := hu₀m.stronglyMeasurable_mk.measurable
  obtain ⟨u, hu⟩ : ∃ u : Eucl (m + 1) → ℝ, u = fun x =>
      if hu₀m.mk _ x ∈ Set.range (Int.cast : ℤ → ℝ) then hu₀m.mk _ x else 0 := ⟨_, rfl⟩
  have hu_meas : Measurable u := by
    rw [hu]
    exact Measurable.ite (hũm (Set.countable_range _).measurableSet) hũm measurable_const
  have hu_Z : ∀ x, ∃ k : ℤ, u x = k := by
    intro x
    rw [hu]; dsimp only; split_ifs with h
    · obtain ⟨k, hk⟩ := h; exact ⟨k, hk.symm⟩
    · exact ⟨0, by simp⟩
  have hu_ae : u =ᵐ[volume] M'.indicator (fun x => θ x * ξ x Δ) := by
    filter_upwards [hu₀m.ae_eq_mk, hu₀Z] with x h1 h2
    rw [hu]; dsimp only; rw [← h1]; simp only [h2, ite_true]
  -- Step 8: `|u| = 1_{M'} θ` a.e., hence `∫ |u| = M(X)`.
  have habs : (fun x => ENNReal.ofReal |u x|) =ᵐ[volume]
      M'.indicator (fun x => ENNReal.ofReal (θ x)) := by
    filter_upwards [hu_ae, (ae_restrict_iff' hM'm).1 hor] with x h1 h2
    rw [h1]
    by_cases hxM : x ∈ M'
    · rw [indicator_of_mem hxM, indicator_of_mem hxM]
      rcases h2 hxM with h | h <;> rw [h]
      · rw [mul_one, abs_of_pos (hT.pos x (hM'M hxM))]
      · rw [mul_neg_one, abs_neg, abs_of_pos (hT.pos x (hM'M hxM))]
    · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, abs_zero, ENNReal.ofReal_zero]
  have hlint : ∫⁻ x, ENNReal.ofReal |u x| = X.mass := by
    rw [lintegral_congr_ae habs, lintegral_indicator hM'm, hrM, hmass, hvol]
  -- Step 9: integrability.
  have hu_int : Integrable u := by
    refine ⟨hu_meas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [hlint]
    exact hXm
  -- Step 10: `u = 0` a.e. off `spt X`.
  have hsupp' : ∀ᵐ x ∂volume, x ∉ X.support → u x = 0 := by
    have h0 : volume (M \ X.support) = 0 := hvol ▸ hsupp
    filter_upwards [hu_ae, measure_eq_zero_iff_ae_notMem.1 h0] with x hx1 hx2 hxs
    rw [hx1, indicator_of_notMem fun h => hx2 ⟨hM'M h, hxs⟩]
  refine ⟨u, hu_meas, hu_Z, hu_int, hlint, hsupp', fun ω => ?_⟩
  -- Step 11: the representation `X(ω) = ∫ u ω_e`, as `⟨ω, ξ⟩ = ω_e s` (Step 4).
  rw [hXT ω]
  unfold tauAction
  rw [hvol, ← hrM, ← integral_indicator hM'm]
  refine integral_congr_ae ?_
  filter_upwards [hu_ae] with x hx
  rw [hx]
  by_cases hxM : x ∈ M'
  · rw [indicator_of_mem hxM, indicator_of_mem hxM]
    have h : ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) =
        (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) * ξ x Δ := by
      rw [← smul_eq_mul, ← map_smul]; congr 1; ext v
      rw [hΔ ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) v]; rfl
    rw [h]; ring
  · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, zero_mul]
/-- An integer median of an integer-valued function on a set of positive finite measure (Simon
Ch. 6, proof of 5.1, (31): the choice of `β_F`).  With `A k = F ∩ {u ≤ k}`, `μ (A k)` increases
to `μ F = a` as `k → ∞` and decreases to `0` as `k → -∞` (continuity of `μ` from below and from
above), so there is a least integer `β` with `μ (A β) ≥ a/2`.  Then `μ (A (β - 1)) < a/2`, and since
`u` is integer-valued, `F ⊆ A (β - 1) ∪ (F ∩ {β ≤ u})`, which forces `μ (F ∩ {β ≤ u}) ≥ a/2`. -/
theorem Submission.fiw_tb_tda_im_median_exists :
    ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ),
      MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u →
      (∀ x, ∃ k : ℤ, u x = k) →
      ∃ β : ℤ, ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ β}) ∧
        ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | (β : ℝ) ≤ u x}) := by
  intro α _ μ F a u hF ha hμF hu hint
  -- Step 1: `A k = F ∩ {u ≤ k}` is measurable and monotone in `k`.
  set A : ℤ → Set α := fun k => F ∩ {x | u x ≤ k}
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k => hF.inter (measurableSet_le hu measurable_const)
  have hAmono : Monotone A := fun k l hkl x hx =>
    ⟨hx.1, show u x ≤ (l : ℝ) from (hx.2 : u x ≤ k).trans (Int.cast_le.mpr hkl)⟩
  have hhalf_pos : 0 < ENNReal.ofReal (a / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hhalf_lt : ENNReal.ofReal (a / 2) < ENNReal.ofReal a :=
    (ENNReal.ofReal_lt_ofReal_iff ha).mpr (by linarith)
  have hsum : ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]
  -- Step 2: `⋃ k, A k = F`, so `μ (A k) → μ F = ofReal a` and some `μ (A k₁) > ofReal (a / 2)`.
  have hUnion : (⋃ k, A k) = F := by
    refine Subset.antisymm (iUnion_subset fun k => inter_subset_left) fun x hx => ?_
    exact mem_iUnion.mpr ⟨⌈u x⌉, hx, show u x ≤ (⌈u x⌉ : ℝ) from Int.le_ceil _⟩
  have hlim_top : Tendsto (μ ∘ A) atTop (𝓝 (ENNReal.ofReal a)) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hAmono
    rwa [hUnion, hμF] at this
  obtain ⟨k₁, hk₁⟩ := (hlim_top.eventually (lt_mem_nhds hhalf_lt)).exists
  -- Step 3: `⋂ j, A (-j) = ∅`, so `μ (A (-j)) → 0` and some `μ (A (-j₀)) < ofReal (a / 2)`.
  have hBanti : Antitone fun j : ℕ => A (-(j : ℤ)) :=
    fun j j' hjj' => hAmono (neg_le_neg (Int.ofNat_le.mpr hjj'))
  have hInter : (⋂ j : ℕ, A (-(j : ℤ))) = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have hx' : u x ≤ ((-((1 - ⌊u x⌋).toNat : ℤ) : ℤ) : ℝ) :=
      (mem_iInter.mp hx (1 - ⌊u x⌋).toNat).2
    have hj : -((1 - ⌊u x⌋).toNat : ℤ) < ⌊u x⌋ := by
      have := Int.self_le_toNat (1 - ⌊u x⌋)
      omega
    exact absurd hx' (not_le.mpr ((Int.cast_lt.mpr hj).trans_le (Int.floor_le _)))
  have hlim_bot : Tendsto (μ ∘ fun j : ℕ => A (-(j : ℤ))) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun j => (hAmeas _).nullMeasurableSet) hBanti
      ⟨0, ne_top_of_le_ne_top (hμF ▸ ENNReal.ofReal_ne_top) (measure_mono inter_subset_left)⟩
    rwa [hInter, measure_empty] at this
  obtain ⟨j₀, hj₀⟩ := (hlim_bot.eventually (gt_mem_nhds hhalf_pos)).exists
  -- Step 4: `β` is the least integer with `ofReal (a / 2) ≤ μ (A β)`; the set of such integers
  -- contains `k₁` and is bounded below by `-j₀`.
  obtain ⟨β, hβK, hβmin⟩ := Int.exists_least_of_bdd
    (P := fun k => ENNReal.ofReal (a / 2) ≤ μ (A k))
    ⟨-(j₀ : ℤ), fun k hk => not_lt.mp fun hlt =>
      lt_irrefl _ ((hk.trans (measure_mono (hAmono hlt.le))).trans_lt hj₀)⟩
    ⟨k₁, hk₁.le⟩
  -- Step 5: the first inequality is `β ∈ K`.
  refine ⟨β, hβK, ?_⟩
  -- Step 6: `μ (A (β - 1)) < ofReal (a / 2)` by minimality, and `F ⊆ A (β - 1) ∪ (F ∩ {β ≤ u})`
  -- as `u` is integer-valued; subadditivity and `a / 2 + a / 2 = a` give the second inequality.
  have hβ1 : μ (A (β - 1)) < ENNReal.ofReal (a / 2) := by
    by_contra h
    have := hβmin _ (not_lt.mp h)
    omega
  have hcover : F ⊆ A (β - 1) ∪ (F ∩ {x | (β : ℝ) ≤ u x}) := by
    intro x hx
    obtain ⟨k, hk⟩ := hint x
    rcases le_or_gt k (β - 1) with hkb | hkb
    · exact Or.inl ⟨hx, show u x ≤ ((β - 1 : ℤ) : ℝ) by rw [hk]; exact_mod_cast hkb⟩
    · exact Or.inr ⟨hx, show (β : ℝ) ≤ u x by rw [hk]; exact_mod_cast (show β ≤ k by omega)⟩
  by_contra hlt
  have h1 : μ F ≤ μ (A (β - 1)) + μ (F ∩ {x | (β : ℝ) ≤ u x}) :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have h2 := ENNReal.add_lt_add hβ1 (not_le.mp hlt)
  rw [hsum, ← hμF] at h2
  exact lt_irrefl _ (h1.trans_lt h2)
/-- **Size and support bounds for a median** (Simon Ch. 6, 5.1, (31) and (35)).  Let `c` be a
median of a measurable `u` on a measurable `F`: both `F ∩ {u ≤ c}` and `F ∩ {c ≤ u}` have measure
at least `a / 2`, where `a > 0`.  Then `|c| a ≤ 2 ∫_F |u| dμ`, and if `c ≠ 0` then `u` is not
`μ`-a.e. zero on `F`.  On the half-measure set `S = F ∩ {c ≤ u}` (if `c ≥ 0`) or
`S = F ∩ {u ≤ c}` (if `c < 0`) one has `|c| ≤ |u|`, and `u ≠ 0` when `c ≠ 0`. -/
theorem Submission.fiw_tb_tda_im_median_bounds : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a c : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → Measurable u → ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ c}) → ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | c ≤ u x}) → ENNReal.ofReal (|c| * a) ≤ 2 * ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ ∧ (c ≠ 0 → μ (F ∩ {x | u x ≠ 0}) ≠ 0) := by
  intro α _ μ F a c u hF ha hu hle hge
  -- A measurable `S ⊆ F` with `a / 2 ≤ μ S` on which `|c| ≤ |u|`, and `u ≠ 0` if `c ≠ 0`.
  obtain ⟨S, hSm, hSF, hSμ, hSabs, hSne⟩ : ∃ S : Set α, MeasurableSet S ∧ S ⊆ F ∧
      ENNReal.ofReal (a / 2) ≤ μ S ∧ (∀ x ∈ S, |c| ≤ |u x|) ∧ (c ≠ 0 → ∀ x ∈ S, u x ≠ 0) := by
    rcases le_or_gt 0 c with hc | hc
    · refine ⟨F ∩ {x | c ≤ u x}, hF.inter (measurableSet_le measurable_const hu),
        inter_subset_left, hge, fun x hx => ?_, fun hc0 x hx => ?_⟩
      · rw [abs_of_nonneg hc]
        exact (show c ≤ u x from hx.2).trans (le_abs_self _)
      · exact ((lt_of_le_of_ne hc (Ne.symm hc0)).trans_le (show c ≤ u x from hx.2)).ne'
    · refine ⟨F ∩ {x | u x ≤ c}, hF.inter (measurableSet_le hu measurable_const),
        inter_subset_left, hle, fun x hx => ?_, fun _ x hx => ?_⟩
      · rw [abs_of_neg hc]
        exact (neg_le_neg (show u x ≤ c from hx.2)).trans (neg_le_abs _)
      · exact ((show u x ≤ c from hx.2).trans_lt hc).ne
  refine ⟨?_, fun hc0 hnull => ?_⟩
  · -- (M1) `|c| (a / 2) ≤ |c| μ(S) = ∫_S |c| ≤ ∫_S |u| ≤ ∫_F |u|`; multiply by `2`.
    have hS : ENNReal.ofReal |c| * ENNReal.ofReal (a / 2) ≤ ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ :=
      calc ENNReal.ofReal |c| * ENNReal.ofReal (a / 2) ≤ ENNReal.ofReal |c| * μ S := by gcongr
        _ = ∫⁻ _ in S, ENNReal.ofReal |c| ∂μ := (setLIntegral_const S _).symm
        _ ≤ ∫⁻ x in S, ENNReal.ofReal |u x| ∂μ :=
          setLIntegral_mono' hSm fun x hx => ENNReal.ofReal_le_ofReal (hSabs x hx)
        _ ≤ ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ := lintegral_mono_set hSF
    calc ENNReal.ofReal (|c| * a) = 2 * (ENNReal.ofReal |c| * ENNReal.ofReal (a / 2)) := by
          rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul zero_le_two]
          congr 1
          ring
      _ ≤ 2 * ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ := by gcongr
  · -- (M2) `S ⊆ F ∩ {u ≠ 0}` would be null, but `0 < ofReal (a / 2) ≤ μ S`.
    have hSsub : S ⊆ F ∩ {x | u x ≠ 0} := fun x hx => ⟨hSF hx, hSne hc0 x hx⟩
    have hS0 : μ S = 0 := measure_mono_null hSsub hnull
    have hpos : 0 < ENNReal.ofReal (a / 2) := ENNReal.ofReal_pos.mpr (half_pos ha)
    exact (hpos.trans_le (hSμ.trans_eq hS0)).ne rfl
/-- Median minimization: if `c₀` is a median of `u` on `F` (each of `F ∩ {u ≤ c₀}` and
`F ∩ {u ≥ c₀}` has measure at least `a / 2`, where `μ F = a`), then `c₀` minimizes
`c ↦ ∫_F |u - c| dμ`. -/
theorem Submission.fiw_tb_tda_im_median_minimizes :
    ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a c₀ : ℝ) (u : α → ℝ),
      MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → IntegrableOn u F μ →
      ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ c₀}) →
      ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | c₀ ≤ u x}) →
      ∀ c : ℝ,
        ∫⁻ x in F, ENNReal.ofReal |u x - c₀| ∂μ ≤ ∫⁻ x in F, ENNReal.ofReal |u x - c| ∂μ := by
  intro α _ μ F a c₀ u hF ha hμF hu _ hle hge c
  -- (P2)–(P3): if `μ (F ∩ S) ≥ a / 2`, then `μ (F \ S) = a - μ (F ∩ S) ≤ a / 2 ≤ μ (F ∩ S)`.
  have half : ∀ S : Set α, MeasurableSet S → ENNReal.ofReal (a / 2) ≤ μ (F ∩ S) →
      μ (F \ S) ≤ μ (F ∩ S) := by
    intro S hS hS2
    have ha2 : (0 : ℝ) ≤ a / 2 := by linarith
    have hfin : μ (F ∩ S) ≠ ∞ := ne_top_of_le_ne_top (by rw [hμF]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
    have hsum : μ (F ∩ S) + μ (F \ S) ≤ μ (F ∩ S) + ENNReal.ofReal (a / 2) :=
      calc μ (F ∩ S) + μ (F \ S) = μ F := measure_inter_add_sdiff F hS
        _ = ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) := by
          rw [hμF, ← ENNReal.ofReal_add ha2 ha2, add_halves]
        _ ≤ μ (F ∩ S) + ENNReal.ofReal (a / 2) := by gcongr
    exact ((ENNReal.add_le_add_iff_left hfin).1 hsum).trans hS2
  -- Step 1 (comparison): for `d ≥ 0`, if `|u - c₀| + d ≤ |u - c|` on `S`, `|u - c₀| - d ≤ |u - c|`
  -- off `S` and `μ (F \ S) ≤ μ (F ∩ S)`, integrate over `F ∩ S` and `F \ S`.
  have key : ∀ (S : Set α) (d : ℝ), MeasurableSet S → 0 ≤ d → μ (F \ S) ≤ μ (F ∩ S) →
      (∀ x ∈ S, |u x - c₀| + d ≤ |u x - c|) → (∀ x ∉ S, |u x - c₀| - d ≤ |u x - c|) →
      ∫⁻ x in F, ENNReal.ofReal |u x - c₀| ∂μ ≤ ∫⁻ x in F, ENNReal.ofReal |u x - c| ∂μ := by
    intro S d hS hd hμS hin hout
    have hin' : ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ + ENNReal.ofReal d * μ (F ∩ S) ≤
        ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c| ∂μ :=
      calc ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ + ENNReal.ofReal d * μ (F ∩ S)
          = ∫⁻ x in F ∩ S, (ENNReal.ofReal |u x - c₀| + ENNReal.ofReal d) ∂μ := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c| ∂μ :=
          setLIntegral_mono' (hF.inter hS) fun x hx => by
            rw [← ENNReal.ofReal_add (abs_nonneg _) hd]
            exact ENNReal.ofReal_le_ofReal (hin x hx.2)
    have hout' : ∫⁻ x in F \ S, ENNReal.ofReal |u x - c₀| ∂μ ≤
        ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F ∩ S) :=
      calc ∫⁻ x in F \ S, ENNReal.ofReal |u x - c₀| ∂μ
          ≤ ∫⁻ x in F \ S, (ENNReal.ofReal |u x - c| + ENNReal.ofReal d) ∂μ :=
            setLIntegral_mono' (hF.diff hS) fun x hx =>
              (ENNReal.ofReal_le_ofReal (by linarith [hout x hx.2])).trans ENNReal.ofReal_add_le
        _ = ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F \ S) := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F ∩ S) := by
            gcongr
    calc ∫⁻ x in F, ENNReal.ofReal |u x - c₀| ∂μ
        = ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ +
            ∫⁻ x in F \ S, ENNReal.ofReal |u x - c₀| ∂μ :=
          (lintegral_inter_add_sdiff (fun x => ENNReal.ofReal |u x - c₀|) F hS).symm
      _ ≤ ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ +
            (∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F ∩ S)) := by
          gcongr
      _ = (∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ + ENNReal.ofReal d * μ (F ∩ S)) +
            ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ := by
          ring
      _ ≤ ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c| ∂μ +
            ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ := by
          gcongr
      _ = ∫⁻ x in F, ENNReal.ofReal |u x - c| ∂μ :=
          lintegral_inter_add_sdiff (fun x => ENNReal.ofReal |u x - c|) F hS
  rcases le_or_gt c₀ c with hc | hc
  · -- Step 2: `c₀ ≤ c`; take `S = {u ≤ c₀}` and `d = c - c₀`.
    have hS : MeasurableSet {x | u x ≤ c₀} := measurableSet_le hu measurable_const
    refine key _ (c - c₀) hS (by linarith) (half _ hS hle) (fun x hx => ?_) (fun x hx => ?_)
    · have hx : u x ≤ c₀ := hx
      rw [abs_of_nonpos (show u x - c₀ ≤ 0 by linarith),
        abs_of_nonpos (show u x - c ≤ 0 by linarith)]
      linarith
    · have hx : c₀ < u x := not_le.1 hx
      rw [abs_of_pos (show 0 < u x - c₀ by linarith)]
      linarith [le_abs_self (u x - c)]
  · -- Step 3: `c < c₀`; take `S = {c₀ ≤ u}` and `d = c₀ - c`.
    have hS : MeasurableSet {x | c₀ ≤ u x} := measurableSet_le measurable_const hu
    refine key _ (c₀ - c) hS (by linarith) (half _ hS hge) (fun x hx => ?_) (fun x hx => ?_)
    · have hx : c₀ ≤ u x := hx
      rw [abs_of_nonneg (show 0 ≤ u x - c₀ by linarith),
        abs_of_nonneg (show 0 ≤ u x - c by linarith)]
      linarith
    · have hx : u x < c₀ := not_le.1 hx
      rw [abs_of_neg (show u x - c₀ < 0 by linarith)]
      linarith [neg_le_abs (u x - c)]
/-- **Mean deviation bound** (the comparison of `u` with its mean `ū = a⁻¹ ∫_F u dμ` on `F`,
`μ(F) = a`, in the integer-median step that feeds the Poincaré inequality, Simon Ch. 6, (32)).
For each `x`, `u(x) − ū = a⁻¹ ∫_F (u(x) − u(y)) dμ(y)`, so `|u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y)`;
integrating over `x ∈ F` gives `∫_F |u − ū| dμ ≤ a⁻¹ ∫_F ∫_F |u(x) − u(y)| dμ(y) dμ(x)`. -/
theorem Submission.fiw_tb_tda_im_mean_deviation : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → IntegrableOn u F μ → ∫⁻ x in F, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ∂μ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ := by
  intro α _ μ F a u _ ha hμF _ hint
  -- `μ(F) = a` is finite and its real value is `a`.
  have hfin : μ F ≠ ∞ := by rw [hμF]; exact ENNReal.ofReal_ne_top
  have hreal : μ.real F = a := by rw [measureReal_def, hμF, ENNReal.toReal_ofReal ha.le]
  have hainv : 0 < a⁻¹ := inv_pos.mpr ha
  -- Pointwise bound `|u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y)`, read in `ℝ≥0∞`.
  have hpt : ∀ x, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ≤
      ENNReal.ofReal a⁻¹ * ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ := by
    intro x
    -- `y ↦ u(x) − u(y)` is integrable on `F`: a constant minus `u`.
    have hc : IntegrableOn (fun _ : α => u x) F μ := integrableOn_const hfin
    have hsub : IntegrableOn (fun y => u x - u y) F μ := hc.sub hint
    -- `a⁻¹ ∫_F (u(x) − u(y)) dμ(y) = a⁻¹ (a u(x) − ∫_F u dμ) = u(x) − ū`.
    have hmean : u x - a⁻¹ * ∫ y in F, u y ∂μ = a⁻¹ * ∫ y in F, (u x - u y) ∂μ := by
      rw [integral_sub hc hint, setIntegral_const, hreal, smul_eq_mul, mul_sub,
        ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    -- `|∫_F f| ≤ ∫_F |f|` and `a⁻¹ > 0`.
    have habs : |u x - a⁻¹ * ∫ y in F, u y ∂μ| ≤ a⁻¹ * ∫ y in F, |u x - u y| ∂μ := by
      rw [hmean, abs_mul, abs_of_pos hainv]
      exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hainv.le
    calc ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ|
        ≤ ENNReal.ofReal (a⁻¹ * ∫ y in F, |u x - u y| ∂μ) := ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (∫ y in F, |u x - u y| ∂μ) :=
          ENNReal.ofReal_mul hainv.le
      _ = ENNReal.ofReal a⁻¹ * ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ := by
          rw [ofReal_integral_eq_lintegral_ofReal hsub.abs
            (Eventually.of_forall fun y => abs_nonneg _)]
  -- Integrate over `x ∈ F` and pull out the finite constant `ofReal a⁻¹`.
  calc ∫⁻ x in F, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ∂μ
      ≤ ∫⁻ x in F, ENNReal.ofReal a⁻¹ * ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Integer medians** (Simon Ch. 6, proof of 5.1, (31) and (35), on an arbitrary measure
space).  If `μ(F) = a > 0` and `u` is measurable, integer-valued and integrable on `F`, some
integer `β` has `|β| a ≤ 2 ∫_F |u|`, `β ≠ 0 → μ(F ∩ {u ≠ 0}) ≠ 0` and
`∫_F |u - β| ≤ a⁻¹ ∫_F ∫_F |u(x) - u(y)| dμ(y) dμ(x)`.  Take an integer median `β`, i.e.
`μ(F ∩ {u ≤ β}) ≥ a/2` and `μ(F ∩ {u ≥ β}) ≥ a/2` (`fiw_tb_tda_im_median_exists`).  The first
two estimates hold for every median (`fiw_tb_tda_im_median_bounds`).  A median minimizes
`c ↦ ∫_F |u - c|` (`fiw_tb_tda_im_median_minimizes`), so comparing with the mean
`c = a⁻¹ ∫_F u` (`fiw_tb_tda_im_mean_deviation`) gives the third. -/
theorem Submission.fiw_tb_tda_integer_median : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → (∀ x, ∃ k : ℤ, u x = k) → IntegrableOn u F μ → ∃ β : ℤ, ENNReal.ofReal (|(β : ℝ)| * a) ≤ 2 * ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ ∧ (β ≠ 0 → μ (F ∩ {x | u x ≠ 0}) ≠ 0) ∧ ∫⁻ x in F, ENNReal.ofReal |u x - β| ∂μ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ := by
  intro α _ μ F a u hF ha hμF hu hZ hui
  -- An integer median: `μ(F ∩ {u ≤ β}) ≥ a/2` and `μ(F ∩ {u ≥ β}) ≥ a/2`.
  obtain ⟨β, hle, hge⟩ := Submission.fiw_tb_tda_im_median_exists μ F a u hF ha hμF hu hZ
  -- (M1) and (M2) hold for every real median `c = β`.
  obtain ⟨hM1, hM2⟩ := Submission.fiw_tb_tda_im_median_bounds μ F a β u hF ha hu hle hge
  refine ⟨β, hM1, fun hβ => hM2 (Int.cast_ne_zero.mpr hβ), ?_⟩
  -- (M4): `∫_F |u - β| ≤ ∫_F |u - ū|` for the mean `ū = a⁻¹ ∫_F u`, then the mean deviation bound.
  exact (Submission.fiw_tb_tda_im_median_minimizes μ F a β u hF ha hμF hu hui hle hge
    (a⁻¹ * ∫ y in F, u y ∂μ)).trans
    (Submission.fiw_tb_tda_im_mean_deviation μ F a u hF ha hμF hu hui)
/-- A translation estimate `∫ |u(x + h) − u(x)| dx ≤ ‖h‖ Λ` bounds the double integral over
`r`-balls: `∫_x ∫_{closedBall(x, r)} |u(x) − u(y)| dy dx ≤ r Λ |closedBall(0, r)|`.
Substituting `y = x + h` turns the inner integral into `∫ 1_B(h) |u(x + h) − u(x)| dh` with
`B = closedBall(0, r)`; Tonelli swaps the integrals, and on `B` the hypothesis and `‖h‖ ≤ r`
bound the inner `x`-integral by `r Λ`. -/
theorem Submission.fiw_tb_tda_ps_translation_ball :
    ∀ (n : ℕ) (u : Eucl n → ℝ) (Λ : ℝ≥0∞) (r : ℝ), Measurable u →
      (∀ h : Eucl n, ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| ≤
        ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r) := by
  intro n u Λ r hu hΛ
  set B : Set (Eucl n) := closedBall 0 r
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- `x + h ∈ closedBall x r ↔ h ∈ closedBall 0 r`.
  have hmem : ∀ x h : Eucl n, x + h ∈ closedBall x r ↔ h ∈ B := by
    intro x h
    simp [B, mem_closedBall, dist_eq_norm]
  -- Substituting `y = x + h` in the inner integral.
  have hsub : ∀ x : Eucl n, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| =
      ∫⁻ h, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| := by
    intro x
    rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_left_eq_self
      ((closedBall x r).indicator fun y => ENNReal.ofReal |u x - u y|) x]
    refine lintegral_congr fun h => ?_
    by_cases hh : h ∈ B
    · rw [indicator_of_mem ((hmem x h).2 hh), indicator_of_mem hh, Pi.one_apply, one_mul,
        abs_sub_comm]
    · rw [indicator_of_notMem (fun h' => hh ((hmem x h).1 h')), indicator_of_notMem hh, zero_mul]
  -- The integrand is jointly measurable.
  have hk : Measurable fun p : Eucl n × Eucl n =>
      B.indicator 1 p.2 * ENNReal.ofReal |u (p.1 + p.2) - u p.1| :=
    ((measurable_one.indicator hBm).comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp ((hu.comp measurable_add).sub (hu.comp measurable_fst))))
  calc ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y|
      = ∫⁻ x, ∫⁻ h, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_congr fun x => hsub x
    _ = ∫⁻ h, ∫⁻ x, B.indicator 1 h * ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_lintegral_swap hk.aemeasurable
    _ = ∫⁻ h, B.indicator 1 h * ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| :=
        lintegral_congr fun h => lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp ((hu.comp (measurable_add_const h)).sub hu)))
    _ ≤ ∫⁻ h, B.indicator (fun _ => ENNReal.ofReal r * Λ) h := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ B
        · rw [indicator_of_mem hh, indicator_of_mem hh, Pi.one_apply, one_mul]
          refine (hΛ h).trans ?_
          gcongr
          exact mem_closedBall_zero_iff.1 hh
        · rw [indicator_of_notMem hh, indicator_of_notMem hh, zero_mul]
    _ = ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r) :=
        lintegral_indicator_const hBm _
/-- Box bound for the volume of a Euclidean ball, used in `fiw_tb_tda_poincare_sum`:
`closedBall(0, r) ⊆ [-r, r]ⁿ`, hence `Lⁿ(closedBall(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_ps_ball_volume_le : ∀ (n : ℕ) (r : ℝ), 0 ≤ r → volume (closedBall (0 : Eucl n) r) ≤ ENNReal.ofReal ((2 * r) ^ n) := by
  intro n r hr
  -- Steps 1–2: `|xᵢ| ≤ ‖x‖ ≤ r`, so `closedBall(0, r) ⊆ ofLp⁻¹(Icc(-r, r))`.
  have hsub : closedBall (0 : Eucl n) r ⊆
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => -r) (fun _ : Fin n => r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    have hcoord : ∀ i, |x i| ≤ r := fun i => by
      have h := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h
      exact h.trans hx
    exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
  -- Steps 3–4: `ofLp` preserves volume, and the box has volume `ofReal (2r) ^ n = ofReal ((2r)ⁿ)`.
  calc volume (closedBall (0 : Eucl n) r)
      ≤ volume (WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => -r) (fun _ : Fin n => r)) :=
        measure_mono hsub
    _ = volume (Icc (fun _ : Fin n => -r) (fun _ : Fin n => r)) :=
        (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ENNReal.ofReal ((2 * r) ^ n) := by
        rw [Real.volume_Icc_pi, ENNReal.ofReal_pow (by linarith)]
        simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, two_mul]
/-- Top-dimensional lattice cubes in `ℝⁿ`, `n = m + 1`, `ρ > 0`.  The only order embedding
`Fin n ↪o Fin n` is the identity, so `latticeFace ρ F` is the closed cube `ρ (F.1 + [0, 1]ⁿ)`:
it is closed, has volume `ρⁿ` and diameter at most `√n ρ`.  The hyperplanes `{xᵢ = ρ k}` are
null, the cubes cover `ℝⁿ` and two distinct cubes only meet inside these hyperplanes, so
lower integrals and integrals of integrable functions split as sums over the cubes. -/
theorem Submission.fiw_tb_tda_lattice_cubes :
    ∀ (m : ℕ) (ρ : ℝ), 0 < ρ →
      (∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
        {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)}) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F)) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1),
        volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1))) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F, ∀ y ∈ latticeFace ρ F,
        dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) ∧
      (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) ∧
      (∀ g : Eucl (m + 1) → ℝ≥0∞, ∫⁻ x, g x =
        ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x) ∧
      ∀ f : Eucl (m + 1) → ℝ, Integrable f →
        ∫ x, f x = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x := by
  intro m ρ hρ
  -- (a) A strictly monotone self-map of the finite chain `Fin (m + 1)` is the identity.
  have ha : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j :=
    fun F _ => F.2.strictMono.apply_eq
  -- (b) Every coordinate lies in `range F.2`, so the face is the closed cube.
  have hb : ∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
      {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)} := by
    intro F
    have hr : ∀ i, i ∈ range F.2 := fun i => ⟨i, ha F i⟩
    ext x
    simp only [latticeFace, mem_ofPred_eq, hr, not_true_eq_false, true_implies, false_implies,
      and_true]
  -- The cube is the preimage of a box under the volume-preserving `WithLp.ofLp`.
  have hbox : ∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
      WithLp.ofLp ⁻¹' Icc (fun i => ρ * (F.1 i : ℝ)) (fun i => ρ * ((F.1 i : ℝ) + 1)) := by
    intro F
    rw [hb F]
    ext x
    simp [Pi.le_def, forall_and]
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  -- (c) The cube is measurable.
  have hc : ∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F) := by
    intro F
    rw [hbox F]
    exact hvol.measurable measurableSet_Icc
  -- (d) Its volume is `∏ᵢ ρ = ρ^(m + 1)`.
  have hd : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1)) := by
    intro F
    rw [hbox F, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    have hside : ∀ i : Fin (m + 1), ρ * ((F.1 i : ℝ) + 1) - ρ * (F.1 i : ℝ) = ρ := fun i => by
      ring
    simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hρ.le]
  -- (e) Coordinates of two points of the cube differ by at most `ρ`.
  have he : ∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F,
      ∀ y ∈ latticeFace ρ F, dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ := by
    intro F x hx y hy
    rw [hb F] at hx hy
    have hcoord : ∀ i, dist (x i) (y i) ^ 2 ≤ ρ ^ 2 := by
      intro i
      refine pow_le_pow_left₀ dist_nonneg ?_ 2
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * ρ ^ 2 := by
      calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin (m + 1), ρ ^ 2 :=
            Finset.sum_le_sum fun i _ => hcoord i
        _ = ((m + 1 : ℕ) : ℝ) * ρ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [EuclideanSpace.dist_eq]
    calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * ρ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hρ.le]
  -- (f) Each hyperplane `{xᵢ = ρ k}` is the `WithLp.ofLp`-preimage of a null hyperplane.
  have hf : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro k
    have hnull : (volume : Measure (Eucl (m + 1))) {x | x i = ρ * k} = 0 :=
      hvol.quasiMeasurePreserving.preimage_null
        (Measure.pi_hyperplane (fun _ : Fin (m + 1) => (volume : Measure ℝ)) i (ρ * k))
    rw [ae_iff]
    simpa using hnull
  -- A point of a cube off the hyperplanes determines the lattice point: `⌊xᵢ / ρ⌋ = F.1 i`.
  have hfloor : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (x : Eucl (m + 1)),
      x ∈ latticeFace ρ F → (∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) →
        ∀ i, ⌊x i / ρ⌋ = F.1 i := by
    intro F x hx hgood i
    rw [hb F] at hx
    obtain ⟨h1, h2⟩ := hx i
    have h3 : x i ≠ ρ * ((F.1 i + 1 : ℤ) : ℝ) := hgood i (F.1 i + 1)
    push_cast at h3
    have h4 : x i < ρ * ((F.1 i : ℝ) + 1) := lt_of_le_of_ne h2 h3
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hρ]
      linarith
    · rw [div_lt_iff₀ hρ]
      linarith
  -- The cubes cover `ℝ^(m + 1)`: `x` lies in the cube at `(⌊xᵢ / ρ⌋)ᵢ`.
  have hU : (⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    refine ⟨(fun i => ⌊x i / ρ⌋, OrderEmbedding.ofStrictMono id strictMono_id), ?_⟩
    rw [hb]
    intro i
    constructor
    · have h := Int.floor_le (x i / ρ)
      rw [le_div_iff₀ hρ] at h
      linarith
    · have h := Int.lt_floor_add_one (x i / ρ)
      rw [div_lt_iff₀ hρ] at h
      linarith
  -- Distinct cubes have distinct lattice points, so they only meet in the null hyperplanes.
  have hbad : (volume : Measure (Eucl (m + 1)))
      {x | ¬ ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k} = 0 := ae_iff.1 hf
  have hdisj : Pairwise (Function.onFun (AEDisjoint (volume : Measure (Eucl (m + 1))))
      fun F : LatticeFaceIndex (m + 1) (m + 1) => latticeFace ρ F) := by
    intro F G hFG
    refine measure_mono_null (fun x hx => ?_) hbad
    intro hgood
    have h2 : F.2 = G.2 := DFunLike.ext _ _ fun j => (ha F j).trans (ha G j).symm
    have h1 : F.1 ≠ G.1 := fun h => hFG (Prod.ext h h2)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact hi ((hfloor F x hx.1 hgood i).symm.trans (hfloor G x hx.2 hgood i))
  refine ⟨ha, hb, hc, hd, he, hf, ?_, ?_⟩
  -- (g) Lower integrals split over the countable, a.e. disjoint cover.
  · intro g
    calc ∫⁻ x, g x = ∫⁻ x in ⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F, g x := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x :=
          lintegral_iUnion₀ (fun F => (hc F).nullMeasurableSet) hdisj g
  -- (h) So do integrals of integrable functions.
  · intro f hfi
    calc ∫ x, f x = ∫ x in ⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F, f x := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x :=
          integral_iUnion_ae (fun F => (hc F).nullMeasurableSet) hdisj (by
            rw [hU]
            exact hfi.integrableOn)
/-- Simon Ch. 6, (2.7) with `μ = Lⁿ` (`n = m + 1`): an integrable density `v` on `ℝⁿ` defines
the top-dimensional current `ω ↦ ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` in `𝒟ₙ(ℝⁿ)`.  Since `‖eᵢ‖ = 1`,
`|⟨ω(x), e₁ ∧ ⋯ ∧ eₙ⟩| ≤ ‖ω(x)‖`, so the integrand is dominated by `(sup ‖ω‖)·|v|`; linearity is
`integral_add`/`integral_const_mul`, and for a null sequence `ω_j → 0` of test forms
`sup ‖ω_j‖ → 0`, whence `|T(ω_j)| ≤ sup ‖ω_j‖ · ∫ |v| → 0`. -/
theorem Submission.fiw_tb_tda_density_current : ∀ (m : ℕ) (v : Eucl (m + 1) → ℝ), Integrable v → ∃ T : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), T ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m v hv
  -- Step 1: `|α(e₁, …, eₙ)| ≤ ‖α‖` for every `n`-covector `α`, since `‖eᵢ‖ = 1`.
  have hcov : ∀ α : Covector (Eucl (m + 1)) (m + 1),
      ‖α (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖α‖ := by
    intro α
    calc ‖α (fun i => EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖α‖ * ∏ i, ‖(EuclideanSpace.single i (1 : ℝ) : Eucl (m + 1))‖ := α.le_opNorm _
      _ = ‖α‖ := by simp
  -- Step 2: if `η` is continuous with `‖η‖ ≤ B`, then `v · η(e)` is integrable and
  -- `|∫ v η(e)| ≤ B ∫ |v|`.
  have hkey : ∀ (η : Eucl (m + 1) → Covector (Eucl (m + 1)) (m + 1)) (B : ℝ),
      Continuous η → (∀ x, ‖η x‖ ≤ B) →
      Integrable (fun x => v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))) ∧
        ‖∫ x, v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ B * ∫ x, ‖v x‖ := by
    intro η B hη hB
    have hbd : ∀ x, ‖η x (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ B :=
      fun x => (hcov _).trans (hB x)
    have hbound : ∀ᵐ x, ‖v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ B * ‖v x‖ :=
      Eventually.of_forall fun x => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _)
    refine ⟨hv.mul_bdd (hη.eval_const _).aestronglyMeasurable (Eventually.of_forall hbd), ?_⟩
    calc ‖∫ x, v x * η x (fun i => EuclideanSpace.single i (1 : ℝ))‖
        ≤ ∫ x, B * ‖v x‖ := norm_integral_le_of_norm_le (hv.norm.const_mul B) hbound
      _ = B * ∫ x, ‖v x‖ := integral_const_mul B _
  -- Step 3: the integrand of every test form is integrable.
  have hintω : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1),
      Integrable (fun x => v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ))) := by
    intro ω
    have hcont : Continuous (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
      ContDiff.continuous ω.property.1.1
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support ω.property.1.2
    exact (hkey _ B hcont hB).1
  -- Step 4: the linear functional `ω ↦ ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.
  let T₀ : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ))
      map_add' := by
        intro ω₁ ω₂
        simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add]
        exact integral_add (hintω ω₁) (hintω ω₂)
      map_smul' := by
        intro c ω
        simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul, RingHom.id_apply, mul_left_comm (v _) c]
        exact integral_const_mul c _ }
  -- Step 5: sequential continuity at `0`, from uniform convergence of the forms themselves.
  refine ⟨⟨T₀, ?_⟩, fun ω => rfl⟩
  intro ωs hconv
  obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
  set I := ∫ x, ‖v x‖
  have hI0 : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  have h0 := Metric.tendstoUniformlyOn_iff.1 (hunif 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
  filter_upwards [h0 _ hδ] with j hj
  have hBj : ∀ y, ‖(ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) y‖ ≤ ε / (I + 1) := by
    intro y
    by_cases hy : y ∈ K
    · have h1 := hj y hy
      have h2 : iteratedFDeriv ℝ 0
          ((0 : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) :
            DifferentialForm (Eucl (m + 1)) (m + 1)) y = 0 := by
        rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
        simp
      rw [h2, dist_zero_left, norm_iteratedFDeriv_zero] at h1
      exact h1.le
    · rw [image_eq_zero_of_notMem_tsupport fun hy' => hy (hsupp j hy'), norm_zero]
      exact hδ.le
  have hcont : Continuous (ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
    ContDiff.continuous (ωs j).property.1.1
  have hle := (hkey _ _ hcont hBj).2
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith
/-- A top-dimensional current with an integrable integer density `v` that is locally constant
where it is nonzero is integer multiplicity (Simon Ch. 6, 3.1):
`T(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ = τ(M, θ, ξ)(ω)` with `M = {v ≠ 0}` (open), `θ = |v|` and
`ξ = ±e₁ ∧ ⋯ ∧ eₙ` according to the sign of `v`.  Near each `x ∈ M` the multiplicity `θ` is
constant, so the weighted blow-up integrals of Ch. 3, 1.7 are eventually equal to `θ(x) ∫ f dLⁿ`
and the approximate tangent space is `ℝⁿ = span(e)`. -/
theorem Submission.fiw_tb_tda_locally_constant_im : ∀ (m : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (v : Eucl (m + 1) → ℝ), Measurable v → Integrable v → (∀ x, ∃ k : ℤ, v x = k) → (∀ x, v x ≠ 0 → ∀ᶠ y in 𝓝 x, v y = v x) → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), T ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → IsIntegerMultiplicity T := by
  intro m T v hvm hvi hvZ hvloc hT
  -- Notation: `e = (e₀, …, e_m)`, `M = {v ≠ 0}`, `θ = |v|`, `ξ = ±e₀ ∧ ⋯ ∧ e_m` (`+` iff `v > 0`).
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ)
  set M : Set (Eucl (m + 1)) := {x | v x ≠ 0}
  set θ : Eucl (m + 1) → ℝ := fun x => |v x|
  set ξ : Eucl (m + 1) → NVector (Eucl (m + 1)) (m + 1) :=
    fun x => if 0 < v x then simpleNVector e else -simpleNVector e
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  -- Step 2: `M` is open (local constancy of `v` where `v ≠ 0`), hence measurable.
  have hMopen : IsOpen M := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hvloc x hx] with y hy
    show v y ≠ 0
    rw [hy]
    exact hx
  have hMmeas : MeasurableSet M := hMopen.measurableSet
  -- Step 1: `θ(x) ⟨α, ξ(x)⟩ = v(x) α(e)` for every covector `α`.
  have hθξ : ∀ x (α : Covector (Eucl (m + 1)) (m + 1)), θ x * ξ x α = v x * α e := by
    intro x α
    by_cases hpos : 0 < v x
    · simp [θ, ξ, hpos, abs_of_pos hpos]
    · simp [θ, ξ, hpos, abs_of_nonpos (not_lt.mp hpos)]
  -- Step 4: the weighted approximate tangent space at `x ∈ M` is `ℝⁿ`.
  have htan : ∀ x ∈ M, HasWeightedApproximateTangentSpaceAt (m + 1) M θ x ⊤ := by
    intro x hx
    refine ⟨by rw [finrank_top, finrank_euclideanSpace_fin], fun f => ?_⟩
    -- `v = v(x)` on `B(x, δ)`, and `spt f ⊆ B̄(0, R)`.
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hvloc x hx)
    obtain ⟨R, hR, hRsupp⟩ :=
      f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Eucl (m + 1))
    -- For `0 < r < δ / (R + 1)` and `f(y) ≠ 0`: `x + r y ∈ B(x, δ) ⊆ M`, so
    -- `y = η_{x,r}(x + r y) ∈ η_{x,r}(M)` and `θ(x + r y) = θ(x)`.
    have hsmall : ∀ r ∈ Ioo (0 : ℝ) (δ / (R + 1)), ∀ y, f y ≠ 0 →
        y ∈ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∧ θ (x + r • y) = θ x := by
      intro r hr y hy
      have hyR : ‖y‖ ≤ R := by
        simpa using hRsupp (subset_tsupport _ hy)
      have hdist : dist (x + r • y) x < δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
        calc r * ‖y‖ ≤ r * (R + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.1.le
          _ < δ := (lt_div_iff₀ (by linarith)).mp hr.2
      have hv : v (x + r • y) = v x := hball hdist
      refine ⟨⟨x + r • y, ?_, ?_⟩, ?_⟩
      · show v (x + r • y) ≠ 0
        rw [hv]
        exact hx
      · simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hr.1.ne']
      · simp [θ, hv]
    -- Hence the blow-up integral equals `θ(x) ∫ f dHⁿ` for all such `r`.
    have hconst : ∀ r ∈ Ioo (0 : ℝ) (δ / (R + 1)),
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y * θ (x + r • y)
            ∂(μHE[m + 1] : Measure (Eucl (m + 1))) =
          θ x * ∫ y in ((⊤ : Submodule ℝ (Eucl (m + 1))) : Set (Eucl (m + 1))), f y
            ∂(μHE[m + 1] : Measure (Eucl (m + 1))) := by
      intro r hr
      rw [Submodule.top_coe, Measure.restrict_univ, setIntegral_eq_integral_of_forall_compl_eq_zero,
        ← integral_const_mul]
      · congr 1
        funext y
        by_cases hy : f y = 0
        · simp [hy]
        · rw [(hsmall r hr y hy).2, mul_comm]
      · intro y hy
        by_cases hfy : f y = 0
        · simp [hfy]
        · exact absurd (hsmall r hr y hfy).1 hy
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ (by linarith : (0 : ℝ) < R + 1))] with r hr
    exact (hconst r hr).symm
  -- `span(range e) = ℝⁿ`.
  have hspan : Submodule.span ℝ (range e) = ⊤ := by
    have h := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.span_eq
    have hcoe : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis = e := by
      funext i
      simp [e]
    rwa [hcoe] at h
  refine ⟨M, θ, ξ, ⟨subset_univ M, hMmeas.nullMeasurableSet, ?_, fun x hx => abs_pos.mpr hx,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- Step 3: `M ⊆ range id` is countably `n`-rectifiable.
    exact (Poincare.SimonGMT.Chapter03.countablyRectifiable_range
      (LipschitzWith.id : LipschitzWith 1 (id : Eucl (m + 1) → Eucl (m + 1)))).mono
      (by rw [range_id]; exact subset_univ M)
  · -- `θ = |v|` is integrable.
    intro K _ _
    rw [hvol]
    exact hvi.abs.integrableOn
  · -- `ξ` is constant on `{v > 0}` and on its complement.
    exact (StronglyMeasurable.ite (measurableSet_lt measurable_const hvm)
      stronglyMeasurable_const stronglyMeasurable_const).aestronglyMeasurable
  · -- Orientation by the orthonormal frame `e` of `TₓM = ℝⁿ`, at every `x ∈ M`.
    refine ae_restrict_of_forall_mem hMmeas fun x hx =>
      ⟨e, EuclideanSpace.orthonormal_single, ?_, ?_⟩
    · rw [hspan]
      exact htan x hx
    · by_cases hpos : 0 < v x
      · left
        simp [ξ, hpos]
      · right
        simp [ξ, hpos]
  · -- `θ = |v|` is natural-valued.
    intro x _
    obtain ⟨k, hk⟩ := hvZ x
    exact ⟨k.natAbs, by rw [Nat.cast_natAbs, Int.cast_abs, ← hk]⟩
  · -- Step 5: `τ(M, θ, ξ)(ω) = ∫_M v ω_e dLⁿ = ∫ v ω_e dLⁿ = T(ω)`.
    intro ω
    rw [hT ω]
    unfold tauAction
    rw [hvol]
    simp_rw [hθξ]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have hx0 : v x = 0 := by
      by_contra h
      exact hx h
    simp [hx0]
/-- **Top-dimensional lattice chains** (Simon Ch. 6, proof of 5.1, (29) and (34), in `ℝⁿ` with
`n = m + 1`).  If `β_F ∈ ℤ` and `∑_F |β_F| ρⁿ < ∞`, let `v = ∑_F β_F 1_{F̊}`, i.e.
`v(x) = β(⌊x/ρ⌋, id)` when no coordinate of `x` lies in `ρℤ` and `v(x) = 0` otherwise.
Then `v` is integrable and integer-valued, `v = β_F` a.e. on each closed cube `F`, and `v` is
locally constant where it is nonzero.  The current `Pc(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` of
`fiw_tb_tda_density_current` is `∑_F β_F [[F]]` (split the integral over the cubes with
`fiw_tb_tda_lattice_cubes`) and is integer multiplicity by `fiw_tb_tda_locally_constant_im`. -/
theorem Submission.fiw_tb_tda_lattice_chain : ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ∀ β : LatticeFaceIndex (m + 1) (m + 1) → ℝ, (∀ F, ∃ k : ℤ, β F = k) → (∑' F, ENNReal.ofReal (|β F| * ρ ^ (m + 1))) < ∞ → ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (v : Eucl (m + 1) → ℝ), IsLatticeChain ρ β Pc ∧ IsIntegerMultiplicity Pc ∧ Integrable v ∧ (∀ F, ∀ᵐ x ∂((volume : Measure (Eucl (m + 1))).restrict (latticeFace ρ F)), v x = β F) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m ρ hρ β hβZ hβsum
  -- The cube toolkit: `F.2 = id`, `Q_F = ρ (F.1 + [0, 1]ⁿ)` has volume `ρⁿ`, a.e. point is
  -- good (no coordinate in `ρℤ`), and integrals split over the cubes.
  obtain ⟨hF2, hQ, hQmeas, hQvol, -, hgood, hlint, hint⟩ :=
    Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  have hcoord : ∀ i : Fin (m + 1), Continuous fun x : Eucl (m + 1) => x i := fun i => by
    fun_prop
  -- Step 1: `v(x) = β(z(x), α₀)`, `z(x) = ⌊x/ρ⌋`, at good points `x ∈ G`; `v = 0` off `G`.
  let α₀ : SimonMultiIndex (m + 1) (m + 1) := RelEmbedding.refl _
  have hα₀ : ∀ F : LatticeFaceIndex (m + 1) (m + 1), F.2 = α₀ := fun F =>
    RelEmbedding.ext (hF2 F)
  let G : Set (Eucl (m + 1)) := {x | ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k}
  let z : Eucl (m + 1) → Fin (m + 1) → ℤ := fun x i => ⌊x i / ρ⌋
  let v : Eucl (m + 1) → ℝ := G.indicator fun x => β (z x, α₀)
  -- Step 2: `v` is measurable and integer-valued.
  have hGmeas : MeasurableSet G := by
    have hG : G = ⋂ (i : Fin (m + 1)) (k : ℤ), {x : Eucl (m + 1) | x i ≠ ρ * k} := by
      ext x
      simp only [G, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hG]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      (isOpen_ne_fun (hcoord i) continuous_const).measurableSet
  have hfloor : Measurable (Int.floor : ℝ → ℤ) := measurable_to_countable' fun k => by
    rw [Int.preimage_floor_singleton]
    exact measurableSet_Ico
  have hzmeas : Measurable z :=
    measurable_pi_iff.mpr fun i => hfloor.comp ((hcoord i).measurable.div_const ρ)
  have hvmeas : Measurable v :=
    ((measurable_of_countable fun w : Fin (m + 1) → ℤ => β (w, α₀)).comp hzmeas).indicator
      hGmeas
  have hvZ : ∀ x, ∃ k : ℤ, v x = k := by
    intro x
    by_cases hx : x ∈ G
    · obtain ⟨k, hk⟩ := hβZ (z x, α₀)
      exact ⟨k, (Set.indicator_of_mem hx _).trans hk⟩
    · exact ⟨0, (Set.indicator_of_notMem hx _).trans Int.cast_zero.symm⟩
  -- Step 3: at good points of the closed cube `Q_F`, `⌊x/ρ⌋ = F.1`; so `v = β_F` a.e. on `Q_F`.
  have hval : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (x : Eucl (m + 1)),
      x ∈ latticeFace ρ F → x ∈ G → v x = β F := by
    intro F x hxQ hxG
    rw [hQ F] at hxQ
    have hz : z x = F.1 := by
      funext i
      obtain ⟨h1, h2⟩ := hxQ i
      have h1' : ρ * (F.1 i : ℝ) < x i := lt_of_le_of_ne h1 fun h => hxG i (F.1 i) h.symm
      have h2' : x i < ρ * ((F.1 i : ℝ) + 1) := lt_of_le_of_ne h2 fun h =>
        hxG i (F.1 i + 1) (by rw [h, Int.cast_add, Int.cast_one])
      show ⌊x i / ρ⌋ = F.1 i
      rw [Int.floor_eq_iff, le_div_iff₀ hρ, div_lt_iff₀ hρ]
      constructor <;> linarith
    exact (Set.indicator_of_mem hxG _).trans (congrArg β (Prod.ext hz (hα₀ F).symm))
  have hae : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∀ᵐ x ∂((volume : Measure (Eucl (m + 1))).restrict (latticeFace ρ F)), v x = β F := by
    intro F
    filter_upwards [ae_restrict_mem (hQmeas F), ae_restrict_of_ae hgood] with x hxQ hxG
    exact hval F x hxQ hxG
  -- Step 4: if `v(x) ≠ 0`, `v` is constant on the open cube `∏ᵢ (ρ zᵢ, ρ (zᵢ + 1)) ∋ x`.
  have hloc : ∀ x, v x ≠ 0 → ∀ᶠ y in 𝓝 x, v y = v x := by
    intro x hx
    have hxG : x ∈ G := by
      by_contra hxG
      exact hx (Set.indicator_of_notMem hxG _)
    have hO : IsOpen {y : Eucl (m + 1) |
        ∀ i, ρ * (z x i : ℝ) < y i ∧ y i < ρ * ((z x i : ℝ) + 1)} := by
      simp only [Set.ofPred_forall, Set.ofPred_and]
      exact isOpen_iInter_of_finite fun i =>
        (isOpen_lt continuous_const (hcoord i)).inter (isOpen_lt (hcoord i) continuous_const)
    have hxO : ∀ i, ρ * (z x i : ℝ) < x i ∧ x i < ρ * ((z x i : ℝ) + 1) := by
      intro i
      have h1 : ((z x i : ℤ) : ℝ) ≤ x i / ρ := Int.floor_le (x i / ρ)
      have h2 : x i / ρ < (z x i : ℝ) + 1 := Int.lt_floor_add_one (x i / ρ)
      rw [le_div_iff₀ hρ] at h1
      rw [div_lt_iff₀ hρ] at h2
      exact ⟨lt_of_le_of_ne (by linarith) fun h => hxG i (z x i) h.symm, by linarith⟩
    filter_upwards [hO.mem_nhds hxO] with y hy
    have hyz : z y = z x := by
      funext i
      obtain ⟨h1, h2⟩ := hy i
      show ⌊y i / ρ⌋ = z x i
      rw [Int.floor_eq_iff, le_div_iff₀ hρ, div_lt_iff₀ hρ]
      constructor <;> linarith
    have hyG : y ∈ G := by
      intro i k hk
      obtain ⟨h1, h2⟩ := hy i
      rw [hk] at h1 h2
      have h3 : z x i < k := by exact_mod_cast lt_of_mul_lt_mul_left h1 hρ.le
      have h4 : k < z x i + 1 := by exact_mod_cast lt_of_mul_lt_mul_left h2 hρ.le
      omega
    show G.indicator (fun x => β (z x, α₀)) y = G.indicator (fun x => β (z x, α₀)) x
    rw [Set.indicator_of_mem hyG, Set.indicator_of_mem hxG, hyz]
  -- Step 5: `∫ |v| = ∑_F |β_F| ρⁿ < ∞`, so `v ∈ L¹`.
  have hcube : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∫⁻ x in latticeFace ρ F, ‖v x‖ₑ = ENNReal.ofReal (|β F| * ρ ^ (m + 1)) := by
    intro F
    calc ∫⁻ x in latticeFace ρ F, ‖v x‖ₑ = ∫⁻ _ in latticeFace ρ F, ‖β F‖ₑ :=
          lintegral_congr_ae (by filter_upwards [hae F] with x hx; rw [hx])
      _ = ‖β F‖ₑ * volume (latticeFace ρ F) := setLIntegral_const _ _
      _ = ENNReal.ofReal (|β F| * ρ ^ (m + 1)) := by
          rw [hQvol F, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  have hvint : Integrable v := by
    refine ⟨hvmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hlint fun x => ‖v x‖ₑ, tsum_congr hcube]
    exact hβsum
  -- Step 6: the current `Pc(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.
  obtain ⟨Pc, hPc⟩ := Submission.fiw_tb_tda_density_current m v hvint
  -- Step 7: splitting `∫ v ω_e` over the cubes, where `v = β_F`, gives `∑_F β_F [[F]](ω)`.
  have hchain : IsLatticeChain ρ β Pc := by
    intro ω
    have hωcont : Continuous (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
      ContDiff.continuous ω.property.1.1
    have hωecont : Continuous fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      (continuous_eval_const _).comp hωcont
    have hωecs : HasCompactSupport fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      ω.property.1.2.comp_left (g := fun c : Covector (Eucl (m + 1)) (m + 1) =>
        c (fun i => EuclideanSpace.single i (1 : ℝ))) rfl
    obtain ⟨C, hC⟩ := hωecont.bounded_above_of_compact_support hωecs
    have hprod : Integrable fun x => v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      hvint.mul_bdd hωecont.aestronglyMeasurable (ae_of_all _ hC)
    rw [hPc ω, hint _ hprod]
    refine tsum_congr fun F => ?_
    rw [latticeFaceAction, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      ← integral_const_mul]
    simp only [hF2 F]
    exact integral_congr_ae (by filter_upwards [hae F] with x hx; rw [hx])
  -- Step 8: `v` is integer-valued and locally constant where nonzero, so `Pc` is integer
  -- multiplicity.
  exact ⟨Pc, v, hchain,
    Submission.fiw_tb_tda_locally_constant_im m Pc v hvmeas hvint hvZ hloc hPc, hvint, hae, hPc⟩
/-- **Difference of two top-dimensional density currents.**  On `ℝⁿ` (`n = m + 1`) let
`X(ω) = ∫ u ω_e dLⁿ` and `Pc(ω) = ∫ v ω_e dLⁿ` with `u, v ∈ L¹`, where
`ω_e(x) = ⟨ω(x), e₁ ∧ ⋯ ∧ eₙ⟩`.  Then `X − Pc` is a current `S` with `M(S) ≤ ∫ |u − v| dLⁿ`.
In top degree the Euclidean coefficient norm (Simon Ch. 6, 1.15 and Remark 2.6) of `ω(x)` is
`|ω_e(x)|`, so every form admissible for the mass (2.4) has `|ω_e| ≤ 1` and
`S(ω) = ∫ (u − v) ω_e dLⁿ ≤ ∫ |u − v| dLⁿ`. -/
theorem Submission.fiw_tb_tda_sub_mass : ∀ (m : ℕ) (X Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (u v : Eucl (m + 1) → ℝ), Integrable u → Integrable v → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → ∃ S : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), (∀ ω, X ω - Pc ω = S ω) ∧ S.mass ≤ ∫⁻ x, ENNReal.ofReal |u x - v x| := by
  intro m X Pc u v hu hv hX hPc
  classical
  -- Top degree: the only strictly monotone `I : Fin n → Fin n` is the identity, so the
  -- Euclidean coefficient norm of `α` is `|α(e₁, …, eₙ)|`.
  have hnorm : ∀ α : Covector (Eucl (m + 1)) (m + 1),
      covectorEuclideanNorm α = |α (fun i => EuclideanSpace.single i (1 : ℝ))| := by
    intro α
    unfold covectorEuclideanNorm
    rw [Finset.sum_eq_single (id : Fin (m + 1) → Fin (m + 1))]
    · rw [ite_eq_left strictMono_id]
      simp only [id, EuclideanSpace.basisFun_apply]
      exact Real.sqrt_sq_eq_abs _
    · intro I _ hI
      rw [ite_eq_right]
      intro h
      exact hI h.eq_id
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- `S = X − Pc`; its continuity is the difference of the continuity fields of `X` and `Pc`.
  refine ⟨⟨X.toCurrent - Pc.toCurrent, fun ωs h => by
    simpa using (X.continuous' ωs h).sub (Pc.continuous' ωs h)⟩, fun ω => rfl, ?_⟩
  unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
  refine sSup_le ?_
  rintro b ⟨ω, hω, rfl⟩
  -- For admissible `ω`, `ω_e` is continuous and `|ω_e| ≤ 1`.
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  set f : Eucl (m + 1) → ℝ := fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e with hf
  have hbd : ∀ x, |f x| ≤ 1 := fun x => by
    have := hω.2 x
    rwa [hnorm] at this
  have hωc : Continuous (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) :=
    ω.property.1.1.continuous
  have hfc : Continuous f := hωc.eval_const e
  have hfm : AEStronglyMeasurable f volume := hfc.aestronglyMeasurable
  have hbd' : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ‖f x‖ ≤ 1 :=
    Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hbd x)
  have hu' : Integrable (fun x => u x * f x) := hu.mul_bdd hfm hbd'
  have hv' : Integrable (fun x => v x * f x) := hv.mul_bdd hfm hbd'
  have huv : Integrable (fun x => |u x - v x|) := (hu.sub hv).abs
  -- `S(ω) = ∫ (u − v) ω_e ≤ ∫ |u − v| |ω_e| ≤ ∫ |u − v|`.
  have key : (X.toCurrent - Pc.toCurrent) ω ≤ ∫ x, |u x - v x| := by
    rw [LinearMap.sub_apply]
    change X ω - Pc ω ≤ _
    rw [hX ω, hPc ω, ← integral_sub hu' hv']
    apply integral_mono (hu'.sub hv') huv
    intro x
    calc u x * f x - v x * f x = (u x - v x) * f x := by ring
      _ ≤ |(u x - v x) * f x| := le_abs_self _
      _ = |u x - v x| * |f x| := abs_mul _ _
      _ ≤ |u x - v x| * 1 := mul_le_mul_of_nonneg_left (hbd x) (abs_nonneg _)
      _ = |u x - v x| := mul_one _
  calc ENNReal.ofReal ((X.toCurrent - Pc.toCurrent) ω)
      ≤ ENNReal.ofReal (∫ x, |u x - v x|) := ENNReal.ofReal_le_ofReal key
    _ = ∫⁻ x, ENNReal.ofReal |u x - v x| :=
      ofReal_integral_eq_lintegral_ofReal huv (Eventually.of_forall (fun x => abs_nonneg _))

/-- Summed Poincaré bound over the top-dimensional lattice cubes of `ℝⁿ`, `n = m + 1`, with
`c = (2√n)ⁿ √n`.  A cube lies in the closed ball of radius `√n ρ` about any of its points, so
summing over the a.e. partition into cubes bounds the left side by
`ρ⁻ⁿ ∫⁻ₓ ∫⁻_{B(x, √n ρ)} |u x - u y|`.  The translation estimate bounds this double integral by
`√n ρ Λ L(B(0, √n ρ))`, and `L(B(0, r)) ≤ (2r)ⁿ`. -/
theorem Submission.fiw_tb_tda_poincare_sum :
    ∀ m : ℕ, ∃ c : ℝ≥0, ∀ (ρ : ℝ), 0 < ρ → ∀ (u : Eucl (m + 1) → ℝ) (Λ : ℝ≥0∞), Measurable u →
      (∀ h : Eucl (m + 1), ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) →
      ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        c * ENNReal.ofReal ρ * Λ := by
  intro m
  -- `s = √n` and `c = (2s)ⁿ s`.
  obtain ⟨s, hs, hs_def⟩ : ∃ s : ℝ, 0 ≤ s ∧ Real.sqrt ((m + 1 : ℕ) : ℝ) = s :=
    ⟨_, Real.sqrt_nonneg _, rfl⟩
  have hC : 0 ≤ (2 * s) ^ (m + 1) * s := by positivity
  refine ⟨NNReal.mk ((2 * s) ^ (m + 1) * s) hC, fun ρ hρ u Λ hu hΛ => ?_⟩
  obtain ⟨-, -, hc, -, he, -, hg, -⟩ := Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  rw [hs_def] at he
  have hr : 0 ≤ s * ρ := mul_nonneg hs hρ.le
  -- Step 1: a cube lies in the closed ball of radius `s ρ` about any of its points.
  have hcube : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤
        ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
    fun F => setLIntegral_mono' (hc F) fun x hx =>
      lintegral_mono_set fun y hy => mem_closedBall.2 (he F y hy x hx)
  -- Step 6 (arithmetic): `(ρⁿ)⁻¹ (s ρ) (2 s ρ)ⁿ = (2s)ⁿ s ρ`.
  have hinv : 0 ≤ (ρ ^ (m + 1))⁻¹ := by positivity
  have hconst : (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1) =
      (2 * s) ^ (m + 1) * s * ρ := by
    calc (ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)
        = (2 * s) ^ (m + 1) * s * ρ * ((ρ ^ (m + 1))⁻¹ * ρ ^ (m + 1)) := by ring
      _ = (2 * s) ^ (m + 1) * s * ρ := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), mul_one]
  calc ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y|
      ≤ ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| :=
        ENNReal.tsum_le_tsum fun F => by gcongr _ * ?_; exact hcube F
    -- Step 2: the cubes form an a.e. partition of `ℝⁿ`.
    _ = ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y| := by
        rw [ENNReal.tsum_mul_left, hg]
    -- Steps 3–5: the translation estimate and the volume of the ball.
    _ ≤ ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          (ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1))) := by
        gcongr _ * ?_
        calc ∫⁻ x, ∫⁻ y in closedBall x (s * ρ), ENNReal.ofReal |u x - u y|
            ≤ ENNReal.ofReal (s * ρ) * Λ * volume (closedBall (0 : Eucl (m + 1)) (s * ρ)) :=
              Submission.fiw_tb_tda_ps_translation_ball (m + 1) u Λ (s * ρ) hu hΛ
          _ ≤ ENNReal.ofReal (s * ρ) * Λ * ENNReal.ofReal ((2 * (s * ρ)) ^ (m + 1)) := by
              gcongr _ * ?_
              exact Submission.fiw_tb_tda_ps_ball_volume_le (m + 1) (s * ρ) hr
    -- Step 6: collect the constants.
    _ = ENNReal.ofReal ((ρ ^ (m + 1))⁻¹ * (s * ρ) * (2 * (s * ρ)) ^ (m + 1)) * Λ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hinv hr), ENNReal.ofReal_mul hinv]
        ring
    _ = ENNReal.ofReal ((2 * s) ^ (m + 1) * s) * ENNReal.ofReal ρ * Λ := by
        rw [hconst, ENNReal.ofReal_mul hC]
    _ = _ := by rw [ENNReal.ofReal_eq_coe_nnreal hC]
/-- Simon Ch. 6, 2.11: a current kills every test form whose support misses `spt T`.
`tsupport ω` is a compact subset of the zero region, so finitely many open `W ⊂⊂ U` on which `T`
vanishes cover it, and a smooth partition of unity `ψᵢ` on `tsupport ω` subordinate to them
splits `ω = ∑ᵢ ψᵢ ω` into test forms supported in those `W`. -/
theorem Submission.fiw_tb_apply_eq_zero_of_disjoint_support :
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

/-- **A rectifiable representation lives on the support (Simon Ch. 6, proof of 7.2, (G2)).**
Under the mass formula `M_W(T) = ∫_{M ∩ W} θ dHⁿ` (MF), `T = τ(M, θ, ξ)` has `Hⁿ(M ∖ spt T) = 0`.
Let `V = U ∩ Z`, `Z` the zero region of `T`.  An admissible form for `M_V(T)` is supported in
`V ⊆ Z`, which misses `spt T = U ∖ Z`, so `T` kills it (`fiw_tb_apply_eq_zero_of_disjoint_support`):
`M_V(T) = 0`, and `∫_{M ∩ V} θ dHⁿ = 0` by MF.  For compact `K ⊆ U`, `θ` is integrable on `M ∩ K`,
hence a.e.-measurable, and positive on `M`, so `Hⁿ(M ∩ V ∩ K) = 0`.  The compact sets
`F i ∩ closedBall 0 j` (`F i ⊆ U` closed, `⋃ i, F i = U`) cover `M ∩ V ⊇ M ∖ spt T`. -/
theorem Submission.fiw_tb_rectifiable_support_null : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := by
  intro hMF P n U hU T M θ ξ hM hT
  -- `V = U ∩ Z` is open, and `M ∖ spt T ⊆ M ∩ V` since `M ⊆ U` and `spt T = U ∖ Z`.
  have hV : IsOpen (U ∩ T.zeroRegion) := hU.inter T.isOpen_zeroRegion
  have hsub : M \ T.support ⊆ M ∩ (U ∩ T.zeroRegion) := fun x hx =>
    ⟨hx.1, hM.subset hx.1, Classical.byContradiction fun hxZ => hx.2 ⟨hM.subset hx.1, hxZ⟩⟩
  -- `M_V(T) = 0`: an admissible form is supported in `V ⊆ Z`, which misses `spt T`.
  have hmass : T.massOn (U ∩ T.zeroRegion) = 0 := by
    refine nonpos_iff_eq_zero.1 (sSup_le ?_)
    rintro _ ⟨ω, hω, rfl⟩
    refine (ENNReal.ofReal_eq_zero.2 (le_of_eq ?_)).le
    exact Submission.fiw_tb_apply_eq_zero_of_disjoint_support P n U T ω
      (Set.disjoint_left.2 fun x hxω hxs => hxs.2 (hω.1 hxω).2)
  -- MF with `W = V`: `∫_{M ∩ V} θ dHⁿ = 0`.
  have hint : ∫⁻ x in M ∩ (U ∩ T.zeroRegion), ENNReal.ofReal (θ x)
      ∂(μHE[n] : Measure (Eucl P)) = 0 :=
    (hMF P n U hU T M θ ξ hM hT _ hV).symm.trans hmass
  -- `Hⁿ(M ∩ V ∩ K) = 0` for compact `K ⊆ U`: `θ` is a.e.-measurable there, so `θ = 0` a.e. on
  -- `M ∩ V ∩ K`, while `θ > 0` on `M`.
  have hnull : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      (μHE[n] : Measure (Eucl P)) (M ∩ (U ∩ T.zeroRegion) ∩ K) = 0 := by
    intro K hKc hKU
    have hθ : AEMeasurable (fun x => ENNReal.ofReal (θ x))
        ((μHE[n] : Measure (Eucl P)).restrict (M ∩ (U ∩ T.zeroRegion) ∩ K)) :=
      ((hM.integrableOn K hKc hKU).aestronglyMeasurable.aemeasurable.mono_set
        (fun x hx => ⟨hx.1.1, hx.2⟩ : M ∩ (U ∩ T.zeroRegion) ∩ K ⊆ M ∩ K)).ennreal_ofReal
    have hae := (lintegral_eq_zero_iff' hθ).1
      (nonpos_iff_eq_zero.1 ((lintegral_mono_set inter_subset_left).trans hint.le))
    have h0 : (μHE[n] : Measure (Eucl P)).restrict (M ∩ (U ∩ T.zeroRegion) ∩ K)
        (M ∩ (U ∩ T.zeroRegion) ∩ K) = 0 :=
      measure_mono_null (t := {x | ENNReal.ofReal (θ x) ≠ 0})
        (fun x hx => (ENNReal.ofReal_pos.2 (hM.pos x hx.1.1)).ne') (ae_iff.1 hae)
    rwa [Measure.restrict_apply_self] at h0
  -- The compact sets `F i ∩ closedBall 0 j ⊆ U` (`F i` closed, `⋃ i, F i = U`) cover `M ∩ V`.
  obtain ⟨F, hFc, hFU, hFeq, -⟩ := hU.exists_iUnion_isClosed
  refine measure_mono_null (hsub.trans fun x hx => ?_) (measure_iUnion_null fun k : ℕ × ℕ =>
    hnull _ ((isCompact_closedBall 0 k.2).inter_left (hFc k.1)) (inter_subset_left.trans (hFU k.1)))
  obtain ⟨i, hi⟩ := mem_iUnion.1 (by rw [hFeq]; exact hx.2.1 : x ∈ ⋃ i, F i)
  exact mem_iUnion.2 ⟨(i, ⌈‖x‖⌉₊), hx, hi, mem_closedBall_zero_iff.2 (Nat.le_ceil _)⟩
/-- Simon Ch. 6, 2.4–2.5 and 2.16: restricting `Y ∈ 𝒟ₖ(U)` to a smaller domain `W ⊆ U` does
not increase mass, `M(Y|_W) ≤ M(Y)`.  Every `ω` admissible for `M_W(Y|_W)`, regarded as the
test form `ιω` on `U` with the same underlying form, is admissible for `M_U(Y)`, and
`Y|_W(ω) = Y(ιω)`.  `W` need not be open. -/
theorem Submission.fiw_tb_ri_restrictDomain_mass_le :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U) (Y : GeometricCurrentOn U k),
      (Y.restrictDomain hWU).mass ≤ Y.mass := by
  intro P k U W hWU Y
  -- `(Y|_W).mass` is the supremum of `ofReal (Y|_W ω)` over `ω ∈ massAdmissibleOn W k W`.
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  -- `ιω` has the same underlying form as `ω`, so `tsupport ιω ⊆ W ⊆ U` and `|ιω(x)| ≤ 1`.
  exact Y.le_massOn (omega := testFormOnInclusion hWU k ω) ⟨hω.1.trans hWU, hω.2⟩
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the
proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to
`Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets, `V ∋ x` open.  If `B_δ(x) ⊆ V` and
`f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off
`W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and
`(M', θ')` agree for all small `r`. -/
theorem Submission.br_weightedTangent_congr :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P) (V : Set (Eucl P)),
      IsOpen V → x ∈ V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ y = θ' y) → θ x = θ' x →
      ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k M' θ' x L := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k M M' θ θ' x V hV hxV hMM' hθθ' hθx L hL
  -- `η_r(y) = r⁻¹ (y - x)` maps `Hᵏ`-null sets to `Hᵏ`-null sets: `Hᵏ(η_r Z) = r⁻ᵏ Hᵏ(Z)`.
  have hnull : ∀ r : ℝ, r ≠ 0 → ∀ Z : Set (Eucl P), (μHE[k] : Measure (Eucl P)) Z = 0 →
      (μHE[k] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- A measurable `N ⊇ {θ ≠ θ'}` with `Hᵏ(N ∩ M ∩ V) = 0`.
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hθθ')
  rw [Measure.restrict_apply hNmeas] at hN0
  refine ⟨hL.1, fun f => ?_⟩
  rw [← hθx]
  refine (hL.2 f).congr' ?_
  -- `f = 0` off `B_R(0)` and `B_δ(x) ⊆ V`; the blow-up integrals agree for `0 < r < δ / R`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hcont : Continuous fun y : Eucl P => x + r • y :=
    continuous_const.add (continuous_const_smul r)
  -- `W = η_r(V)` is open and the integrands `f(y) g(x + r y)` vanish off `W`.
  set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' V with hW
  have hWmeas : MeasurableSet W := (hV.preimage hcont).measurableSet
  have hvan : ∀ g : Eucl P → ℝ, ∀ y, y ∉ W → f y * g (x + r • y) = 0 := by
    intro g y hy
    have hfy : f y = 0 := by
      apply hfR
      have h1 : x + r • y ∉ ball x δ := fun h => hy (hδV h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, not_lt] at h1
      rw [lt_div_iff₀ hR] at hrR
      exact le_of_lt (lt_of_mul_lt_mul_left (hrR.trans_le h1) hr0.le)
    rw [hfy, zero_mul]
  -- Cutting by `W`: `∫_{η_r(S)} = ∫_{W ∩ η_r(S)}`.
  have hcut : ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ y in W ∩ blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
    intro S g
    rw [← Measure.restrict_restrict hWmeas,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan g)]
  -- `W ∩ η_r(M) = W ∩ η_r(M')` up to the null set `η_r((M ∆ M') ∩ V)`.
  have hset : W ∩ blowUpMap x r '' M =ᵐ[(μHE[k] : Measure (Eucl P))] W ∩ blowUpMap x r '' M' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inl ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inr ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
  -- `θ(x + r y) = θ'(x + r y)` a.e. on `W ∩ η_r(M)`, off the null set `η_r(N ∩ M ∩ V)`.
  have hae : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (W ∩ blowUpMap x r '' M)),
      f y * θ (x + r • y) = f y * θ' (x + r • y) := by
    have hN'meas : MeasurableSet ((fun y => x + r • y) ⁻¹' N) :=
      hNmeas.preimage hcont.measurable
    rw [ae_iff]
    refine measure_mono_null (t := (fun y => x + r • y) ⁻¹' N) ?_ ?_
    · intro y hy
      by_contra hyN
      apply hy
      have hθy : θ (x + r • y) = θ' (x + r • y) := by
        by_contra hne
        exact hyN (hNsub hne)
      rw [hθy]
    · rw [Measure.restrict_apply hN'meas]
      refine measure_mono_null ?_ (hnull r hr0.ne' _ hN0)
      rintro y ⟨hyN, hyW, z, hzM, rfl⟩
      refine ⟨z, ⟨?_, hzM, ?_⟩, rfl⟩
      · simpa [hinv r hr0.ne' z] using hyN
      · simpa [hW, hinv r hr0.ne' z] using hyW
  calc ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P))
      = ∫ y in W ∩ blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        hcut M θ
    _ = ∫ y in W ∩ blowUpMap x r '' M, f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        integral_congr_ae hae
    _ = ∫ y in W ∩ blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
        rw [Measure.restrict_congr_set hset]
    _ = ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        (hcut M' θ').symm

/-- Simon Ch. 6, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of an integer multiplicity
`Y = τ(M, θ, ξ) ∈ 𝒟ₖ(U)` to an open `W ⊆ U` is the integer multiplicity current
`τ(M ∩ W, θ, ξ)`. -/
theorem Submission.br_restrictDomain_isIntegerMultiplicity :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U), IsOpen W →
      ∀ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y →
        IsIntegerMultiplicity (Y.restrictDomain hWU) := by
  rintro P k U W hWU hW Y ⟨M, θ, ξ, hM, hθ, hY⟩
  have hMW : NullMeasurableSet (M ∩ W) (μHE[k] : Measure (Eucl P)) :=
    hM.nullMeasurableSet.inter hW.measurableSet.nullMeasurableSet
  refine ⟨M ∩ W, θ, ξ,
    { subset := inter_subset_right
      nullMeasurableSet := hMW
      countablyRectifiable := hM.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => hM.pos x hx.1
      integrableOn := fun K hK hKW =>
        (hM.integrableOn K hK (hKW.trans hWU)).mono_set fun y hy => ⟨hy.1.1, hy.2⟩
      aestronglyMeasurable := hM.aestronglyMeasurable.mono_set inter_subset_left
      orients := ?_ }, fun x hx => hθ x hx.1, fun ω => ?_⟩
  · -- `M` and `M ∩ W` agree in the open set `W`, so they have the same weighted approximate
    -- tangent spaces at points of `W`.
    have hnull : symmDiff M (M ∩ W) ∩ W = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_symmDiff, mem_empty_iff_false, iff_false]
      tauto
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hM.orients,
      ae_restrict_mem₀ hMW] with x hxM hx
    obtain ⟨τ, hτ, hTx, hξ⟩ := hxM
    exact ⟨τ, hτ, Submission.br_weightedTangent_congr P k M (M ∩ W) θ θ x W hW hx.2
      (by rw [hnull, measure_empty]) (ae_of_all _ fun _ => rfl) rfl _ hTx, hξ⟩
  · -- A test form on `W` vanishes off `W`, so the integrals over `M` and `M ∩ W` agree.
    have h0 : ∀ x, x ∉ W → θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (ω.property.2 h), map_zero, mul_zero]
    rw [GeometricCurrentOn.restrictDomain_apply, hY]
    simp only [tauAction, testFormOnInclusion_coe]
    rw [inter_comm M W, ← Measure.restrict_restrict hW.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero h0]

/-- Simon Ch. 6, 2.4, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of `Y ∈ 𝒟ₖ(U)` to an open
`W ⊆ U` has `M_W(Y|_W) ≤ M_U(Y)`, since every admissible form for `M_W` is admissible for `M_U`,
and it is integer multiplicity when `Y` is: `Y|_W = τ(M ∩ W, θ, ξ)` for `Y = τ(M, θ, ξ)`. -/
theorem Submission.fiw_tb_restrictDomain_mass_im :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U), IsOpen W →
      ∀ Y : GeometricCurrentOn U k, (Y.restrictDomain hWU).mass ≤ Y.mass ∧
        (IsIntegerMultiplicity Y → IsIntegerMultiplicity (Y.restrictDomain hWU)) := by
  intro P k U W hWU hW Y
  exact ⟨Submission.fiw_tb_ri_restrictDomain_mass_le P k U W hWU Y,
    Submission.br_restrictDomain_isIntegerMultiplicity P k U W hWU hW Y⟩

/-- **Extension of a compactly supported current to `ℝ^P` (Simon Ch. 6, proof of 7.2, (G3)).**
If `spt X ⊆ K` with `K ⊆ U` compact and `M(X) < ∞`, then `Y(ω) = X(χ ω)`, `χ` a smooth cutoff
with `tsupport χ ⊆ U` and `χ = 1` on an open `N ⊇ K`, is a current on `ℝ^P` (`fiw_tb_ext_cutoff`,
`fiw_tb_ext_cutoff_current`).  Since `X` kills test forms whose support misses `K`
(`fiw_tb_apply_eq_zero_of_disjoint_support`) and `χ ω = ω` on `N`, `Y|_U = X`
(`fiw_tb_ext_apply_eq_of_eqOn`); `Y` and `∂Y` kill test forms whose support misses `K`, as
`tsupport (χ ω) ⊆ tsupport ω` and `tsupport dω ⊆ tsupport ω`, and `(∂Y)|_U = ∂X`.  Support,
mass and integer multiplicity of `Y` and `∂Y` are then controlled by those of their restrictions
`X` and `∂X` (`fiw_tb_ext_support_subset`, `fiw_tb_ext_mass_le_restrictDomain`,
`fiw_tb_ext_isIntegerMultiplicity`).  The mass formula (MF) is not needed. -/
theorem Submission.fiw_tb_extend_to_univ : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P m : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ X : GeometricCurrentOn U (m + 1), X.support ⊆ K → X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧ (IsIntegerMultiplicity X.boundary → IsIntegerMultiplicity Y.boundary) := by
  intro _hMF P m U K hU hK hKU X hXK hXm
  -- (V) for `X`: as `spt X ⊆ K`, `X` kills every test form whose support misses `K`.
  have hXv : ∀ ω : TestFormOn U (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) K → X ω = 0 := fun ω hω =>
    Submission.fiw_tb_apply_eq_zero_of_disjoint_support P (m + 1) U X ω (hω.mono_right hXK)
  -- The cutoff `χ` and multiplication by `χ`, from test forms on `ℝ^P` and on `U` to `U`.
  obtain ⟨χ, N, hχ, hχ01, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P (m + 1) univ U χ hχ hχU
  obtain ⟨LU, hLU⟩ := Submission.fiw_tb_ext_smul_testForm P (m + 1) U U χ hχ hχU
  -- `Y(ω) = X(χ ω)` is a current on `ℝ^P`, since `M(X) < ∞` and `|χ| ≤ 1`.
  obtain ⟨Y, hY⟩ := Submission.fiw_tb_ext_cutoff_current P (m + 1) U χ hχ hχU
    (fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩) X hXm
  -- `Y|_U = X`: `Y(ω) = X(χ ω) = X(ω)`, as `χ ω = ω` on `N ⊇ K`.
  have hres : Y.restrictDomain (subset_univ U) = X := by
    ext ω
    rw [GeometricCurrentOn.restrictDomain_apply,
      hY (testFormOnInclusion (subset_univ U) (m + 1) ω) (LU ω) (hLU ω)]
    exact Submission.fiw_tb_ext_apply_eq_of_eqOn P (m + 1) U K N X hN hKN hXv ω (LU ω)
      fun x hx => by rw [hLU, hχN x hx, one_smul]
  -- (V) for `Y`: `Y(ω) = X(χ ω)` and `tsupport (χ ω) ⊆ tsupport ω`.
  have hYv : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) K → Y ω = 0 := by
    intro ω hω
    rw [hY ω (L ω) (hL ω)]
    refine hXv (L ω) (hω.mono_left ?_)
    rw [show (L ω : DifferentialForm (Eucl P) (m + 1)) =
      fun x => χ x • (ω : DifferentialForm (Eucl P) (m + 1)) x from funext (hL ω)]
    exact tsupport_smul_subset_right _ _
  -- (V) for `∂Y`, as `tsupport dω ⊆ tsupport ω`; and `(∂Y)|_U = ∂X`, as `d` commutes with the
  -- inclusion of test forms on `U` into test forms on `ℝ^P`.
  have hbYv : ∀ ω : TestFormOn (univ : Set (Eucl P)) m,
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) m)) K → Y.boundary ω = 0 := fun ω hω =>
    hYv _ (hω.mono_left (tsupport_exteriorDerivative_subset _))
  have hbres : Y.boundary.restrictDomain (subset_univ U) = X.boundary := by
    rw [← hres]
    rfl
  refine ⟨Y, hres, Submission.fiw_tb_ext_support_subset P (m + 1) univ K Y isOpen_univ
    hK.isClosed hYv, ?_, ?_, fun hX => ?_, fun hX => ?_⟩
  · -- `M(Y) ≤ M(Y|_U) = M(X)`.
    rw [← hres]
    exact Submission.fiw_tb_ext_mass_le_restrictDomain P (m + 1) U K hU hK hKU Y hYv
  · -- `M(∂Y) ≤ M((∂Y)|_U) = M(∂X)`.
    rw [← hbres]
    exact Submission.fiw_tb_ext_mass_le_restrictDomain P m U K hU hK hKU Y.boundary hbYv
  · rw [← hres] at hX
    exact Submission.fiw_tb_ext_isIntegerMultiplicity P (m + 1) U K hU hK hKU Y hYv hX
  · rw [← hbres] at hX
    exact Submission.fiw_tb_ext_isIntegerMultiplicity P m U K hU hK hKU Y.boundary hbYv hX
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
/-- The `n`-dimensional coordinate box `{x : c_i + a ≤ x_i ≤ c_i + b (i ∈ range α), x_i = c_i
(i ∉ range α)}` in `ℝ^N` has `μHE[n]`-measure `(b - a)^n`.  The map
`ι(y)_i = c_i + ∑_j [α j = i] y_j` is an isometry `ℝⁿ → ℝ^N` carrying the cube `[a, b]ⁿ` onto the
box; `μHE[n]` is invariant under isometries and equals Lebesgue measure on `ℝⁿ`. -/
theorem Submission.isoperimetric_coord_box_measure :
    ∀ (n N : ℕ) (α : SimonMultiIndex n N) (c : Fin N → ℝ) (a b : ℝ), a ≤ b →
      (μHE[n] : Measure (Eucl N)) {x : Eucl N | ∀ i : Fin N,
        (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧ (i ∉ range α → x i = c i)} =
        ENNReal.ofReal ((b - a) ^ n) := by
  intro n N α c a b hab
  classical
  -- The parametrization `ι(y)_i = c_i + ∑_j [α j = i] y_j` of the box.
  set ι : EuclideanSpace ℝ (Fin n) → Eucl N :=
    fun y => WithLp.toLp 2 (fun i => c i + ∑ j, if α j = i then y j else 0) with hι
  have hι_on : ∀ y j, ι y (α j) = c (α j) + y j := by
    intro y j
    simp only [hι, PiLp.toLp_apply, α.inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hι_off : ∀ y i, i ∉ range α → ι y i = c i := by
    intro y i hi
    have hne : ∀ j, α j ≠ i := fun j hj => hi ⟨j, hj⟩
    simp [hι, hne]
  -- `ι` is an isometry: coordinates off `range α` agree, the others reindex along `α`.
  have hiso : Isometry ι := by
    refine Isometry.of_dist_eq fun y y' => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
/-- Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Z) < ∞` and `|η(x)| ≤ c` everywhere (Euclidean
coefficient norm) with `c > 0`, then `|Z(η)| ≤ c · M(Z)`. -/
theorem Submission.fiw_tb_te_abs_apply_le_mul_mass :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U n) (η : TestFormOn U n) (c : ℝ),
      0 < c → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ c) →
      Z.mass ≠ ∞ → |Z η| ≤ c * Z.mass.toReal := by
  intro P n U Z η c hc hη hZ
  -- Homogeneity of the Euclidean coefficient norm: `|t β| = |t| |β|`.
  have hsmul : ∀ (t : ℝ) (β : Covector (Eucl P) n),
      covectorEuclideanNorm (t • β) = |t| * covectorEuclideanNorm β := by
    intro t β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image α)) ?_,
      Finset.sum_image (fun j _ j' _ h => α.injective h)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hι_on, hι_on, dist_add_left]
    · intro i _ hi
      have hi' : i ∉ range α := by
        rintro ⟨j, rfl⟩
        exact hi (Finset.mem_image_of_mem α (Finset.mem_univ j))
      rw [hι_off y i hi', hι_off y' i hi', dist_self]
      ring
  -- `ι` maps the cube `[a, b]ⁿ` onto the box, with preimage `y_j = x_{α j} - c_{α j}`.
  have himage : ι '' {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      {x : Eucl N | ∀ i : Fin N, (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧
        (i ∉ range α → x i = c i)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨?_, hι_off y i⟩
      rintro ⟨j, rfl⟩
      rw [hι_on]
      exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
    · intro hx
      refine ⟨WithLp.toLp 2 (fun j => x (α j) - c (α j)), fun j => ?_, ?_⟩
      · have h := (hx (α j)).1 ⟨j, rfl⟩
        constructor <;> dsimp only <;> linarith [h.1, h.2]
      · ext i
        by_cases hi : i ∈ range α
        · obtain ⟨j, rfl⟩ := hi
          rw [hι_on]
          simp
        · rw [hι_off _ i hi, (hx i).2 hi]
  rw [← himage, hiso.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- The cube is the preimage of `Icc` under the volume-preserving `WithLp.ofLp`.
  have hQ : {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => a) (fun _ => b) := by
    ext y
    simp [Pi.le_def, forall_and]
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (sub_nonneg.2 hab)]
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

/-- A mass-admissible test form isolating one lattice face: for `ρ > 0`, `0 < δ < 1/4` and the
face `F₀ = ρ(z + F_α)`, the form `ω = φ dx^α` (`φ` the cut-off of `F₀`) has `[[F]](ω) = 0` for every
other face `F` (`dx^α` kills the faces of other directions, `φ` those of direction `α`), and
`[[F₀]](ω) = ∫_{F₀} φ dHⁿ ≥ Hⁿ(K) = (ρ(1 − 2δ))^n`, `K` the shrunken face where `φ = 1`. -/
theorem Submission.isoperimetric_lattice_face_isolating_form :
    ∀ (n N : ℕ) (ρ δ : ℝ) (F₀ : LatticeFaceIndex n N), 0 < ρ → 0 < δ → δ < 1 / 4 →
      ∃ ω : TestFormOn (univ : Set (Eucl N)) n, ω ∈ massAdmissibleOn (univ : Set (Eucl N)) n univ ∧
        (∀ F : LatticeFaceIndex n N, F ≠ F₀ →
          latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧
        (ρ * (1 - 2 * δ)) ^ n ≤ latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ δ F₀ hρ hδ hδ'
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the coordinate covector `η = dx^α` and the cut-off `φ` of the face `(z, α)`.
  obtain ⟨hηα, hηne, hηnorm⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ δ z α hρ hδ
  -- Step 2: the test form `ω = φ • η`, smooth with compact support.
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ x, (ω : DifferentialForm (Eucl N) n) x = φ x • η :=
    ⟨⟨fun x => φ x • η, ⟨hφs.smul contDiff_const, hφc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ x (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) x v = φ x * η v :=
    fun x v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ⟨subset_univ _, fun x => ?_⟩, ?_, ?_⟩
  -- Step 3: admissibility, `|ω(x)| = |φ(x)| ≤ 1`.
  · rw [hωx, hηnorm, abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- Step 4: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · -- same direction: `z' ≠ z`, and `φ = 0` on the face `(z', α)`.
      have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [hωv, hφ0 z' hz x (by rwa [hα] at hx), zero_mul]
    · -- other direction: `η(e_{α'}) = 0`.
      simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Steps 5–8: the face `F₀`.
  · set K : Set (Eucl N) := {x | ∀ i : Fin N,
      (i ∈ range α → ρ * ((z i : ℝ) + δ) ≤ x i ∧ x i ≤ ρ * ((z i : ℝ) + 1 - δ)) ∧
      (i ∉ range α → x i = ρ * (z i : ℝ))} with hK
    -- Step 6: both `F₀` and `K` are coordinate boxes with base point `c_i = ρ z_i`.
    have hFmeas : (μHE[n] : Measure (Eucl N)) (latticeFace ρ ((z, α) : LatticeFaceIndex n N)) =
        ENNReal.ofReal (ρ ^ n) := by
      convert Submission.isoperimetric_coord_box_measure n N α (fun i => ρ * (z i : ℝ)) 0 ρ
        hρ.le using 2
      · ext x
        simp only [latticeFace, mem_ofPred_eq, add_zero, mul_add, mul_one]
      · rw [sub_zero]
    have hKmeas : (μHE[n] : Measure (Eucl N)) K = ENNReal.ofReal ((ρ * (1 - 2 * δ)) ^ n) := by
      convert Submission.isoperimetric_coord_box_measure n N α (fun i => ρ * (z i : ℝ)) (ρ * δ)
        (ρ * (1 - δ)) (by nlinarith) using 2
      · ext x
        simp only [hK, mem_ofPred_eq, mul_add, mul_sub, mul_one, add_sub_assoc]
      · ring
    -- Step 7: `K ⊆ F₀`, `K` is closed, and `φ` is integrable on `F₀`.
    have hKsub : K ⊆ latticeFace ρ ((z, α) : LatticeFaceIndex n N) := by
      intro x hx i
      refine ⟨fun hi => ?_, (hx i).2⟩
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      constructor <;> nlinarith
    have hc : ∀ i : Fin N, Continuous fun x : Eucl N => x i := fun i => PiLp.continuous_apply 2 _ i
    have hKc : IsClosed K := by
      rw [hK, ofPred_forall]
      refine isClosed_iInter fun i => ?_
      by_cases hi : i ∈ range α
      · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
        exact (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)
      · simp only [hi, IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
        exact isClosed_eq (hc i) continuous_const
    have hint : IntegrableOn φ (latticeFace ρ ((z, α) : LatticeFaceIndex n N))
        (μHE[n] : Measure (Eucl N)) :=
      Measure.integrableOn_of_bounded (M := 1) (by rw [hFmeas]; exact ENNReal.ofReal_ne_top)
        hφs.continuous.aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 x).1]; exact (hφ01 x).2)
    -- Step 8: `(ρ(1 − 2δ))^n = Hⁿ(K) = ∫_K φ ≤ ∫_{F₀} φ = [[F₀]](ω)`.
    calc (ρ * (1 - 2 * δ)) ^ n
        = ((μHE[n] : Measure (Eucl N)) K).toReal := by
          rw [hKmeas, ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg hρ.le (by linarith)) n)]
      _ = ∫ _ in K, (1 : ℝ) ∂(μHE[n] : Measure (Eucl N)) := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = ∫ x in K, φ x ∂(μHE[n] : Measure (Eucl N)) :=
          setIntegral_congr_fun hKc.measurableSet fun x hx => (hφ1 x hx).symm
      _ ≤ ∫ x in latticeFace ρ ((z, α) : LatticeFaceIndex n N), φ x ∂(μHE[n] : Measure (Eucl N)) :=
          setIntegral_mono_set hint (ae_of_all _ fun x => (hφ01 x).1)
            (Filter.EventuallySubset.of_subset hKsub)
      _ = latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N)
            (ω : DifferentialForm (Eucl N) n) := by
          simp only [latticeFaceAction, hωv, hηα, mul_one]

/-- Simon Ch. 6, proof of 6.1, (1) (p. 169): a lattice chain `Pc = ∑_F β_F [[F]]` in `ℝ^N` has
mass at least `|β_F| ρ^{m+1}` for every face `F` (`H^{m+1}(F) = ρ^{m+1}`).  For `0 < δ < 1/4`
the isolating form `ω` of `F` kills every other face, so testing `Pc` with `±ω` gives
`M(Pc) ≥ |β_F| [[F]](ω) ≥ |β_F| (ρ (1 - 2δ))^{m+1}`; then let `δ → 0⁺`. -/
theorem Submission.isoperimetric_lattice_chain_mass_ge :
    ∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ)
      (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc →
      ∀ F : LatticeFaceIndex (m + 1) N, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass := by
  intro m N ρ β Pc hρ hPc F₀
  -- Step 1: for `0 < δ < 1/4`, the bound with `ρ` replaced by `ρ (1 - 2δ)`.
  have hδ_bound : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
      ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)) ≤ Pc.mass := by
    intro δ hδ hδ'
    obtain ⟨ω, hadm, hoff, hlb⟩ :=
      Submission.isoperimetric_lattice_face_isolating_form (m + 1) N ρ δ F₀ hρ hδ hδ'
    -- Only `F₀` contributes to the lattice sum.
    have hPcω :
        Pc ω = β F₀ * latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) (m + 1)) := by
      rw [hPc ω, tsum_eq_single F₀ fun F hF => by rw [hoff F hF, mul_zero]]
    -- `-ω` is admissible as well, and `Pc(-ω) = -Pc(ω)`.
    have hadm' : -ω ∈ massAdmissibleOn (univ : Set (Eucl N)) (m + 1) univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
      exact hadm.2 x
    have hPcneg : Pc (-ω) = -Pc ω := map_neg Pc.toCurrent ω
    -- Test with `ω` if `β F₀ ≥ 0` and with `-ω` otherwise.
    rcases le_or_gt 0 (β F₀) with hβ | hβ
    · calc ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1))
          ≤ ENNReal.ofReal (Pc ω) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hPcω, abs_of_nonneg hβ]
            exact mul_le_mul_of_nonneg_left hlb hβ
        _ ≤ Pc.mass := Pc.le_massOn hadm
    · calc ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1))
          ≤ ENNReal.ofReal (Pc (-ω)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hPcneg, hPcω, abs_of_neg hβ, ← neg_mul]
            exact mul_le_mul_of_nonneg_left hlb (neg_nonneg.2 hβ.le)
        _ ≤ Pc.mass := Pc.le_massOn hadm'
  -- Step 2: let `δ → 0⁺`; the left-hand side is continuous in `δ`.
  have hc : Continuous fun δ : ℝ => ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (|β F₀| * (ρ * (1 - 2 * δ)) ^ (m + 1)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (|β F₀| * ρ ^ (m + 1)))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
    fun δ hδ => hδ_bound δ hδ.1 hδ.2)
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

/-- Simon Ch. 6, proof of 7.2, (2) (p. 171): every face `F` of a lattice chain
`Pc = ∑_F β_F [[F]]` in `ℝ^N` with `β_F ≠ 0` lies in `spt Pc`, and `|β_F| ρ^{m+1} ≤ M(Pc)`.  If a
point `x ∈ F` were outside `spt Pc`, then `Pc` would vanish on some open `W ∋ x`; the isolating
form `ω` of `F` localized at `x` (`tsupport ω ⊆ W`, `[[G]](ω) = 0` for `G ≠ F`, `[[F]](ω) > 0`)
would give `0 = Pc(ω) = β_F [[F]](ω) ≠ 0`.  The mass bound is
`isoperimetric_lattice_chain_mass_ge`. -/
theorem Submission.fiw_tb_lattice_chain_coeff : ∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ) (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc → ∀ F : LatticeFaceIndex (m + 1) N, β F ≠ 0 → latticeFace ρ F ⊆ Pc.support ∧ ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass := by
  intro m N ρ β Pc hρ hPc F hF
  refine ⟨fun x hx => ?_, Submission.isoperimetric_lattice_chain_mass_ge m N ρ β Pc hρ hPc F⟩
  -- Otherwise `x` lies in the zero region: some open `W ∋ x` on which `Pc` vanishes.
  by_contra hxs
  have hxz : x ∈ Pc.zeroRegion := by
    by_contra h
    exact hxs ⟨mem_univ x, h⟩
  obtain ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩ := hxz
  -- The isolating form of `F` localized at `x` is supported in `W`, so `Pc` kills it.
  obtain ⟨ω, hωW, hoff, hpos⟩ :=
    Submission.fiw_tb_lcc_local_isolating_form (m + 1) N ρ F x W hρ hx hWo hxW
  have h1 : Pc ω = 0 := hWv ω hωW
  -- Only `F` contributes to the lattice sum, so `Pc ω = β_F [[F]](ω) ≠ 0`.
  have h2 : Pc ω = β F * latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) (m + 1)) := by
    rw [hPc ω, tsum_eq_single F fun G hG => by rw [hoff G hG, mul_zero]]
  exact mul_ne_zero hF hpos.ne' (h2 ▸ h1)
/-- Simon Ch. 6, proof of 7.2 (p. 171, "only finitely many currents `P` as in (2)"): for `ρ > 0`,
a bounded `Y ⊆ ℝ^N` and `A ∈ ℝ`, only finitely many integer coefficient families `β` have the
face `F` inside `Y` and `|β_F| ≤ A` whenever `β_F ≠ 0`. -/
theorem Submission.fiw_tb_lattice_coeff_finite :
    ∀ (n N : ℕ) (ρ : ℝ), 0 < ρ → ∀ (Y : Set (Eucl N)), Bornology.IsBounded Y → ∀ A : ℝ,
      {β : LatticeFaceIndex n N → ℝ | (∀ F, ∃ k : ℤ, β F = k) ∧
        ∀ F, β F ≠ 0 → latticeFace ρ F ⊆ Y ∧ |β F| ≤ A}.Finite := by
  intro n N ρ hρ Y hY A
  -- Faces inside `Y`: the vertex `ρ z` of the face `(z, α)` lies in `Y ⊆ closedBall 0 R`, so
  -- `z` lies in a finite box, and `α` ranges over a finite type.
  obtain ⟨R, hR⟩ := hY.subset_closedBall 0
  have hS : {F : LatticeFaceIndex n N | latticeFace ρ F ⊆ Y}.Finite := by
    refine ((Set.Finite.pi fun _ : Fin N => Set.finite_Icc (-⌈R / ρ⌉) ⌈R / ρ⌉).prod
      Set.finite_univ).subset ?_
    rintro ⟨z, α⟩ hF
    refine ⟨fun i _ => ?_, Set.mem_univ _⟩
    have hv : (WithLp.toLp 2 fun i => ρ * (z i : ℝ) : Eucl N) ∈ latticeFace ρ (z, α) :=
      fun j => ⟨fun _ => ⟨le_rfl, mul_le_mul_of_nonneg_left (by linarith) hρ.le⟩, fun _ => rfl⟩
    have hi := (PiLp.norm_apply_le _ i).trans (mem_closedBall_zero_iff.mp (hR (hF hv)))
    rw [PiLp.toLp_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hρ] at hi
    have hz : |(z i : ℝ)| ≤ R / ρ := by
      rw [le_div_iff₀ hρ]
      linarith
    have hc := Int.le_ceil (R / ρ)
    obtain ⟨h1, h2⟩ := abs_le.mp hz
    constructor
    · have : ((-⌈R / ρ⌉ : ℤ) : ℝ) ≤ z i := by push_cast; linarith
      exact_mod_cast this
    · have : (z i : ℝ) ≤ ((⌈R / ρ⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  -- Admissible values: integers of absolute value at most `|A|` (this includes `0`).
  have hV : {x : ℝ | (∃ k : ℤ, x = k) ∧ |x| ≤ |A|}.Finite := by
    refine ((Set.finite_Icc (-⌈|A|⌉) ⌈|A|⌉).image fun k : ℤ => (k : ℝ)).subset ?_
    rintro x ⟨⟨k, rfl⟩, hx⟩
    have hc := Int.le_ceil |A|
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · have : ((-⌈|A|⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
      exact_mod_cast this
    · have : (k : ℝ) ≤ ((⌈|A|⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  -- Restriction to the faces inside `Y` maps the set into the finite set of maps into the
  -- admissible values, and is injective on it since every `β` in it vanishes off these faces.
  have := hS.to_subtype
  refine Set.Finite.of_finite_image
    (f := fun β (F : {F : LatticeFaceIndex n N | latticeFace ρ F ⊆ Y}) => β F) ?_ ?_
  · refine (Set.Finite.pi' fun _ => hV).subset ?_
    rintro _ ⟨β, ⟨hint, hsupp⟩, rfl⟩ F
    dsimp only
    refine ⟨hint F, ?_⟩
    by_cases h : β F = 0
    · rw [h, abs_zero]
      exact abs_nonneg A
    · exact (hsupp F h).2.trans (le_abs_self A)
  · rintro β ⟨-, hsupp⟩ β' ⟨-, hsupp'⟩ h
    funext F
    by_cases hF : latticeFace ρ F ⊆ Y
    · exact congrFun h ⟨F, hF⟩
    · have h0 : β F = 0 := by
        by_contra h'
        exact hF (hsupp F h').1
      have h0' : β' F = 0 := by
        by_contra h'
        exact hF (hsupp' F h').1
      rw [h0, h0']
/-- Simon Ch. 6, proof of 7.2 (translation estimate): for `φ ∈ C_c^∞(ℝⁿ)`, `n = m + 1`, and
`h ∈ ℝⁿ`, the test `m`-form `ω = φ α` with `α = ∑ₖ (-1)ᵏ hₖ dx⁽ᵏ⁾`, where `dx⁽ᵏ⁾` is the wedge of
the coordinate covectors `dxʲ`, `j ≠ k`, in increasing order (indices `0, …, m`), satisfies
`|ω(x)| = ‖h‖ |φ(x)|` and `dω(x)(e₀, …, eₘ) = ∑ᵢ hᵢ ∂ᵢφ(x) = Dφ(x) h`. -/
theorem Submission.fiw_tb_te_directional_form :
    ∀ (m : ℕ) (φ : Eucl (m + 1) → ℝ) (h : Eucl (m + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∃ ω : TestFormOn (univ : Set (Eucl (m + 1))) m,
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ ‖h‖ * |φ x|) ∧
        ∀ x, ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) m ω :
            TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1))
          x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h := by
  intro m φ h hφ hcs
  -- The coordinate `m`-covector omitting direction `k`, on the frame omitting `eᵢ`, is `δₖᵢ`.
  have hcoord : ∀ k i : Fin (m + 1),
      (wedgeCovectors m (fun a => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ)))
        (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = if k = i then 1 else 0 := by
    intro k i
    rw [wedgeCovectors_apply_det]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl]
      have hM : (Matrix.of fun a b => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ)
          (EuclideanSpace.single (k.succAbove b) (1 : ℝ))) = 1 := by
        ext a b
        simp [Matrix.one_apply]
      rw [hM, Matrix.det_one]
    · -- `i = k.succAbove a₀` for some `a₀`, and row `a₀` of the matrix vanishes.
      rw [ite_eq_right hki]
      obtain ⟨a₀, ha₀⟩ : i ∈ Set.range k.succAbove := by
        rw [Fin.range_succAbove]; exact Ne.symm hki
      apply Matrix.det_eq_zero_of_row_eq_zero a₀
      intro b
      simp [ha₀, (Fin.succAbove_ne i b).symm]
  -- The strictly increasing `I : Fin m → Fin (m + 1)` are exactly the maps `k.succAbove`.
  have hincr : ∀ I : Fin m → Fin (m + 1), StrictMono I → ∃ k : Fin (m + 1), I = k.succAbove := by
    intro I hI
    have hinj := hI.injective
    have hns : ¬ Function.Surjective I := by
      intro hs
      have := Fintype.card_le_of_surjective I hs
      simp at this
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨k, hk⟩ := hns
    refine ⟨k, ?_⟩
    have hsub : Set.range I ⊆ Set.range k.succAbove := by
      rw [Fin.range_succAbove]
      rintro _ ⟨a, rfl⟩
      exact hk a
    have hcard : (Set.range k.succAbove).ncard ≤ (Set.range I).ncard := by
      rw [Set.ncard_range_of_injective hinj,
        Set.ncard_range_of_injective Fin.succAbove_right_injective]
    have heq : Set.range I = Set.range k.succAbove := Set.eq_of_subset_of_ncard_le hsub hcard
    exact (StrictMono.range_inj_of_wellFoundedLT hI (Fin.strictMono_succAbove k)).1 heq
  -- The constant covector `α` with `α(e ∘ i.succAbove) = (-1)ⁱ hᵢ`.
  set α : Covector (Eucl (m + 1)) m := ∑ k : Fin (m + 1), ((-1 : ℝ) ^ (k : ℕ) * h k) •
    wedgeCovectors m (fun a => (EuclideanSpace.proj (k.succAbove a) : Eucl (m + 1) →L[ℝ] ℝ))
    with hα
  have hαe : ∀ i : Fin (m + 1),
      α (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = (-1 : ℝ) ^ (i : ℕ) * h i := by
    intro i
    simp only [hα, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hcoord, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  -- `ω₀ = φ α` is a test form on `univ`.
  set ω₀ : DifferentialForm (Eucl (m + 1)) m := fun y => φ y • α with hω₀
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω₀ := hφ.smul contDiff_const
  have hcs₀ : HasCompactSupport ω₀ := hcs.smul_right
  have hmem : ω₀ ∈ testFormOnSubmodule (univ : Set (Eucl (m + 1))) m :=
    ⟨⟨hsmooth, hcs₀⟩, subset_univ _⟩
  refine ⟨⟨ω₀, hmem⟩, ?_, ?_⟩
  · -- Norm: reindex the increasing multi-indices by `k ↦ k.succAbove`; then `|ω₀(x)| = |φ(x)| ‖h‖`.
    intro x
    apply le_of_eq
    change covectorEuclideanNorm (φ x • α) = ‖h‖ * |φ x|
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin m → Fin (m + 1),
        if StrictMono I then
          ((φ x • α) (fun i ↦ EuclideanSpace.basisFun (Fin (m + 1)) ℝ (I i))) ^ 2
        else 0) = ∑ k : Fin (m + 1), (φ x) ^ 2 * (h k) ^ 2 := by
      symm
      apply Fintype.sum_of_injective (fun k : Fin (m + 1) => k.succAbove)
        Fin.succAbove_left_injective
      · intro I hI
        rw [ite_eq_right]
        intro hmono
        obtain ⟨k, rfl⟩ := hincr I hmono
        exact hI ⟨k, rfl⟩
      · intro k
        simp only [Fin.strictMono_succAbove, ite_true, EuclideanSpace.basisFun_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        rw [hαe k, mul_pow, mul_pow, ← pow_mul, mul_comm (k : ℕ) 2, pow_mul]
        norm_num
    rw [hsum, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      EuclideanSpace.norm_eq, mul_comm]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.norm_eq_abs, sq_abs]
  · -- Exterior derivative: `dω₀(x)(e) = ∑ᵢ (-1)ⁱ (-1)ⁱ hᵢ Dφ(x) eᵢ = Dφ(x) h`.
    intro x
    change exteriorDerivative ω₀ x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h
    have hdiff : DifferentiableAt ℝ ω₀ x := (hsmooth.differentiable (by simp)).differentiableAt
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply hdiff]
    have key : ∀ i : Fin (m + 1),
        (fun y => ω₀ y (i.removeNth (fun j => EuclideanSpace.single j (1 : ℝ)))) =
          fun y => ((-1 : ℝ) ^ (i : ℕ) * h i) * φ y := by
      intro i
      funext y
      change (φ y • α) (fun b => EuclideanSpace.single (i.succAbove b) (1 : ℝ)) = _
      rw [ContinuousAlternatingMap.smul_apply, hαe i, smul_eq_mul, mul_comm]
    have hstep : ∀ i : Fin (m + 1),
        (-1 : ℤ) ^ (i : ℕ) • fderiv ℝ
            (fun y => ω₀ y (i.removeNth (fun j => EuclideanSpace.single j (1 : ℝ)))) x
            (EuclideanSpace.single i (1 : ℝ)) =
          h i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
      intro i
      rw [key i, fderiv_const_mul hφd]
      simp only [smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, smul_eq_mul]
/-- Weak translation estimate: if `|∫ u · Dφ(h)| ≤ B` for every `C^∞` compactly supported `φ`
with `|φ| ≤ 1`, then `|∫ (u(· + h) − u) · g| ≤ B` for every such `g`.  For `φ_t = g(· − t h)`,
`F(t) = ∫ u(y) g(y − t h) dy` has `F'(t) = −∫ u(y) Dφ_t(y)(h) dy`, so `|F'| ≤ B`, and
`F(1) − F(0) = ∫ (u(x + h) − u(x)) g(x) dx` by translation invariance. -/
theorem Submission.fiw_tb_te_translation_dual :
    ∀ (n : ℕ) (u : Eucl n → ℝ) (h : Eucl n) (B : ℝ), Integrable u →
      (∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, |φ x| ≤ 1) → |∫ x, u x * fderiv ℝ φ x h| ≤ B) →
      ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        (∀ x, |g x| ≤ 1) → |∫ x, (u (x + h) - u x) * g x| ≤ B := by
  intro n u h B hu hB g hg hgc hg1
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- `Dg` is continuous with compact support, hence bounded.
  obtain ⟨K, hK⟩ := (hg.continuous_fderiv hn).bounded_above_of_compact_support (hgc.fderiv ℝ)
  have hcont : ∀ t : ℝ, Continuous fun y : Eucl n => g (y - t • h) := fun t =>
    hg.continuous.comp (continuous_id.sub continuous_const)
  have hcont' : ∀ t : ℝ, Continuous fun y : Eucl n => fderiv ℝ g (y - t • h) (-h) := fun t =>
    ((hg.continuous_fderiv hn).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const
  have hgle : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure (Eucl n)), ‖g (y - t • h)‖ ≤ 1 := fun t =>
    ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hg1 _
  -- Differentiation under the integral sign, dominated by `‖u‖ K ‖h‖`:
  -- `d/dt ∫ u(y) g(y - t h) dy = ∫ u(y) Dg(y - t h)(-h) dy`.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ∫ y, u y * g (y - s • h))
      (∫ y, u y * fderiv ℝ g (y - t • h) (-h)) t := by
    intro t
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
      (F := fun s y => u y * g (y - s • h)) (F' := fun s y => u y * fderiv ℝ g (y - s • h) (-h))
      (bound := fun y => ‖u y‖ * (K * ‖h‖)) Filter.univ_mem
      (Filter.Eventually.of_forall fun s => hu.aestronglyMeasurable.mul
        (hcont s).aestronglyMeasurable)
      (hu.mul_bdd (hcont t).aestronglyMeasurable (hgle t))
      (hu.aestronglyMeasurable.mul (hcont' t).aestronglyMeasurable)
      (ae_of_all _ fun y s _ => ?_) (hu.norm.mul_const _) (ae_of_all _ fun y s _ => ?_)).2
    · rw [norm_mul]
      gcongr
      calc ‖fderiv ℝ g (y - s • h) (-h)‖ ≤ K * ‖-h‖ :=
            (fderiv ℝ g (y - s • h)).le_of_opNorm_le (hK _) (-h)
        _ = K * ‖h‖ := by rw [norm_neg]
    · have hline : HasDerivAt (fun s : ℝ => y - s • h) (-h) s := by
        simpa using ((hasDerivAt_id s).smul_const h).const_sub y
      exact ((hg.differentiable hn (y - s • h)).hasFDerivAt.comp_hasDerivAt s hline).const_mul (u y)
  -- Each derivative is bounded by `B`: apply the hypothesis to `φ_t = g(· - t h)`.
  have hbound : ∀ t : ℝ, ‖∫ y, u y * fderiv ℝ g (y - t • h) (-h)‖ ≤ B := by
    intro t
    have hφ := hB (fun y => g (y - t • h)) (hg.comp (contDiff_id.sub contDiff_const))
      (hgc.comp_homeomorph (Homeomorph.subRight (t • h))) (fun y => hg1 _)
    simp only [fderiv_comp_sub] at hφ
    have heq : ∫ y, u y * fderiv ℝ g (y - t • h) (-h) = -∫ y, u y * fderiv ℝ g (y - t • h) h := by
      rw [← integral_neg]
      simp only [map_neg, mul_neg]
    rw [heq, norm_neg, Real.norm_eq_abs]
    exact hφ
  -- Mean value inequality on `[0, 1]`.
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => ∫ y, u y * g (y - s • h))
    (fun t _ => (hderiv t).hasDerivWithinAt) (fun t _ => hbound t)
  -- Identify the endpoints, using translation invariance of Lebesgue measure.
  have h1 : ∫ y, u y * g (y - (1 : ℝ) • h) = ∫ x, u (x + h) * g x := by
    rw [one_smul, ← integral_add_right_eq_self (μ := volume) (fun y => u y * g (y - h)) h]
    simp only [add_sub_cancel_right]
  have h0 : ∫ y, u y * g (y - (0 : ℝ) • h) = ∫ x, u x * g x := by
    simp only [zero_smul, sub_zero]
  have hint1 : Integrable fun x => u (x + h) * g x := by
    simpa using (hu.comp_add_right h).mul_bdd (hcont 0).aestronglyMeasurable (hgle 0)
  have hint0 : Integrable fun x => u x * g x := by
    simpa using hu.mul_bdd (hcont 0).aestronglyMeasurable (hgle 0)
  have hJ : ∫ x, (u (x + h) - u x) * g x = (∫ x, u (x + h) * g x) - ∫ x, u x * g x := by
    rw [← integral_sub hint1 hint0]
    simp only [sub_mul]
  rw [hJ, ← h1, ← h0, ← Real.norm_eq_abs]
  exact hmvt
/-- Smooth `±1` separation of two disjoint compact sets `K₁, K₂ ⊆ ℝ^n`: a `C^∞` function
`g : ℝ^n → ℝ` with compact support, `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`.
`Disjoint.exists_thickenings` gives `δ > 0` with disjoint open thickenings `Vᵢ ⊇ Kᵢ`; the smooth
Urysohn lemma `exists_contDiff_support_eq_eq_one_iff` gives `gᵢ : ℝ^n → [0, 1]` with
`support gᵢ = Vᵢ` and `gᵢ = 1` on `Kᵢ`, compactly supported since `closure Vᵢ ⊆ cthickening δ Kᵢ`.
At each point one of `g₁, g₂` vanishes, and `g = g₁ - g₂`. -/
theorem Submission.fiw_tb_te_l1d_smooth_sign_sep : ∀ (n : ℕ) (K₁ K₂ : Set (Eucl n)), IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ → ∃ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧ (∀ x, |g x| ≤ 1) ∧ (∀ x ∈ K₁, g x = 1) ∧ (∀ x ∈ K₂, g x = -1) := by
  intro n K₁ K₂ hK₁ hK₂ hd
  -- Steps 1–2: disjoint δ-thickenings `V₁ ⊇ K₁`, `V₂ ⊇ K₂`.
  obtain ⟨δ, hδ, hdδ⟩ := hd.exists_thickenings hK₁ hK₂.isClosed
  -- Step 3: smooth Urysohn functions `gᵢ : ℝ^n → [0, 1]`, `support gᵢ = Vᵢ`, `gᵢ = 1` on `Kᵢ`.
  obtain ⟨g₁, hg₁, hr₁, hs₁, he₁⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₁)) hK₁.isClosed (self_subset_thickening hδ K₁)
  obtain ⟨g₂, hg₂, hr₂, hs₂, he₂⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K₂)) hK₂.isClosed (self_subset_thickening hδ K₂)
  -- Step 4: `tsupport gᵢ = closure Vᵢ ⊆ cthickening δ Kᵢ`, which is compact.
  have hc : ∀ (K : Set (Eucl n)) (f : Eucl n → ℝ), IsCompact K →
      Function.support f = thickening δ K → HasCompactSupport f := by
    intro K f hK hs
    refine (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport f) ?_
    rw [tsupport, hs]
    exact closure_thickening_subset_cthickening δ K
  have h01₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1 := fun x => hr₁ (mem_range_self x)
  have h01₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1 := fun x => hr₂ (mem_range_self x)
  -- Step 5: at every point one of `g₁, g₂` vanishes, since `V₁ ∩ V₂ = ∅`.
  have hdis : ∀ x, g₁ x = 0 ∨ g₂ x = 0 := by
    intro x
    by_contra h
    rw [not_or] at h
    have h1 : x ∈ Function.support g₁ := h.1
    have h2 : x ∈ Function.support g₂ := h.2
    rw [hs₁] at h1
    rw [hs₂] at h2
    exact Set.disjoint_left.mp hdδ h1 h2
  -- Steps 6–8: `g = g₁ - g₂`.
  refine ⟨g₁ - g₂, hg₁.sub hg₂, (hc K₁ g₁ hK₁ hs₁).sub (hc K₂ g₂ hK₂ hs₂), ?_, ?_, ?_⟩
  · intro x
    have a := h01₁ x
    have b := h01₂ x
    rw [Pi.sub_apply, abs_le]
    rcases hdis x with h | h <;> constructor <;> linarith
  · intro x hx
    have h1 : g₁ x = 1 := (he₁ x).1 hx
    have h2 : g₂ x = 0 := by
      rcases hdis x with h | h
      · rw [h1] at h; norm_num at h
      · exact h
    simp [h1, h2]
  · intro x hx
    have h2 : g₂ x = 1 := (he₂ x).1 hx
    have h1 : g₁ x = 0 := by
      rcases hdis x with h | h
      · exact h
      · rw [h2] at h; norm_num at h
    simp [h1, h2]
/-- Compact approximation of the sign of an integrable `w : ℝ^n → ℝ`: for `ε > 0` there are
disjoint compact sets `K₁, K₂` such that every a.e.-strongly measurable `g` with `|g| ≤ 1`,
`g = 1` on `K₁` and `g = -1` on `K₂` satisfies `∫ |w| < ∫ w g + ε`.
For a Borel representative `v` of `w`, the finite measure `ν = |v| dx` is inner regular, so there
are compact `K₁ ⊆ {v > 0}` and `K₂ ⊆ {v < 0}` with `ν({v > 0} \ K₁), ν({v < 0} \ K₂) < ε/4`.
Off `S = ({v > 0} \ K₁) ∪ ({v < 0} \ K₂)` we have `v g = |v|`, and on `S` we have `v g ≥ -|v|`,
so `∫ |v| ≤ ∫ v g + 2 ν(S) < ∫ v g + ε`. -/
theorem Submission.fiw_tb_te_l1d_compact_sign_approx : ∀ (n : ℕ) (w : Eucl n → ℝ), Integrable w → ∀ ε : ℝ, 0 < ε → ∃ K₁ K₂ : Set (Eucl n), IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧ ∀ g : Eucl n → ℝ, AEStronglyMeasurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ K₁, g x = 1) → (∀ x ∈ K₂, g x = -1) → (∫ x, |w x|) < (∫ x, w x * g x) + ε := by
  intro n w hw ε hε
  -- A Borel representative `v` of `w` and the finite measure `ν = |v| dx`.
  set v : Eucl n → ℝ := hw.aestronglyMeasurable.mk w with hv_def
  have hv_meas : StronglyMeasurable v := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hwv : w =ᵐ[volume] v := hw.aestronglyMeasurable.ae_eq_mk
  have hvi : Integrable v := hw.congr hwv
  set ν : Measure (Eucl n) := volume.withDensity (fun x => ENNReal.ofReal |v x|) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hvi.abs.hasFiniteIntegral
  -- Inner approximation of `{v > 0}` and `{v < 0}` by compact sets.
  set Ap : Set (Eucl n) := {x | 0 < v x} with hAp_def
  set Am : Set (Eucl n) := {x | v x < 0} with hAm_def
  have hAp : MeasurableSet Ap := measurableSet_lt measurable_const hv_meas.measurable
  have hAm : MeasurableSet Am := measurableSet_lt hv_meas.measurable measurable_const
  have hε4 : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨Kp, hKpA, hKp, hKpν⟩ := hAp.exists_isCompact_sdiff_lt (measure_ne_top ν Ap) hε4
  obtain ⟨Km, hKmA, hKm, hKmν⟩ := hAm.exists_isCompact_sdiff_lt (measure_ne_top ν Am) hε4
  have hdisj : Disjoint Kp Km := by
    rw [Set.disjoint_left]
    intro x hp hm
    have h1 : 0 < v x := hKpA hp
    have h2 : v x < 0 := hKmA hm
    linarith
  refine ⟨Kp, Km, hKp, hKm, hdisj, ?_⟩
  intro g hg hg1 hgp hgm
  -- The pointwise inequality `|v| - 2·1_S|v| ≤ v g`.
  set S : Set (Eucl n) := (Ap \ Kp) ∪ (Am \ Km) with hS_def
  have hS : MeasurableSet S := (hAp.diff hKp.measurableSet).union (hAm.diff hKm.measurableSet)
  have hpt : ∀ x, |v x| - 2 * S.indicator (fun y => |v y|) x ≤ v x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have h : |v x * g x| ≤ |v x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hg1 x)
      linarith [(abs_le.mp h).1]
    · rw [indicator_of_notMem hx]
      have hx' : (0 < v x → x ∈ Kp) ∧ (v x < 0 → x ∈ Km) := by
        constructor
        · intro h
          by_contra hK
          exact hx (Or.inl ⟨h, hK⟩)
        · intro h
          by_contra hK
          exact hx (Or.inr ⟨h, hK⟩)
      rcases lt_trichotomy (v x) 0 with h | h | h
      · rw [hgm x (hx'.2 h), abs_of_neg h]
        linarith
      · rw [h]
        simp
      · rw [hgp x (hx'.1 h), abs_of_pos h]
        linarith
  -- Integrate.
  have hvg : Integrable (fun x => v x * g x) :=
    hvi.mul_bdd hg (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg1 x)
  have hind : Integrable (fun x => S.indicator (fun y => |v y|) x) := hvi.abs.indicator hS
  have hlhs : Integrable (fun x => |v x| - 2 * S.indicator (fun y => |v y|) x) :=
    hvi.abs.sub (hind.const_mul 2)
  have hmono := integral_mono hlhs hvg hpt
  rw [integral_sub hvi.abs (hind.const_mul 2), integral_const_mul, integral_indicator hS] at hmono
  -- `∫_S |v| = (ν S).toReal < ε / 2`.
  have hνS : ν S = ∫⁻ x in S, ENNReal.ofReal |v x| := withDensity_apply _ hS
  have hSint : ∫ x in S, |v x| = (ν S).toReal := by
    rw [hνS, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _)
      hvi.abs.aestronglyMeasurable.restrict]
  have hνS_lt : ν S < ENNReal.ofReal (ε / 2) := by
    calc ν S ≤ ν (Ap \ Kp) + ν (Am \ Km) := measure_union_le _ _
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := ENNReal.add_lt_add hKpν hKmν
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
  have hSlt : ∫ x in S, |v x| < ε / 2 := by
    rw [hSint]
    exact ENNReal.toReal_lt_of_lt_ofReal hνS_lt
  -- Transfer back from `v` to `w`.
  have h1 : ∫ x, |w x| = ∫ x, |v x| := integral_congr_ae (hwv.fun_comp abs)
  have h2 : ∫ x, w x * g x = ∫ x, v x * g x :=
    integral_congr_ae (hwv.mono fun x hx => by simp only [hx])
  rw [h1, h2]
  linarith

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

/-- **`L¹` norm by duality with smooth test functions** (proof of the translation estimate,
Step 4).  If `w : ℝⁿ → ℝ` is integrable and `∫ w g ≤ C` for every `C^∞` compactly supported `g`
with `|g| ≤ 1`, then `∫ |w| ≤ C`.  Given `ε > 0`, inner regularity of the finite measure `|w| dx`
gives disjoint compact sets `K₁, K₂`, approximating `{w > 0}` and `{w < 0}`, such that
`∫ |w| < ∫ w g + ε` for every measurable `g` with `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`.
Smooth Urysohn functions on disjoint thickenings of `K₁, K₂` give such a `g ∈ C_c^∞`, so
`∫ |w| < C + ε`. -/
theorem Submission.fiw_tb_te_l1_le_of_smooth_dual : ∀ (n : ℕ) (w : Eucl n → ℝ) (C : ℝ), Integrable w → (∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → (∀ x, |g x| ≤ 1) → ∫ x, w x * g x ≤ C) → ∫ x, |w x| ≤ C := by
  intro n w C hw H
  -- Step 8: it suffices that `∫ |w| < C + ε` for every `ε > 0`.
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- Steps 1, 2, 6, 7: compact `K₁, K₂` on which a `±1`-valued `g` nearly attains `∫ |w|`.
  obtain ⟨K₁, K₂, hK₁, hK₂, hd, hB⟩ := Submission.fiw_tb_te_l1d_compact_sign_approx n w hw ε hε
  -- Steps 3–5: a `C^∞` compactly supported `g` with `|g| ≤ 1`, `g = 1` on `K₁`, `g = -1` on `K₂`.
  obtain ⟨g, hg, hgc, hg1, hgK₁, hgK₂⟩ :=
    Submission.fiw_tb_te_l1d_smooth_sign_sep n K₁ K₂ hK₁ hK₂ hd
  -- `g` is continuous, hence a.e.-strongly measurable: `∫ |w| < ∫ w g + ε ≤ C + ε`.
  have h1 := hB g hg.continuous.aestronglyMeasurable hg1 hgK₁ hgK₂
  have h2 := H g hg hgc hg1
  linarith

/-- Translation estimate (Simon Ch. 6, proof of 7.2, used for the summed form of 5.1 (32)): if the
top-dimensional current `X ∈ 𝒟ₙ(ℝⁿ)` is `X(ω) = ∫ u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` with `u ∈ L¹`, then
`∫ |u(x + h) − u(x)| dx ≤ |h| M(∂X)` for every `h ∈ ℝⁿ`. -/
theorem Submission.fiw_tb_translation_estimate :
    ∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1))
      (u : Eucl (m + 1) → ℝ), Integrable u →
      (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x *
        (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))) →
      ∀ h : Eucl (m + 1),
        ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * X.boundary.mass := by
  intro m X u hu hX h
  -- Trivial cases: `h = 0` (the left side vanishes) and `M(∂X) = ∞` (the right side is `∞`).
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  by_cases hM : X.boundary.mass = ∞
  · rw [hM, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpos).ne']
    exact le_top
  -- For `φ ∈ C_c^∞` with `|φ| ≤ 1`, the directional form `ω` has `dω(e) = Dφ(h)` and
  -- `|ω| ≤ ‖h‖`, so `|∫ u Dφ(h)| = |X(dω)| = |∂X(ω)| ≤ ‖h‖ M(∂X)`.
  have hdiv : ∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      HasCompactSupport φ → (∀ x, |φ x| ≤ 1) →
        |∫ x, u x * fderiv ℝ φ x h| ≤ ‖h‖ * X.boundary.mass.toReal := by
    intro φ hφ hφc hφ1
    obtain ⟨ω, hω, hdω⟩ := Submission.fiw_tb_te_directional_form m φ h hφ hφc
    have hval : X.boundary ω = ∫ x, u x * fderiv ℝ φ x h := by
      rw [GeometricCurrentOn.boundary_apply, hX]
      exact integral_congr_ae (ae_of_all _ fun x => congrArg (u x * ·) (hdω x))
    rw [← hval]
    refine Submission.fiw_tb_te_abs_apply_le_mul_mass (m + 1) m univ X.boundary ω ‖h‖ hpos
      (fun x => ?_) hM
    calc covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x)
        ≤ ‖h‖ * |φ x| := hω x
      _ ≤ ‖h‖ * 1 := by gcongr; exact hφ1 x
      _ = ‖h‖ := mul_one _
  -- Weak estimate `|∫ (u(· + h) − u) g| ≤ ‖h‖ M(∂X)`, then `L¹` duality.
  have hweak := Submission.fiw_tb_te_translation_dual (m + 1) u h _ hu hdiv
  have hw : Integrable (fun x => u (x + h) - u x) := (hu.comp_add_right h).sub hu
  have hL1 : ∫ x, |u (x + h) - u x| ≤ ‖h‖ * X.boundary.mass.toReal :=
    Submission.fiw_tb_te_l1_le_of_smooth_dual (m + 1) (fun x => u (x + h) - u x) _ hw
      fun g hg hgc hg1 => (le_abs_self _).trans (hweak g hg hgc hg1)
  calc ∫⁻ x, ENNReal.ofReal |u (x + h) - u x|
      = ENNReal.ofReal (∫ x, |u (x + h) - u x|) :=
        (ofReal_integral_eq_lintegral_ofReal hw.abs (ae_of_all _ fun x => abs_nonneg _)).symm
    _ ≤ ENNReal.ofReal (‖h‖ * X.boundary.mass.toReal) := ENNReal.ofReal_le_ofReal hL1
    _ = ENNReal.ofReal ‖h‖ * X.boundary.mass := by
      rw [ENNReal.ofReal_mul (norm_nonneg h), ENNReal.ofReal_toReal hM]

/-- **Top-dimensional approximation by a lattice chain (Simon Ch. 6, proof of 5.1, (27)–(37) with
`Q := X`, `R := 0`).**  An integer multiplicity `X ∈ 𝒟ₙ(ℝⁿ)` (`n = m + 1`) with `M(X), M(∂X) < ∞`
has an integer `L¹` density `u`: `X(ω) = ∫ u ω(e)`, `∫ |u| = M(X)` and `u = 0` a.e. off `spt X`.
Integer medians `β_F` of `u` on the cubes `F ∈ 𝓛ₙ(ρ)` give the lattice chain `Pc = ∑ β_F [[F]]`,
integer multiplicity with density `v = β_F` on `F`.  `S = X − Pc` is integer multiplicity (LC) and
`M(S) ≤ ∫ |u − v| = ∑_F ∫_F |u − β_F| ≤ ∑_F ρ⁻ⁿ ∫_F ∫_F |u(x) − u(y)| ≤ c ρ M(∂X)` by the
translation estimate `∫ |u(· + h) − u| ≤ ‖h‖ M(∂X)`.  A cube with `β_F ≠ 0` meets `{u ≠ 0}` in
positive measure, hence meets `spt X`, and has diameter `√n ρ`. -/
theorem Submission.fiw_tb_top_dim_approx : (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) → ∀ m : ℕ, ∃ c : ℝ≥0, ∀ X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ → ∃ (β : LatticeFaceIndex (m + 1) (m + 1) → ℝ) (Pc S : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsLatticeChain ρ β Pc ∧ (∀ F, ∃ k : ℤ, β F = k) ∧ (∀ F, β F ≠ 0 → latticeFace ρ F ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) X.support) ∧ (∀ F, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ 2 * X.mass) ∧ IsIntegerMultiplicity S ∧ (∀ ω, X ω - Pc ω = S ω) ∧ S.mass ≤ c * ENNReal.ofReal ρ * X.boundary.mass := by
  intro hMF hLC m
  -- `c` is the constant of the summed cube Poincaré inequality.
  obtain ⟨c, hc⟩ := Submission.fiw_tb_tda_poincare_sum m
  refine ⟨c, fun X hX hXm hXb ρ hρ => ?_⟩
  -- The integer `L¹` density `u` of `X`; its hypothesis is MF with `U = W = univ` together with
  -- `Hⁿ(M ∖ spt X) = 0` (support_null).
  obtain ⟨u, hum, huZ, huint, humass, husupp, hXu⟩ :=
    Submission.fiw_tb_tda_density m X hX hXm fun M θ ξ hM hXM => by
      refine ⟨?_, Submission.fiw_tb_rectifiable_support_null hMF (m + 1) (m + 1) univ isOpen_univ
        X M θ ξ hM hXM⟩
      have h := hMF (m + 1) (m + 1) univ isOpen_univ X M θ ξ hM hXM univ isOpen_univ
      rwa [inter_univ] at h
  -- The cubes `F ∈ 𝓛ₙ(ρ)` are measurable, of volume `ρⁿ` and diameter `√n ρ`, and `∫⁻` splits
  -- over them.
  obtain ⟨-, -, hFmeas, hFvol, hFdiam, -, hFsum, -⟩ := Submission.fiw_tb_tda_lattice_cubes m ρ hρ
  -- Integer medians `b F` of `u` on the cubes, with (M1), (M2) and (M4).
  choose b hb1 hb2 hb3 using fun F : LatticeFaceIndex (m + 1) (m + 1) =>
    Submission.fiw_tb_tda_integer_median volume (latticeFace ρ F) (ρ ^ (m + 1)) u (hFmeas F)
      (pow_pos hρ _) (hFvol F) hum huZ huint.integrableOn
  -- (M1): `|b F| ρⁿ ≤ 2 ∫_F |u| ≤ 2 M(X)`; summed over the cubes, `≤ 2 M(X) < ∞`.
  have hcoef : ∀ F, ENNReal.ofReal (|(b F : ℝ)| * ρ ^ (m + 1)) ≤ 2 * X.mass := fun F =>
    (hb1 F).trans (by rw [← humass]; exact mul_le_mul_right (setLIntegral_le_lintegral _ _) 2)
  have hsum : (∑' F, ENNReal.ofReal (|(b F : ℝ)| * ρ ^ (m + 1))) < ∞ :=
    calc (∑' F, ENNReal.ofReal (|(b F : ℝ)| * ρ ^ (m + 1)))
        ≤ ∑' F, 2 * ∫⁻ x in latticeFace ρ F, ENNReal.ofReal |u x| := ENNReal.tsum_le_tsum hb1
      _ = 2 * X.mass := by
        rw [ENNReal.tsum_mul_left, ← hFsum fun x => ENNReal.ofReal |u x|, humass]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofNat_ne_top.lt_top hXm
  -- The lattice chain `Pc = ∑ b F [[F]]`: integer multiplicity, with density `v = b F` a.e. on `F`.
  obtain ⟨Pc, v, hPc, hPcim, hvint, hvF, hPcv⟩ :=
    Submission.fiw_tb_tda_lattice_chain m ρ hρ (fun F => (b F : ℝ)) (fun F => ⟨b F, rfl⟩) hsum
  -- `S = X − Pc` with `M(S) ≤ ∫ |u − v|`; `S` is integer multiplicity by LC (`a = 1`, `b = −1`).
  obtain ⟨S, hS, hSmass⟩ := Submission.fiw_tb_tda_sub_mass m X Pc u v huint hvint hXu hPcv
  have hSim : IsIntegerMultiplicity S :=
    hLC (m + 1) (m + 1) univ isOpen_univ X Pc S 1 (-1) hX hPcim fun ω => by
      rw [← hS ω]; push_cast; ring
  refine ⟨fun F => (b F : ℝ), Pc, S, hPc, fun F => ⟨b F, rfl⟩, fun F hF => ?_, hcoef, hSim, hS, ?_⟩
  · -- (M2): `F ∩ {u ≠ 0}` is not null and `u = 0` a.e. off `spt X`, so `F` meets `spt X`, and
    -- every point of `F` lies within `diam F = √n ρ` of that point.
    obtain ⟨p, hpF, hpX⟩ : (latticeFace ρ F ∩ X.support).Nonempty := by
      by_contra hne
      refine hb2 F (Int.cast_ne_zero.1 hF) (measure_mono_null (fun x hx => ?_) (ae_iff.1 husupp))
      exact fun h => hx.2 (h fun hxX => hne ⟨x, hx.1, hxX⟩)
    exact fun x hx => mem_cthickening_of_dist_le x p _ _ hpX (hFdiam F x hx p hpF)
  · -- (M4) on every cube, summed, then the summed Poincaré inequality fed by the translation
    -- estimate `∫ |u(· + h) − u| ≤ ‖h‖ M(∂X)`.
    calc S.mass ≤ ∫⁻ x, ENNReal.ofReal |u x - v x| := hSmass
      _ = ∑' F, ∫⁻ x in latticeFace ρ F, ENNReal.ofReal |u x - v x| := hFsum _
      _ = ∑' F, ∫⁻ x in latticeFace ρ F, ENNReal.ofReal |u x - b F| := by
        refine tsum_congr fun F => lintegral_congr_ae ?_
        filter_upwards [hvF F] with x hx
        rw [hx]
      _ ≤ ∑' F, ENNReal.ofReal (ρ ^ (m + 1))⁻¹ *
          ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| :=
        ENNReal.tsum_le_tsum hb3
      _ ≤ c * ENNReal.ofReal ρ * X.boundary.mass :=
        hc ρ hρ u _ hum (Submission.fiw_tb_translation_estimate m X u huint hXu)

end GMT.Ch06
