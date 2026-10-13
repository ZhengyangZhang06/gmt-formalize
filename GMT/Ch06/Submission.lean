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

/-- Properness transfer (fact (P)); "proper on `F`" means `f⁻¹(K) ∩ F` is compact for every
compact `K`.  (a) If `G` is proper on the closed set `F` and the continuous map `g` is `d`-close
to `G` on `F`, then `g⁻¹(K) ∩ F` is a closed subset of the compact set
`G⁻¹(cthickening d K) ∩ F`.  (b) The affine homotopy `H(y) = F₀(x) + s • (F₁(x) − F₀(x))`,
`y = (s, x)`, of two such maps stays in the closed `d`-ball about `G(x)` by convexity, so
`H⁻¹(K) ∩ ([0,1] × F)` is a closed subset of the image of the compact set
`[0,1] × (G⁻¹(cthickening d K) ∩ F)` under the continuous chart `(s, x) ↦ y`. -/
theorem Submission.dph_lpf_proper_transfer :
    (∀ (m m' : ℕ) (G g : Eucl m → Eucl m') (F : Set (Eucl m)) (d : ℝ), IsClosed F → Continuous g → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → (∀ x ∈ F, dist (g x) (G x) ≤ d) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact (g ⁻¹' K ∩ F)) ∧ (∀ (m m' : ℕ) (G F₀ F₁ : Eucl m → Eucl m') (F : Set (Eucl m)) (d : ℝ), IsClosed F → Continuous F₀ → Continuous F₁ → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → (∀ x ∈ F, dist (F₀ x) (G x) ≤ d) → (∀ x ∈ F, dist (F₁ x) (G x) ≤ d) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ F})) := by
  refine ⟨?_, ?_⟩
  · intro m m' G g F d hF hg hG hd K hK
    refine (hG _ (hK.cthickening (r := d))).of_isClosed_subset
      ((hK.isClosed.preimage hg).inter hF) ?_
    rintro x ⟨hxK, hxF⟩
    exact ⟨mem_cthickening_of_dist_le (G x) (g x) d K hxK ((dist_comm _ _).trans_le (hd x hxF)),
      hxF⟩
  · intro m m' G F₀ F₁ F d hF hF₀ hF₁ hG hd₀ hd₁ K hK
    set e := EuclideanSpace.equiv (Fin (m + 1)) ℝ
    set e' := EuclideanSpace.equiv (Fin m) ℝ
    -- The coordinates `s = t(y)`, `x = tl(y)` and the homotopy `H` are continuous.
    have ht : Continuous fun y : Eucl (m + 1) => e y 0 := (continuous_apply 0).comp e.continuous
    have htl : Continuous fun y : Eucl (m + 1) => e'.symm (Fin.tail (e y)) :=
      e'.symm.continuous.comp (continuous_pi fun i => (continuous_apply i.succ).comp e.continuous)
    have hH : Continuous fun y : Eucl (m + 1) => F₀ (e'.symm (Fin.tail (e y))) +
        e y 0 • (F₁ (e'.symm (Fin.tail (e y))) - F₀ (e'.symm (Fin.tail (e y)))) :=
      (hF₀.comp htl).add (ht.smul ((hF₁.comp htl).sub (hF₀.comp htl)))
    -- The inverse chart `(s, x) ↦ y` is continuous.
    have hc : Continuous fun p : ℝ × Eucl m => e.symm (Fin.cons p.1 (e' p.2) : Fin (m + 1) → ℝ) :=
      e.symm.continuous.comp
        (continuous_fst.finCons (A := fun _ => ℝ) (e'.continuous.comp continuous_snd))
    -- `H⁻¹(K) ∩ cyl(F)` is closed and lies in the chart image of
    -- `[0,1] × (G⁻¹(cthickening d K) ∩ F)`, which is compact.
    refine (((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
        (hG _ (hK.cthickening (r := d)))).image hc).of_isClosed_subset
      ((hK.isClosed.preimage hH).inter ((isClosed_Icc.preimage ht).inter (hF.preimage htl))) ?_
    rintro y ⟨hyK, hyt, hyF⟩
    refine ⟨(e y 0, e'.symm (Fin.tail (e y))), ⟨hyt, ?_, hyF⟩, ?_⟩
    · -- `H(y)` lies in the closed `d`-ball about `G(x)`, so `G(x) ∈ cthickening d K`.
      have hmem := (convex_closedBall (G (e'.symm (Fin.tail (e y)))) d).add_smul_sub_mem
        (mem_closedBall.2 (hd₀ _ hyF)) (mem_closedBall.2 (hd₁ _ hyF)) hyt
      exact mem_cthickening_of_dist_le _ _ d K hyK
        ((dist_comm _ _).trans_le (mem_closedBall.1 hmem))
    · show e.symm (Fin.cons (e y 0) (e' (e'.symm (Fin.tail (e y))))) = y
      rw [e'.apply_symm_apply, Fin.cons_self_tail, e.symm_apply_apply]

/-- **Reference smooth approximations near a closed set** (Simon Ch. 6, 2.28–2.29; Step 2 of the
Lipschitz push-forward).  Assume the smooth approximation statement (SA) of
`dph_lipschitz_smooth_approx`.  If `F` is closed, `G` is `Λ`-Lipschitz on `F_r` (`r > 0`) and
proper on `F`, (SA) with `A := F`, `δ := r` gives `C^∞` maps `Gₙ` with `‖DGₙ‖ ≤ Λ` on `F_(r/2)`
and `Gₙ → Ĝ` uniformly, where `Ĝ = G` on `F_r ⊇ F_(r/2)`.  So `Gₙ → G` uniformly on `F_(r/2)`,
eventually `dist (Gₙ x) (G x) ≤ 1` on `F`, and `dph_lpf_proper_transfer` (a) makes `Gₙ` proper
on `F`. -/
theorem Submission.dph_lpf_reference_sequence : (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ → LipschitzOnWith Λ G (thickening δ A) → ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧ (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧ TendstoUniformly Gj G' atTop ∧ (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧ ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m') (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε → (∀ x ∈ thickening ε A, G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) → ∀ i, i ∉ range α → G x i = z i) → (∀ y, (ω : DifferentialForm (Eucl m') k) y (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) → ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A, ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap (fderiv ℝ (Gj j) x) = 0) → (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) := by
  intro hSA m m' G Λ r F hr hF hG hprop
  -- 1. (SA) with `A := F`, `δ := r`.
  obtain ⟨G', Gj, L, -, hG'G, hsmooth, -, hconv, hderiv, -⟩ := hSA m m' G Λ F r hr hG
  -- 2. `F_(r/2) ⊆ F_r`, where `G' = G`, so `Gj → G` uniformly on `F_(r/2)`.
  have hsub : thickening (r / 2) F ⊆ thickening r F := thickening_mono (half_le_self hr.le) F
  have hconvG : TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) :=
    hconv.tendstoUniformlyOn.congr_right (hG'G.mono hsub)
  refine ⟨Gj, hsmooth, hderiv, hconvG, ?_⟩
  -- 3. Eventually `dist (G x) (Gj n x) < 1` on `F_(r/2) ⊇ F`.
  have hFsub : F ⊆ thickening (r / 2) F := self_subset_thickening (half_pos hr) F
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconvG 1 one_pos] with n hn
  -- 4. `Gj n` is continuous and `1`-close to `G` on `F`, hence proper on `F`.
  exact Submission.dph_lpf_proper_transfer.1 m m' G (Gj n) F 1 hF (hsmooth n).continuous hprop
    fun x hx => by
      rw [dist_comm]
      exact (hn x (hFsub hx)).le
/-- **The affine homotopy restricts to its ends and is smooth** (Simon Ch. 6, (2.26), p. 140:
`h(t, x) = f(x) + t (g(x) − f(x))`).  On `ℝ^{m+1}` write `t(y) = y₀` and `tl(y) = (y₁, …, y_m)`;
`G = F₀ ∘ tl + t • (F₁ ∘ tl − F₀ ∘ tl)`.  For `y = cons(s, x)`, `t(y) = s` and `tl(y) = x` hold
definitionally, so `G(cons(0, x)) = F₀(x)` and `G(cons(1, x)) = F₁(x)`.  The maps `t` and `tl` are
coordinate projections composed with continuous linear equivalences, hence `C^∞`, so `G` is `C^∞`
when `F₀` and `F₁` are. -/
theorem Submission.dph_lpf_cmp_affine_homotopy : ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m') (G : Eucl (m + 1) → Eucl m'), G = (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) → (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) = F₀ ∧ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) = F₁ ∧ (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) := by
  intro m m' F₀ F₁ G hG
  subst hG
  refine ⟨funext fun x => ?_, funext fun x => ?_, fun h₀ h₁ => ?_⟩
  -- `t(cons(0, x)) = 0` and `tl(cons(0, x)) = x` definitionally (`simp` does not see through
  -- `EuclideanSpace.equiv`, so restate the goal by `change`).
  · change F₀ x + (0 : ℝ) • (F₁ x - F₀ x) = F₀ x
    rw [zero_smul, add_zero]
  -- Likewise `t(cons(1, x)) = 1` and `tl(cons(1, x)) = x`.
  · change F₀ x + (1 : ℝ) • (F₁ x - F₀ x) = F₁ x
    rw [one_smul, add_sub_cancel]
  -- `Fin.tail` is `C^∞`: each of its coordinates `q ↦ q i.succ` is.
  · have htail : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) :=
      contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ
    -- `tl` is `C^∞`: compose with the continuous linear equivalences.
    have htl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Eucl (m + 1) =>
        (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) :=
      (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.comp
        (htail.comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).contDiff)
    -- `t` is `C^∞`: the coordinate `q ↦ q 0` composed with a continuous linear equivalence.
    have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Eucl (m + 1) =>
        EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 :=
      (contDiff_apply ℝ ℝ (0 : Fin (m + 1))).comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).contDiff
    exact (h₀.comp htl).add (ht.smul ((h₁.comp htl).sub (h₀.comp htl)))
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
/-- A current kills every test form whose support misses `spt T`: `tsupport ω` is a compact subset
of the zero region, so finitely many open `W ⊂⊂ U` on which `T` vanishes cover it, and a smooth
partition of unity `ψᵢ` on `tsupport ω` subordinate to them splits `ω = ∑ᵢ ψᵢ ω` into test forms
supported in those `W`. -/
theorem Submission.isoperimetric_apply_eq_zero_of_disjoint_support :
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

/-- Supports of boundaries, weak limits and linear combinations: `spt ∂Z ⊆ spt Z`; a weak limit of
currents supported in a closed `K` is supported in `K`; `spt Z ⊆ spt Z₁ ∪ spt Z₂` when
`Z = a Z₁ + b Z₂`.  In each case a point outside the claimed support lies in an open `W ⊂⊂ U` on
which the current vanishes, i.e. in its zero region. -/
theorem Submission.iwl_cr_support_lemmas :
    (∀ (P m : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (m + 1)),
      Z.boundary.support ⊆ Z.support) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P))
      (Zj : ℕ → GeometricCurrentOn U n) (Z : GeometricCurrentOn U n), IsClosed K →
      (∀ j, (Zj j).support ⊆ K) → WeaklyConvergesOn Zj Z → Z.support ⊆ K) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Z₁ Z₂ Z : GeometricCurrentOn U n) (a b : ℝ),
      (∀ ω : TestFormOn U n, Z ω = a * Z₁ ω + b * Z₂ ω) →
      Z.support ⊆ Z₁.support ∪ Z₂.support) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) If `Z` vanishes on an admissible `W`, so does `∂Z`: `∂Z φ = Z (dφ)` and
    -- `tsupport dφ ⊆ tsupport φ ⊆ W`.
    intro P m U Z x hx
    refine ⟨hx.1, fun hxZ => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
    refine Set.mem_sUnion.2 ⟨W, ⟨hWo, hWc, hWU, fun φ hφ => ?_⟩, hxW⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hφ)
  · -- (2) For `x ∈ spt Z \ K`, the ball `W = B(x, ε/2)` has `closure W ⊆ U \ K`.  A test form
    -- supported in `W` misses `K ⊇ spt (Zj j)`, so every `Zj j` kills it, and so does the limit.
    intro P n U hU K Zj Z hK hZj hconv x hx
    by_contra hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.sdiff hK) x ⟨hx.1, hxK⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ U \ K := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans sdiff_subset, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have h0 : ∀ j, Zj j ω = 0 := fun j =>
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U (Zj j) ω
          (Set.disjoint_left.2 fun y hy hyS => (hcl (subset_closure (hω hy))).2 (hZj j hyS))
      have hlim := hconv ω
      simp only [h0] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- (3) For `x ∈ spt Z` outside `spt Z₁ ∪ spt Z₂`, the ball `W = B(x, ε/2)` has `closure W`
    -- inside both zero regions and `U`, so `Z₁`, `Z₂` and hence `Z = a Z₁ + b Z₂` vanish on `W`.
    intro P n U hU Z₁ Z₂ Z a b hZ x hx
    by_contra hx12
    have h1 : x ∈ Z₁.zeroRegion := by
      by_contra h
      exact hx12 (Or.inl ⟨hx.1, h⟩)
    have h2 : x ∈ Z₂.zeroRegion := by
      by_contra h
      exact hx12 (Or.inr ⟨hx.1, h⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((Z₁.isOpen_zeroRegion.inter Z₂.isOpen_zeroRegion).inter hU) x ⟨⟨h1, h2⟩, hx.1⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ Z₁.zeroRegion ∩ Z₂.zeroRegion ∩ U := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans inter_subset_right, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have e1 : Z₁ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₁ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.1)
      have e2 : Z₂ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₂ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.2)
      rw [hZ ω, e1, e2]
      ring
/-- **Test forms have bounded Euclidean coefficient norm** (the finiteness of `sup_x |ω(x)|` behind
"Evidently (1), (2) give `P_k(ω) → T(ω)`" in the proof of Simon Ch. 6, 6.2, p. 169).
`x ↦ |ω(x)|` is continuous, since `α ↦ |α|` is the square root of a finite sum of squares of
evaluations, and has compact support, since `|0| = 0`.  A continuous compactly supported real
function is bounded by some `C₀ ≥ 0`, and `C = C₀ + 1` is positive. -/
theorem Submission.br_la_testForm_covectorNorm_bounded : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U n), ∃ C : ℝ, 0 < C ∧ ∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C := by
  intro P n U ω
  -- `ω` is smooth, hence continuous.
  have hω : Continuous (ω : DifferentialForm (Eucl P) n) := ω.property.1.1.continuous
  -- `x ↦ |ω(x)|` is continuous: a square root of a finite sum of squares of evaluations.
  have hcont : Continuous fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (hω.eval_const _).pow 2
    · exact continuous_const
  -- `|ω(x)| = 0` wherever `ω(x) = 0`, so `x ↦ |ω(x)|` inherits the compact support of `ω`.
  have hsupp : HasCompactSupport fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) := by
    refine ω.property.1.2.mono' fun x hx => subset_tsupport _ fun h => hx ?_
    simp [h]
  -- A continuous compactly supported function is bounded by some `C₀ ≥ |f(0)| ≥ 0`.
  obtain ⟨C₀, hC₀⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨C₀ + 1, by linarith [(norm_nonneg _).trans (hC₀ 0)], fun x => ?_⟩
  linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)),
    (Real.norm_eq_abs _).symm.trans_le (hC₀ x)]
/-- **Core estimate of the comparison lemma** (Simon Ch. 6, proof of 2.29, p. 141: the homotopy
formula 2.25 for the affine homotopy 2.26 and the mass bound 2.27 give
`|f_ε# T(ω) − f_δ# T(ω)| ≤ C sup |f_ε − f_δ| (Lip f)ⁿ`).  Assume the interval product (Prod) and
the homotopy formulas (E0), (E1) with the affine estimate (Aff).  For `X` with `M(X) < ∞` (and
`M(∂X) < ∞` if `k ≥ 1`), `ω` and `L ≥ 0`, everything entering `C₀` is chosen before the maps: `Z`
with `ProdChar(X, Z)`, the constant `c` of (Aff), `C₁ ≥ |dω|` and `B = M(X)`; for `k = j + 1` also
`Z′` with `ProdChar(∂X, Z′)`, `c′`, `C₂ ≥ |ω|` and `B′ = M(∂X)`.  For the affine homotopy
`H = H[F₀, F₁]`, the pull-backs `η′ = H^# dω`, `θ′ = H^# ω` near `[0, 1] × spt X` turn the homotopy
formula into `X(η₁) − X(η₀) = Z(η′) (+ Z′(θ′))`, and (Aff) bounds each term by
`c s L^k M(·) sup |·|`. -/
theorem Submission.dph_lpf_cmp_core_estimate : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (L : ℝ), 0 ≤ L → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s : ℝ) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → 0 ≤ s → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (F₀ x)).compContinuousLinearMap (fderiv ℝ F₀ x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (F₁ x)).compContinuousLinearMap (fderiv ℝ F₁ x)) → |X η₁ - X η₀| ≤ C₀ * s := by
  intro hProd hSH m m' k X hXm hbd ω L hL
  obtain ⟨hE0, hE1, hAff⟩ := hSH
  -- 1. Data that do not depend on the maps: `Z` with `ProdChar(X, Z)`, the constant `c` of (Aff),
  -- a bound `C₁` for `|dω|` and `B = M(X)`.
  obtain ⟨Z, hZ⟩ := hProd m k X hXm
  obtain ⟨c, hc0, hc⟩ := hAff m m' k
  obtain ⟨C₁, hC₁0, hC₁⟩ := Submission.br_la_testForm_covectorNorm_bounded m' (k + 1) univ
    (exteriorDerivativeTestOn univ k ω)
  obtain ⟨B, hB0, hXB⟩ : ∃ B : ℝ, 0 ≤ B ∧ X.mass ≤ ENNReal.ofReal B :=
    ⟨X.mass.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hXm.ne).ge⟩
  cases k with
  | zero =>
    -- 2. `k = 0`: `C₀ = c B C₁`.
    refine ⟨c * B * C₁, mul_nonneg (mul_nonneg hc0 hB0) hC₁0.le, ?_⟩
    intro F₀ F₁ O s η₀ η₁ hF₀ hF₁ hO hXO hs hdist hD₀ hD₁ hF₀p hHp hη₀ hη₁
    -- (i) The affine homotopy `H = H[F₀, F₁]` has ends `F₀`, `F₁` and is `C^∞`.
    set H : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))) with hH
    obtain ⟨hH₀, hH₁, hHs⟩ := Submission.dph_lpf_cmp_affine_homotopy m m' F₀ F₁ H hH
    have hHsm := hHs hF₀ hF₁
    -- (ii) `η′ = H^# dω` near `[0, 1] × spt X`, as `H` is proper there.
    obtain ⟨η', -, N, hN, hXN, -, -, hη', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (0 + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) (exteriorDerivativeTestOn univ 0 ω)
    -- (iii) The homotopy formula (E0), its end conditions rewritten by (i):
    -- `X(η₁) − X(η₀) = Z(η′)`.
    rw [hE0 m m' X Z H hXm hZ hHsm hHp ω η₀ η₁ η' (by rw [hH₀]; exact hη₀)
      (by rw [hH₁]; exact hη₁) ⟨N, hN, hXN, hη'⟩]
    -- (iv)–(v) The affine estimate (Aff) with `ψ = dω`: `|Z(η′)| ≤ c s L⁰ B C₁ = C₀ s`.
    calc |Z η'| ≤ c * s * L ^ 0 * B * C₁ :=
          hc X Z F₀ F₁ O s L B hs hL hB0 hXB hZ hF₀ hF₁ hO hXO hdist hD₀ hD₁ hF₀p
            (exteriorDerivativeTestOn univ 0 ω) C₁ η' hC₁ ⟨N, hN, hXN, hη'⟩
      _ = c * B * C₁ * s := by ring
  | succ j =>
    -- 3. `k = j + 1`, further data that do not depend on the maps: `B′ = M(∂X) < ∞`, `Z′` with
    -- `ProdChar(∂X, Z′)`, the constant `c′` of (Aff) in degree `j`, a bound `C₂` for `|ω|`, and
    -- `spt ∂X ⊆ spt X` with `spt ∂X` closed.
    have hbm : X.boundary.mass < ∞ := hbd j X rfl HEq.rfl
    obtain ⟨B', hB'0, hXB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧ X.boundary.mass ≤ ENNReal.ofReal B' :=
      ⟨X.boundary.mass.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hbm.ne).ge⟩
    obtain ⟨Z', hZ'⟩ := hProd m j X.boundary hbm
    obtain ⟨c', hc'0, hc'⟩ := hAff m m' j
    obtain ⟨C₂, hC₂0, hC₂⟩ := Submission.br_la_testForm_covectorNorm_bounded m' (j + 1) univ ω
    have hsub : X.boundary.support ⊆ X.support := Submission.iwl_cr_support_lemmas.1 m j univ X
    have hcl : IsClosed X.boundary.support := isClosed_univ.sdiff X.boundary.isOpen_zeroRegion
    refine ⟨c * L ^ (j + 1) * B * C₁ + c' * L ^ j * B' * C₂,
      add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (pow_nonneg hL _)) hB0) hC₁0.le)
        (mul_nonneg (mul_nonneg (mul_nonneg hc'0 (pow_nonneg hL _)) hB'0) hC₂0.le), ?_⟩
    intro F₀ F₁ O s η₀ η₁ hF₀ hF₁ hO hXO hs hdist hD₀ hD₁ hF₀p hHp hη₀ hη₁
    -- 4. The affine homotopy `H = H[F₀, F₁]`, as in 2(i).
    set H : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))) with hH
    obtain ⟨hH₀, hH₁, hHs⟩ := Submission.dph_lpf_cmp_affine_homotopy m m' F₀ F₁ H hH
    have hHsm := hHs hF₀ hF₁
    -- (i) `η′ = H^# dω` and `θ′ = H^# ω` near `[0, 1] × spt X`.
    obtain ⟨η', -, N, hN, hXN, -, -, hη', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (j + 1 + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) (exteriorDerivativeTestOn univ (j + 1) ω)
    obtain ⟨θ', -, N', hN', hXN', -, -, hθ', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (j + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) ω
    -- (ii) The homotopy formula (E1): `X(η₁) − X(η₀) = Z(η′) + Z′(θ′)`.
    rw [hE1 m m' j X Z Z' H hXm hZ hZ' hHsm hHp ω η₀ η₁ η' θ' (by rw [hH₀]; exact hη₀)
      (by rw [hH₁]; exact hη₁) ⟨N, hN, hXN, hη'⟩ ⟨N', hN', hXN', hθ'⟩]
    -- (iii) (Aff) for `X` with `ψ = dω`: `|Z(η′)| ≤ c s L^(j+1) B C₁`.
    have hest : |Z η'| ≤ c * s * L ^ (j + 1) * B * C₁ :=
      hc X Z F₀ F₁ O s L B hs hL hB0 hXB hZ hF₀ hF₁ hO hXO hdist hD₀ hD₁ hF₀p
        (exteriorDerivativeTestOn univ (j + 1) ω) C₁ η' hC₁ ⟨N, hN, hXN, hη'⟩
    -- (iv) `F₀` is proper on the closed subset `spt ∂X` of `spt X`.
    have hF₀p' : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.boundary.support) := by
      intro K hK
      have h := (hF₀p K hK).inter_right hcl
      rwa [inter_assoc, inter_eq_right.mpr hsub] at h
    -- (v) (Aff) for `∂X` with `ψ = ω`, as `[0, 1] × spt ∂X ⊆ [0, 1] × spt X ⊆ N′`:
    -- `|Z′(θ′)| ≤ c′ s L^j B′ C₂`.
    have hest' : |Z' θ'| ≤ c' * s * L ^ j * B' * C₂ :=
      hc' X.boundary Z' F₀ F₁ O s L B' hs hL hB'0 hXB' hZ' hF₀ hF₁ hO (hsub.trans hXO) hdist hD₀
        hD₁ hF₀p' ω C₂ θ' hC₂ ⟨N', hN', fun y hy => hXN' ⟨hy.1, hsub hy.2⟩, hθ'⟩
    -- (vi) Sum the two estimates.
    calc |Z η' + Z' θ'| ≤ |Z η'| + |Z' θ'| := abs_add_le _ _
      _ ≤ c * s * L ^ (j + 1) * B * C₁ + c' * s * L ^ j * B' * C₂ := add_le_add hest hest'
      _ = (c * L ^ (j + 1) * B * C₁ + c' * L ^ j * B' * C₂) * s := by ring
/-- Comparison lemma (Step 1 of the Lipschitz push-forward): if `C^∞` maps `Gₙ`, `G'ₙ` with
eventual derivative bounds `L`, `L'` near `spt X` both converge uniformly to a map `G` proper on
`spt X`, then pull-backs `ηₙ`, `η'ₙ` of `ω` compatible with `Gₙ`, `G'ₙ` near `spt X` satisfy
`X(η'ₙ) − X(ηₙ) → 0`.  For `ε > 0`, eventually `Gₙ` and `G'ₙ` are `ε`-close to `G` on
`O ∩ O' ⊇ spt X`; so `Gₙ` is proper on `spt X` and the affine homotopy between `Gₙ` and `G'ₙ` is
proper on `[0,1] × spt X` (properness transfer), `dist(G'ₙ, Gₙ) ≤ 2ε` on `O ∩ O'`, and the core
estimate gives `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε`, which is `< δ` for `ε = δ/(2C₀ + 1)`. -/
theorem Submission.dph_lpf_comparison : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) := by
  intro hProd hSH m m' k X G hXm hbd hG Gj Gj' O O' L L' hO hXO hGj hGjL hGjU hO' hXO' hGj'
    hGjL' hGjU' ω ηj ηj' hηj hηj'
  -- Step 1 (core estimate), with the common derivative bound `L'' = max (max L L') 0`: a
  -- constant `C₀ ≥ 0` that does not depend on the maps.
  obtain ⟨C₀, hC₀, hcore⟩ := Submission.dph_lpf_cmp_core_estimate hProd hSH m m' k X hXm hbd ω
    (max (max L L') 0) (le_max_right _ _)
  -- `spt X = univ \ zeroRegion X` is closed.
  have hXc : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- Step 4: `ε = δ / (2C₀ + 1)`.
  have hpos : 0 < 2 * C₀ + 1 := by linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (2 * C₀ + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ div_pos hδ hpos
  -- Step 2: eventually the derivative bounds, `ε`-closeness to `G` and the compatibilities hold.
  filter_upwards [hGjL, hGjL', Metric.tendstoUniformlyOn_iff.1 hGjU ε hε0,
    Metric.tendstoUniformlyOn_iff.1 hGjU' ε hε0, hηj, hηj'] with n hL hL' hd hd' hc hc'
  -- Step 3: `Gₙ` and `G'ₙ` are `ε`-close to `G` on `spt X`, so properness transfers to `Gₙ` on
  -- `spt X` and to the affine homotopy between them on `cyl(spt X)`.
  have hd₀ : ∀ x ∈ X.support, dist (Gj n x) (G x) ≤ ε := fun x hx =>
    (dist_comm _ _).trans_le (hd x (hXO hx)).le
  have hd₁ : ∀ x ∈ X.support, dist (Gj' n x) (G x) ≤ ε := fun x hx =>
    (dist_comm _ _).trans_le (hd' x (hXO' hx)).le
  have hest : |X (ηj' n) - X (ηj n)| ≤ C₀ * (2 * ε) :=
    hcore (Gj n) (Gj' n) (O ∩ O') (2 * ε) (ηj n) (ηj' n) (hGj n) (hGj' n) (hO.inter hO')
      (subset_inter hXO hXO') (by linarith)
      (fun x hx => by
        linarith [dist_triangle (Gj' n x) (G x) (Gj n x), dist_comm (Gj' n x) (G x),
          hd x hx.1, hd' x hx.2])
      (fun x hx => (hL x hx.1).trans ((le_max_left L L').trans (le_max_left _ 0)))
      (fun x hx => (hL' x hx.2).trans ((le_max_right L L').trans (le_max_left _ 0)))
      (Submission.dph_lpf_proper_transfer.1 m m' G (Gj n) X.support ε hXc (hGj n).continuous
        hG hd₀)
      (Submission.dph_lpf_proper_transfer.2 m m' G (Gj n) (Gj' n) X.support ε hXc
        (hGj n).continuous (hGj' n).continuous hG hd₀ hd₁)
      hc hc'
  -- `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε = δ · 2C₀/(2C₀ + 1) < δ`.
  rw [Real.dist_eq, sub_zero]
  calc |X (ηj' n) - X (ηj n)| ≤ C₀ * (2 * ε) := hest
    _ = 2 * C₀ * δ / (2 * C₀ + 1) := by rw [hε]; ring
    _ < δ := by
      rw [div_lt_iff₀ hpos]
      linarith
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

/-- **A bounded linear functional on `𝒟ⁿ(U)` is a current of mass at most `B`** (Simon Ch. 6,
2.1 and 2.4; fact (F5/F6) for the Lipschitz push-forward).  If `T₀` is additive and homogeneous
and `|T₀(ω)| ≤ B·C` whenever `|ω(y)| ≤ C` for all `y`, then `T₀` is a current `S`: its
sequential continuity is `fiw_ims_sc_continuous_of_bound` with `A := B` on every compact
`K ⊆ U`, and every mass-admissible `ω` (`|ω| ≤ 1`) has `S(ω) ≤ |T₀(ω)| ≤ B·1`, so the
supremum `M(S)` is at most `B`. -/
theorem Submission.dph_lpf_current_of_bounded_functional : ∀ (P n : ℕ) (U : Set (Eucl P)) (T₀ : TestFormOn U n → ℝ) (B : ℝ), (∀ ω η : TestFormOn U n, T₀ (ω + η) = T₀ ω + T₀ η) → (∀ (c : ℝ) (ω : TestFormOn U n), T₀ (c • ω) = c * T₀ ω) → (∀ (ω : TestFormOn U n) (C : ℝ), (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) y) ≤ C) → |T₀ ω| ≤ B * C) → ∃ S : GeometricCurrentOn U n, (∀ ω, S ω = T₀ ω) ∧ S.mass ≤ ENNReal.ofReal B := by
  intro P n U T₀ B hadd hsmul hbound
  -- Additivity and homogeneity make `T₀` an `ℝ`-linear map on `𝒟ⁿ(U)`.
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := T₀
      map_add' := hadd
      map_smul' := fun c ω => by rw [RingHom.id_apply, smul_eq_mul]; exact hsmul c ω }
  -- Continuity: on every compact `K ⊆ U` the bound holds with `A := B`.
  refine ⟨⟨L, fun ωs hωs => Submission.fiw_ims_sc_continuous_of_bound P n U T₀
    (fun _ _ _ => ⟨B, fun ω C _ _ hω => hbound ω C hω⟩) ωs hωs⟩, fun _ => rfl, ?_⟩
  -- Mass: an admissible `ω` has `|ω| ≤ 1`, so `S(ω) ≤ |T₀(ω)| ≤ B · 1 = B`.
  apply sSup_le
  rintro _ ⟨ω, hω, rfl⟩
  exact ENNReal.ofReal_le_ofReal
    ((le_abs_self _).trans ((hbound ω 1 hω.2).trans_eq (mul_one B)))
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
/-- Counting identity: for any family `u` of vectors of `ℝ^P` and any `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = k! ∑_{I strictly increasing} φ(u_{I 0}, …, u_{I (k-1)})²`,
where `I` ranges over all maps `Fin k → Fin P`. -/
theorem Submission.slicing_mb_wn_sq_sum_eq_factorial_mul :
    ∀ (P k : ℕ) (u : Fin P → Eucl P) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        (k.factorial : ℝ) * ∑ I : Fin k → Fin P,
          if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  classical
  set g : (Fin k → Fin P) → ℝ := fun I => (φ (fun i => u (I i))) ^ 2
  -- A non-injective `I` repeats a vector of `u ∘ I`, so `φ (u ∘ I) = 0`.
  have h0 : ∀ I : Fin k → Fin P, ¬Function.Injective I → g I = 0 := by
    intro I hI
    have hv : ¬Function.Injective (fun i => u (I i)) :=
      fun h => hI fun a b hab => h (by simp only [hab])
    simp only [g, φ.map_eq_zero_of_not_injective _ hv, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  -- `φ (u ∘ I ∘ σ) = sign σ • φ (u ∘ I)`, so the square is invariant under permutations.
  have hperm : ∀ (I : Fin k → Fin P) (σ : Equiv.Perm (Fin k)), g (I ∘ σ) = g I := by
    intro I σ
    have h : φ (fun i => u ((I ∘ σ) i)) = Equiv.Perm.sign σ • φ (fun i => u (I i)) :=
      φ.toAlternatingMap.map_perm (fun i => u (I i)) σ
    simp only [g, h]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h' <;> simp [h']
  -- Write both sides as sums over the injective, resp. strictly increasing, maps.
  have hL : ∑ I, g I = ∑ I ∈ Finset.univ.filter Function.Injective, g I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · exact h0 I h
  have hR : (∑ I : Fin k → Fin P, if StrictMono I then g I else 0) =
      ∑ I ∈ Finset.univ.filter StrictMono, g I := (Finset.sum_filter _ _).symm
  -- `(σ, β) ↦ β ∘ σ` is a bijection from permutations × strictly increasing maps onto the
  -- injective maps, with inverse `I ↦ ((sort I)⁻¹, I ∘ sort I)`.
  have hbij : ∑ I ∈ Finset.univ.filter Function.Injective, g I =
      ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))) ×ˢ Finset.univ.filter StrictMono,
        g (p.2 ∘ p.1) := by
    refine Finset.sum_nbij' (fun I => ((Tuple.sort I)⁻¹, I ∘ Tuple.sort I))
      (fun p => p.2 ∘ p.1) ?_ ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
      exact (Tuple.monotone_sort I).strictMono_of_injective (hI.comp (Tuple.sort I).injective)
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.injective.comp σ.injective
    · intro I _
      funext i
      simp
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      -- sorting `β ∘ σ` recovers the strictly increasing `β`
      have hsorted : (β ∘ σ) ∘ Tuple.sort (β ∘ σ) = β := by
        rw [Tuple.comp_perm_comp_sort_eq_comp_sort,
          (Tuple.sort_eq_refl_iff_monotone).2 hp.monotone]
        rfl
      have hσ : σ * Tuple.sort (β ∘ σ) = 1 := by
        ext i
        have := congrFun hsorted i
        simp only [Function.comp_apply] at this
        simpa using congrArg Fin.val (hp.injective this)
      have hinv : (Tuple.sort (β ∘ σ))⁻¹ = σ := by
        rw [inv_eq_iff_eq_inv]
        exact eq_inv_of_mul_eq_one_right hσ
      simp only [hinv, hsorted]
    · intro I _
      congr 1
      funext i
      simp
  -- Each permutation contributes `∑_β g β`, and there are `k!` permutations.
  rw [hL, hbij, hR, Finset.sum_product]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- Basis independence of the full coefficient sum (Parseval's identity, one slot at a time): for
orthonormal bases `u`, `v` of `ℝ^P` and a `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = ∑_I φ(v_{I 0}, …, v_{I (k-1)})²`, both sums over all index maps
`I : Fin k → Fin P`.  Induction on `k`: write `I = (i, J)` and `φ(w_I) = (φ.curryLeft w_i)(w_J)`,
replace `u` by `v` in the last `k` slots by the induction hypothesis for `φ.curryLeft (u i)`, then
in slot `0` by `OrthonormalBasis.norm_dual` for the functional `z ↦ (φ.curryLeft z)(v_J)`. -/
theorem Submission.slicing_mb_wn_sq_sum_onb_invariant :
    ∀ (P k : ℕ) (u v : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        ∑ I : Fin k → Fin P, (φ (fun i => v (I i))) ^ 2 := by
  intro P k u v
  induction k with
  | zero =>
    -- Both families are the empty tuple.
    intro φ
    exact Fintype.sum_congr _ _ fun I => by
      rw [Subsingleton.elim (fun i => u (I i)) (fun i => v (I i))]
  | succ k ih =>
    intro φ
    -- Split `I = Fin.cons i J`; then `φ(w_I) = (φ.curryLeft w_i)(w_J)`.
    have hsplit : ∀ w : OrthonormalBasis (Fin P) ℝ (Eucl P),
        ∑ I : Fin (k + 1) → Fin P, (φ (fun i => w (I i))) ^ 2 =
          ∑ i : Fin P, ∑ J : Fin k → Fin P, (φ.curryLeft (w i) (fun j => w (J j))) ^ 2 := by
      intro w
      rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Fin P).sum_comp]
      refine Fintype.sum_congr _ _ fun p => ?_
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    -- Slots `1, …, k`: the induction hypothesis for each `k`-covector `φ.curryLeft (u i)`.
    rw [hsplit u, hsplit v]
    simp_rw [ih]
    -- Slot `0`: for each `J`, Parseval for `ℓ_J z = (φ.curryLeft z)(v_J)` in the bases `u`, `v`.
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun J => ?_
    let ℓ : StrongDual ℝ (Eucl P) :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (fun j => v (J j))).comp φ.curryLeft
    have hu := u.norm_dual ℓ
    have hv := v.norm_dual ℓ
    simp only [ℓ, ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.apply_apply] at hu hv
    rw [← hu, ← hv]

/-- The Euclidean coefficient norm of a `k`-covector can be computed in any orthonormal basis
`u` of `ℝ^P` (Simon Ch. 6, 1.5–1.6 and Remark 2.6): `|φ|² = ∑_{I increasing} φ(u_I)²`.
With `e` the standard basis used by `covectorEuclideanNorm` and `N_w(φ) = ∑_{all I} φ(w_I)²`,
`k! |φ|² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`, and `k! ≠ 0`. -/
theorem Submission.slicing_mb_wn_norm_sq_eq_onb_sum :
    ∀ (P k : ℕ) (u : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      covectorEuclideanNorm φ ^ 2 =
        ∑ I : Fin k → Fin P, if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  -- `k! ∑_{I increasing} φ(e_I)² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`.
  have key := (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k
      (EuclideanSpace.basisFun (Fin P) ℝ) φ).symm.trans
    ((Submission.slicing_mb_wn_sq_sum_onb_invariant P k
      (EuclideanSpace.basisFun (Fin P) ℝ) u φ).trans
        (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k u φ))
  -- `|φ|² = ∑_{I increasing} φ(e_I)²`: the radicand is a sum of squares and zeros.
  rw [covectorEuclideanNorm, Real.sq_sqrt]
  · exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) key
  · exact Finset.sum_nonneg fun I _ => by split_ifs <;> positivity

/-- Full tuple sum of squared coefficients in the standard basis `e` of `ℝ^m`: for a `j`-covector
`γ`, `∑_i γ(e_{i 0}, …, e_{i (j-1)})² = j! |γ|²`, the sum over all index maps `i : Fin j → Fin m`.
The counting identity turns the left side into `j! ∑_{I increasing} γ(e_I)²`, and the
orthonormal-basis formula for `|γ|²`, applied to `e` itself, identifies that sum with `|γ|²`. -/
theorem Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul :
    ∀ (m j : ℕ) (γ : Covector (Eucl m) j),
      ∑ i : Fin j → Fin m, (γ (fun k => EuclideanSpace.basisFun (Fin m) ℝ (i k))) ^ 2 =
        (j.factorial : ℝ) * covectorEuclideanNorm γ ^ 2 := by
  intro m j γ
  rw [Submission.slicing_mb_wn_norm_sq_eq_onb_sum m j (EuclideanSpace.basisFun (Fin m) ℝ) γ]
  exact Submission.slicing_mb_wn_sq_sum_eq_factorial_mul m j (EuclideanSpace.basisFun (Fin m) ℝ) γ
/-- One-slot bound: for `L : ℝ^P → ℝ^Q` and a linear functional `f` on `ℝ^Q`,
`∑_a f(L e_a)² ≤ ‖L‖² ∑_b f(e′_b)²`.  The Riesz vector `g = (f(e′_b))_b` gives `f = ⟨g, ·⟩`
and the test vector `u = (f(L e_a))_a` has `f(L u) = |u|²`, so Cauchy–Schwarz and the operator
norm give `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`; cancel `|u|` and square. -/
theorem Submission.iwl_sp_pn_sum_sq_comp_basis_le : ∀ (P Q : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (f : Eucl Q →ₗ[ℝ] ℝ), ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 ≤ ‖L‖ ^ 2 * ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 := by
  intro P Q L f
  -- The Riesz vector `g` of `f`: `f y = ⟨g, y⟩` and `|g|² = ∑_b f(e′_b)²`.
  set g : Eucl Q := WithLp.toLp 2 (fun b => f (EuclideanSpace.basisFun (Fin Q) ℝ b)) with hg_def
  have hf : ∀ y : Eucl Q, f y = inner ℝ g y := by
    intro y
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hg_def]
  have hg : ‖g‖ ^ 2 = ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  -- The test vector `u`: `|u|² = ∑_a f(L e_a)²` and `f(L u) = |u|²`.
  set u : Eucl P := WithLp.toLp 2 (fun a => f (L (EuclideanSpace.basisFun (Fin P) ℝ a)))
    with hu_def
  have hu : ‖u‖ ^ 2 = ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hfLu : f (L u) = ‖u‖ ^ 2 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr u]
    rw [map_sum, map_sum, hu]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hu_def, sq]
  -- Cauchy–Schwarz and the operator norm: `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`.
  have key : ‖u‖ ^ 2 ≤ ‖g‖ * (‖L‖ * ‖u‖) := by
    rw [← hfLu, hf]
    calc inner ℝ g (L u) ≤ ‖g‖ * ‖L u‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * (‖L‖ * ‖u‖) := mul_le_mul_of_nonneg_left (L.le_opNorm u) (norm_nonneg _)
  -- Cancel `|u|` (trivial if `|u| = 0`), then square.
  have hle : ‖u‖ ≤ ‖L‖ * ‖g‖ := by
    rcases (norm_nonneg u).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · have : ‖u‖ * ‖u‖ ≤ (‖L‖ * ‖g‖) * ‖u‖ := by nlinarith [key]
      exact le_of_mul_le_mul_right this hpos
  rw [← hu, ← hg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Multilinear tensor-power bound: for every continuous linear `L : ℝ^P → ℝ^Q` and every
`j`-multilinear `β : (ℝ^Q)^j → ℝ` (not necessarily alternating or continuous),
`∑_{i : Fin j → Fin P} β(L e_{i(1)}, …, L e_{i(j)})²`
`≤ (‖L‖²)^j ∑_{i : Fin j → Fin Q} β(e′_{i(1)}, …, e′_{i(j)})²`,
with `e`, `e′` the standard bases.  Induction on `j`, generalizing `β`: split the sums over
`Fin (j + 1) → Fin n` along `Fin.cons`, apply the inductive hypothesis to `β.curryLeft (L e_a)`,
exchange the sums and bound each slot functional `y ↦ β(Fin.cons y (e′ ∘ i″))` by the one-slot
estimate `Submission.iwl_sp_pn_sum_sq_comp_basis_le`. -/
theorem Submission.iwl_sp_pn_multilinear_sum_sq_le :
    ∀ (P Q j : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (β : MultilinearMap ℝ (fun _ : Fin j => Eucl Q) ℝ),
      ∑ i : Fin j → Fin P, (β (fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i k)))) ^ 2 ≤
        (‖L‖ ^ 2) ^ j *
          ∑ i : Fin j → Fin Q, (β (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k))) ^ 2 := by
  intro P Q j L
  induction j with
  | zero =>
    -- Both sums have the single empty tuple as index, and both arguments of `β` are empty.
    intro β
    rw [Fintype.sum_unique, Fintype.sum_unique, pow_zero, one_mul]
    exact (congrArg (fun v => β v ^ 2) (Subsingleton.elim _ _)).le
  | succ j ih =>
    intro β
    -- Sums over `Fin (j + 1) → Fin n` split along `Fin.cons` (`Fin.consEquiv`).
    have split : ∀ (n : ℕ) (G : (Fin (j + 1) → Fin n) → ℝ),
        ∑ i, G i = ∑ a : Fin n, ∑ i' : Fin j → Fin n, G (Fin.cons a i') := by
      intro n G
      rw [← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin n) _ _ fun _ => rfl).symm
    -- The slot functionals `y ↦ β (Fin.cons y w)` are linear.
    let slot : (Fin j → Eucl Q) → Eucl Q →ₗ[ℝ] ℝ := fun w =>
      { toFun := fun y => β (Fin.cons y w)
        map_add' := fun x y => β.cons_add w x y
        map_smul' := fun c x => β.cons_smul w c x }
    calc ∑ i : Fin (j + 1) → Fin P, (β fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i k))) ^ 2
        = ∑ a : Fin P, ∑ i' : Fin j → Fin P,
            (β.curryLeft (L (EuclideanSpace.basisFun (Fin P) ℝ a))
              fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i' k))) ^ 2 := by
          rw [split P]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ =>
            congrArg (fun v => β v ^ 2)
              (Fin.comp_cons (fun p => L (EuclideanSpace.basisFun (Fin P) ℝ p)) a i')
      -- the inductive hypothesis for `β.curryLeft (L e_a)`
      _ ≤ ∑ a : Fin P, (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q,
            (β.curryLeft (L (EuclideanSpace.basisFun (Fin P) ℝ a))
              fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k)) ^ 2 :=
          Finset.sum_le_sum fun a _ => ih _
      _ = (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q, ∑ a : Fin P,
            (slot (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))
              (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          rfl
      -- the one-slot bound for each slot functional
      _ ≤ (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q, ‖L‖ ^ 2 * ∑ b : Fin Q,
            (slot (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))
              (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i'' _ => Submission.iwl_sp_pn_sum_sq_comp_basis_le P Q L _)
            (by positivity)
      _ = (‖L‖ ^ 2) ^ (j + 1) * ∑ b : Fin Q, ∑ i'' : Fin j → Fin Q,
            (β (Fin.cons (EuclideanSpace.basisFun (Fin Q) ℝ b)
              fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm, pow_succ (‖L‖ ^ 2) j, mul_assoc]
          rfl
      _ = (‖L‖ ^ 2) ^ (j + 1) * ∑ i : Fin (j + 1) → Fin Q,
            (β fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k)) ^ 2 := by
          rw [split Q]
          exact congrArg _ (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i'' _ =>
            congrArg (fun v => β v ^ 2)
              (Fin.comp_cons (fun p => EuclideanSpace.basisFun (Fin Q) ℝ p) b i'').symm)

/-- Pullback bound for the Euclidean covector norm: for `L : ℝ^P → ℝ^Q` and a `j`-covector `α`
on `ℝ^Q`, `|L^#α| ≤ ‖L‖^j |α|`.  The multilinear bound
`Submission.iwl_sp_pn_multilinear_sum_sq_le` for `β := α` gives
`∑_i α(L e∘i)² ≤ (‖L‖²)^j ∑_i α(e′∘i)²`, and `α(L e∘i) = (L^#α)(e∘i)` by definition.  By
`Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul` the two sums over all index tuples are
`j! |L^#α|²` and `j! |α|²`; cancel `j! > 0` and take square roots. -/
theorem Submission.iwl_sp_covectorEuclideanNorm_pullback_le : ∀ (P Q j : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (α : Covector (Eucl Q) j), covectorEuclideanNorm (α.compContinuousLinearMap L) ≤ ‖L‖ ^ j * covectorEuclideanNorm α := by
  intro P Q j L α
  -- Sums over all index tuples: `j! |L^#α|²` on `ℝ^P` and `j! |α|²` on `ℝ^Q`.
  have hP := Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul P j (α.compContinuousLinearMap L)
  have hQ := Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul Q j α
  -- The multilinear bound for `β := α`.
  have hβ := Submission.iwl_sp_pn_multilinear_sum_sq_le P Q j L α.toMultilinearMap
  have key : (j.factorial : ℝ) * covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2 ≤
      (j.factorial : ℝ) * (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 :=
    calc (j.factorial : ℝ) * covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2
        = ∑ i : Fin j → Fin P,
            (α.compContinuousLinearMap L fun k => EuclideanSpace.basisFun (Fin P) ℝ (i k)) ^ 2 :=
          hP.symm
      -- `(L^#α)(e∘i) = α(L e∘i)` holds by definition (`compContinuousLinearMap_apply`).
      _ ≤ (‖L‖ ^ 2) ^ j * ∑ i : Fin j → Fin Q,
            (α fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k)) ^ 2 := hβ
      _ = (j.factorial : ℝ) * (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 := by
          rw [hQ]
          ring
  -- Cancel `j! > 0`, then take square roots of nonnegative quantities.
  have hsq : covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2 ≤
      (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 :=
    le_of_mul_le_mul_left key (by exact_mod_cast j.factorial_pos)
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg (norm_nonneg L) j) (covectorEuclideanNorm_nonneg α))

/-- Bounded compatible pull-back forms (Steps 2–3 of the Lipschitz push-forward construction): if
`f` is `C^∞`, proper on `A`, and `‖Df‖ ≤ Λ` on an open `O ⊇ A`, every `ω ∈ 𝒟ᵏ(ℝ^{m′})` has a
pull-back `η ∈ 𝒟ᵏ(ℝ^m)` with `η = f^#ω` on an open `N ⊇ A` and `|η(x)| ≤ Λ^k C` whenever
`|ω| ≤ C`.  The cut-off pull-back `η = ζ f^#ω ∈ 𝒟ᵏ(O)` of
`Submission.iwl_sp_exists_compatible_testForm` is also a test form on `ℝ^m`; on `O`,
`|ζ f^#ω| = ζ |f^#ω| ≤ ‖Df‖^k |ω ∘ f| ≤ Λ^k C` by
`Submission.iwl_sp_covectorEuclideanNorm_pullback_le`, and off `O ⊇ spt η` it vanishes. -/
theorem Submission.dph_lpfex_bounded_compatible_form :
    ∀ (m m' k : ℕ) (f : Eucl m → Eucl m') (A O : Set (Eucl m)) (Λ : ℝ≥0), IsOpen O → A ⊆ O →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ x ∈ O, ‖fderiv ℝ f x‖ ≤ Λ) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (f ⁻¹' K ∩ A)) →
      ∀ ω : TestFormOn (univ : Set (Eucl m')) k, ∃ η : TestFormOn (univ : Set (Eucl m)) k,
        (∃ N : Set (Eucl m), IsOpen N ∧ A ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl m) k) x =
          ((ω : DifferentialForm (Eucl m') k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∧
        ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
          ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C := by
  intro m m' k f A O Λ hO hAO hf hDf hprop ω
  -- 1. The cut-off pull-back `η₀ = ζ f^#ω ∈ 𝒟ᵏ(O)` with `0 ≤ ζ ≤ 1`, equal to `f^#ω` on `N ⊇ A`.
  obtain ⟨η₀, ζ, N, hN, hAN, hζ, hη₀, hη₀N, -⟩ :=
    Submission.iwl_sp_exists_compatible_testForm m m' k O univ A f hO hAO hf
      (fun K hK _ => hprop K hK) ω
  obtain ⟨hη₀test, hη₀O⟩ := η₀.property
  -- 2. `spt η₀ ⊆ O ⊆ ℝ^m`, so the same form is a test form on `ℝ^m`.
  refine ⟨⟨(η₀ : DifferentialForm (Eucl m) k), hη₀test, subset_univ _⟩, ⟨N, hN, hAN, hη₀N⟩,
    fun C hC x => ?_⟩
  show covectorEuclideanNorm ((η₀ : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C
  -- 3. Homogeneity `|c γ| = |c| |γ|`: every squared coefficient scales by `c²`.
  have hsmul : ∀ (c : ℝ) (γ : Covector (Eucl m) k),
      covectorEuclideanNorm (c • γ) = |c| * covectorEuclideanNorm γ := by
    intro c γ
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  -- 4. `C ≥ |ω(0)| ≥ 0`.
  have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
  by_cases hx : x ∈ O
  · -- On `O`: `|ζ f^#ω| = ζ |f^#ω| ≤ |f^#ω| ≤ ‖Df‖^k |ω ∘ f| ≤ Λ^k C`.
    rw [hη₀ x, hsmul, abs_of_nonneg (hζ x).1]
    calc _ ≤ covectorEuclideanNorm
          (((ω : DifferentialForm (Eucl m') k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hζ x).2
      _ ≤ ‖fderiv ℝ f x‖ ^ k * covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) (f x)) :=
          Submission.iwl_sp_covectorEuclideanNorm_pullback_le m m' k _ _
      _ ≤ (Λ : ℝ) ^ k * C :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDf x hx) k) (hC _)
            (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.coe_nonneg k)
  · -- Off `O ⊇ spt η₀` the form vanishes.
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hη₀O h), covectorEuclideanNorm_zero]
    exact mul_nonneg (pow_nonneg Λ.coe_nonneg k) hC0
/-- Simon Ch. 6, 3.6–3.9 (Lipschitz push-forward, existence), the Cauchy argument of Step 6: a
real sequence `a` converges if `a (q i) - a (p i) → 0` for all index maps `p, q → ∞`. -/
theorem Submission.dph_lpfex_tendsto_of_index_maps :
    ∀ a : ℕ → ℝ, (∀ p q : ℕ → ℕ, Tendsto p atTop atTop → Tendsto q atTop atTop →
      Tendsto (fun i => a (q i) - a (p i)) atTop (𝓝 0)) → ∃ s : ℝ, Tendsto a atTop (𝓝 s) := by
  intro a ha
  -- 1. `a` is Cauchy; otherwise some `ε > 0` has `ε ≤ |a m - a n|` for some `m, n ≥ N`, every `N`.
  have hcauchy : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    by_contra hne
    push Not at hne
    obtain ⟨ε, hε, hgap⟩ := hne
    -- 2. Index maps `p N, q N ≥ N` with `ε ≤ |a (p N) - a (q N)|`; both tend to infinity.
    choose p hp q hq hpq using hgap
    have hpt : Tendsto p atTop atTop := tendsto_atTop_mono hp tendsto_id
    have hqt : Tendsto q atTop atTop := tendsto_atTop_mono hq tendsto_id
    -- 3. The hypothesis gives `|a (q i) - a (p i)| < ε` for some `i`, contradicting the gap.
    obtain ⟨i, hi⟩ := (Metric.tendsto_nhds.1 (ha p q hpt hqt) ε hε).exists
    have hgap_i := hpq i
    rw [Real.dist_eq, sub_zero] at hi
    rw [Real.dist_eq, abs_sub_comm] at hgap_i
    exact lt_irrefl ε (hgap_i.trans_lt hi)
  -- 4. `ℝ` is complete.
  exact cauchySeq_tendsto_of_complete hcauchy
/-- Support of a push-forward (Simon Ch. 6, 2.23 and 3.6, pp. 139, 147): if `S ω` is the limit of
`X` on forms equal to the pull-back of `ω` by continuous `G_n` near `spt X`, and `G_n → G`
uniformly on `spt X`, then `spt S ⊆ closure (G(spt X))`. -/
theorem Submission.dph_lpfex_support_subset_closure_image :
    ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k)
      (S : GeometricCurrentOn (univ : Set (Eucl m')) k) (G : Eucl m → Eucl m')
      (Gj : ℕ → Eucl m → Eucl m'),
      (∀ n, Continuous (Gj n)) → TendstoUniformlyOn Gj G atTop X.support →
      (∀ (ω : TestFormOn (univ : Set (Eucl m')) k)
          (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧
          ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x)) →
        Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) →
      S.support ⊆ closure (G '' X.support) := by
  intro m m' k X S G Gj hGj hunif hchar y hy
  by_contra hyc
  -- 1. A ball `B(y, ε)` misses `closure (G(spt X))`, so `ε ≤ dist (G x) y` on `spt X`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl y hyc
  have hfar : ∀ x ∈ X.support, ε ≤ dist (G x) y := by
    intro x hx
    by_contra hlt
    exact hball (mem_ball.mpr (not_le.mp hlt)) (subset_closure (mem_image_of_mem G hx))
  have hρ : 0 < ε / 3 := by positivity
  -- 2. `S` vanishes on `B(y, ε/3)`: the zero forms are eventually compatible with `ω`.
  have hvan : S.VanishesOn (ball y (ε / 3)) := by
    intro ω hω
    have hT := hchar ω (fun _ => 0) <| by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (ε / 3) hρ] with n hn
      refine ⟨Gj n ⁻¹' (tsupport (ω : DifferentialForm (Eucl m') k))ᶜ,
        (isClosed_tsupport _).isOpen_compl.preimage (hGj n), ?_, ?_⟩
      · -- `spt X ⊆ G_n⁻¹((spt ω)ᶜ)`, by the triangle inequality.
        intro x hx hmem
        have h1 : dist (Gj n x) y < ε / 3 := mem_ball.mp (hω hmem)
        linarith [hfar x hx, hn x hx, dist_triangle (G x) (Gj n x) y]
      · -- There `ω(G_n x) = 0`, so its pull-back is `0`.
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx]
        ext v
        simp
    simp only [map_zero] at hT
    exact (tendsto_nhds_unique tendsto_const_nhds hT).symm
  -- 3. `B(y, ε/3)` is open with compact closure, so `y ∈ S.zeroRegion`, i.e. `y ∉ spt S`.
  exact hy.2 (mem_sUnion.mpr ⟨ball y (ε / 3), ⟨isOpen_ball,
    (isCompact_closedBall y (ε / 3)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _, hvan⟩, mem_ball_self hρ⟩)
/-- **Lipschitz push-forward, existence** (Simon Ch. 6, 2.29, p. 141; supplied Steps 1–12).  Assume
the reference-sequence statement (RS) and the comparison statement (CL).  Let `M(X) < ∞`, let
`G` be `Λ`-Lipschitz on `(spt X)_r` and proper on `spt X`.  (RS) with `F := spt X` gives `C^∞`
maps `G_n` with `‖DG_n‖ ≤ Λ` on `O₀ := (spt X)_{r/2}`, `G_n → G` uniformly there and `G_n` proper
on `spt X` for `n ≥ n₀`.  `Submission.dph_lpfex_bounded_compatible_form` gives forms `η_n(ω)`,
compatible with `(G_n, ω)` near `spt X` for `n ≥ n₀` (`η_n(ω) := 0` for `n < n₀`), with
`|η_n(ω)| ≤ Λ^k C` whenever `|ω| ≤ C`; the mass bound gives `|X(η_n(ω))| ≤ M(X) Λ^k C`.
(CL) along pairs of reindexings and `Submission.dph_lpfex_tendsto_of_index_maps` give a limit
`S₀(ω) = lim X(η_n(ω))`, and (CL) against `η_n(ω)` shows that every admissible approximation
computes `S₀(ω)`; this makes `S₀` linear.  `Submission.dph_lpf_current_of_bounded_functional`
turns `S₀` into a current `S` with `M(S) ≤ Λ^k M(X)`; uniqueness is uniqueness of limits, and
`Submission.dph_lpfex_support_subset_closure_image` gives `spt S ⊆ closure (G(spt X))`. -/
theorem Submission.dph_lpf_existence : (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧ (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧ S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support)) := by
  intro hRS hCL m m' k X G Λ r hXm hXb hr hLip hprop
  -- 1. Reference sequence: (RS) with the closed set `F := spt X`, on `O₀ := (spt X)_{r/2}`.
  have hXc : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  obtain ⟨Gs, hGs, hGsd, hGsu, hGsp⟩ := hRS m m' G Λ r X.support hr hXc hLip hprop
  set O₀ := thickening (r / 2) X.support
  have hO₀ : IsOpen O₀ := isOpen_thickening
  have hXO₀ : X.support ⊆ O₀ := self_subset_thickening (half_pos hr) _
  have hGsd' : ∀ᶠ n in atTop, ∀ x ∈ O₀, ‖fderiv ℝ (Gs n) x‖ ≤ (Λ : ℝ) :=
    Eventually.of_forall hGsd
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hGsp
  -- 3. Forms `η n ω`, compatible with `(G_n, ω)` near `spt X` for `n ≥ n₀`, with
  -- `|η n ω| ≤ Λ^k C` whenever `|ω| ≤ C`; `η n ω := 0` for `n < n₀`.
  have hη : ∀ (n : ℕ) (ω : TestFormOn (univ : Set (Eucl m')) k),
      ∃ η : TestFormOn (univ : Set (Eucl m)) k,
        (n₀ ≤ n → ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (η : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gs n x)).compContinuousLinearMap
              (fderiv ℝ (Gs n) x)) ∧
        ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
          ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C := by
    intro n ω
    by_cases hn : n₀ ≤ n
    · obtain ⟨η, hc, hb⟩ := Submission.dph_lpfex_bounded_compatible_form m m' k (Gs n) X.support
        O₀ Λ hO₀ hXO₀ (hGs n) (hGsd n) (hn₀ n hn) ω
      exact ⟨η, fun _ => hc, hb⟩
    · refine ⟨0, fun h => absurd h hn, fun C hC x => ?_⟩
      have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
      rw [Submodule.coe_zero, Pi.zero_apply, covectorEuclideanNorm_zero]
      positivity
  choose η hηc hηb using hη
  have hηc0 : ∀ ω, ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
      (η n ω : DifferentialForm (Eucl m) k) x =
        ((ω : DifferentialForm (Eucl m') k) (Gs n x)).compContinuousLinearMap
          (fderiv ℝ (Gs n) x) :=
    fun ω => (eventually_ge_atTop n₀).mono fun n hn => hηc n ω hn
  -- 5. Reindexing along `p → ∞` keeps the reference sequence and the compatibility.
  have hGsu' : ∀ p : ℕ → ℕ, Tendsto p atTop atTop →
      TendstoUniformlyOn (fun i => Gs (p i)) G atTop O₀ :=
    fun p hp u hu => hp.eventually (hGsu u hu)
  have hηc' : ∀ p : ℕ → ℕ, Tendsto p atTop atTop → ∀ ω, ∀ᶠ i in atTop, ∃ N : Set (Eucl m),
      IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η (p i) ω : DifferentialForm (Eucl m) k) x =
        ((ω : DifferentialForm (Eucl m') k) (Gs (p i) x)).compContinuousLinearMap
          (fderiv ℝ (Gs (p i)) x) :=
    fun p hp ω => (hp.eventually_ge_atTop n₀).mono fun i hi => hηc (p i) ω hi
  -- 6. (CL) along any two reindexings: `X (η n ω)` converges, to `S₀ ω` say.
  have hlim : ∀ ω, ∃ s, Tendsto (fun n => X (η n ω)) atTop (𝓝 s) := by
    intro ω
    refine Submission.dph_lpfex_tendsto_of_index_maps _ fun p q hp hq => ?_
    exact hCL m m' k X G hXm hXb hprop (fun i => Gs (p i)) (fun i => Gs (q i)) O₀ O₀ Λ Λ
      hO₀ hXO₀ (fun i => hGs (p i)) (Eventually.of_forall fun i => hGsd (p i)) (hGsu' p hp)
      hO₀ hXO₀ (fun i => hGs (q i)) (Eventually.of_forall fun i => hGsd (q i)) (hGsu' q hq)
      ω (fun i => η (p i) ω) (fun i => η (q i) ω) (hηc' p hp ω) (hηc' q hq ω)
  choose S₀ hS₀ using hlim
  -- 9. (CL) against `η n ω`: every admissible approximation computes `S₀ ω`.
  have hconv : ∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O →
      X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
      (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
      ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (ηj n : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x)) →
        Tendsto (fun n => X (ηj n)) atTop (𝓝 (S₀ ω)) := by
    intro Gj O L hO hXO hGj hGjd hGju ω ηj hηj
    have h := hCL m m' k X G hXm hXb hprop Gs Gj O₀ O Λ L hO₀ hXO₀ hGs hGsd' hGsu hO hXO hGj
      hGjd hGju ω (fun n => η n ω) ηj (hηc0 ω) hηj
    simpa using h.add (hS₀ ω)
  -- 7. Linearity of `S₀`: the sums and multiples of the `η n ω` are again compatible.
  have hadd : ∀ ω ω' : TestFormOn (univ : Set (Eucl m')) k, S₀ (ω + ω') = S₀ ω + S₀ ω' := by
    intro ω ω'
    have hc : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        ((η n ω + η n ω' : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x =
          (((ω + ω' : TestFormOn (univ : Set (Eucl m')) k) : DifferentialForm (Eucl m') k)
            (Gs n x)).compContinuousLinearMap (fderiv ℝ (Gs n) x) := by
      filter_upwards [hηc0 ω, hηc0 ω'] with n ⟨N, hN, hXN, hNe⟩ ⟨N', hN', hXN', hNe'⟩
      refine ⟨N ∩ N', hN.inter hN', subset_inter hXN hXN', fun x hx => ?_⟩
      rw [Submodule.coe_add, Pi.add_apply, hNe x hx.1, hNe' x hx.2, Submodule.coe_add,
        Pi.add_apply]
      ext v
      simp
    exact tendsto_nhds_unique (hconv Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu _ _ hc)
      (((hS₀ ω).add (hS₀ ω')).congr fun n => (map_add X.toCurrent (η n ω) (η n ω')).symm)
  have hsmul : ∀ (c : ℝ) (ω : TestFormOn (univ : Set (Eucl m')) k), S₀ (c • ω) = c * S₀ ω := by
    intro c ω
    have hc : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        ((c • η n ω : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x =
          (((c • ω : TestFormOn (univ : Set (Eucl m')) k) : DifferentialForm (Eucl m') k)
            (Gs n x)).compContinuousLinearMap (fderiv ℝ (Gs n) x) := by
      filter_upwards [hηc0 ω] with n ⟨N, hN, hXN, hNe⟩
      refine ⟨N, hN, hXN, fun x hx => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hNe x hx, Submodule.coe_smul, Pi.smul_apply]
      ext v
      simp
    exact tendsto_nhds_unique (hconv Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu _ _ hc)
      (((hS₀ ω).const_mul c).congr fun n => (by rw [map_smul, smul_eq_mul]))
  -- 4 and 8. `|X (η n ω)| ≤ M(X) Λ^k C`, hence `|S₀ ω| ≤ Λ^k M(X) C`, whenever `|ω| ≤ C`.
  have hXη : ∀ (n : ℕ) (ω : TestFormOn (univ : Set (Eucl m')) k) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
        |X (η n ω)| ≤ X.mass.toReal * ((Λ : ℝ) ^ k * C) :=
    fun n ω C hC => Submission.cmb_abs_apply_le_of_massOn_le m k univ univ X (η n ω) _ _
      ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hXm.ne).ge (subset_univ _) (hηb n ω C hC)
  have hS₀b : ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
        |S₀ ω| ≤ ((Λ : ℝ) ^ k * X.mass.toReal) * C := by
    intro ω C hC
    calc |S₀ ω| ≤ X.mass.toReal * ((Λ : ℝ) ^ k * C) :=
          le_of_tendsto' (hS₀ ω).abs fun n => hXη n ω C hC
      _ = ((Λ : ℝ) ^ k * X.mass.toReal) * C := by ring
  -- 8. `S₀` is a current `S` with `M(S) ≤ Λ^k M(X)`.
  obtain ⟨S, hSS₀, hSm⟩ := Submission.dph_lpf_current_of_bounded_functional m' k univ S₀
    ((Λ : ℝ) ^ k * X.mass.toReal) hadd hsmul hS₀b
  have hS : ∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O →
      X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
      (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
      ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (ηj n : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x)) →
        Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω)) := by
    intro Gj O L hO hXO hGj hGjd hGju ω ηj hηj
    rw [hSS₀ ω]
    exact hconv Gj O L hO hXO hGj hGjd hGju ω ηj hηj
  refine ⟨S, hS, fun S' hS' => ?_, ?_, ?_⟩
  · -- 10. Uniqueness: test `S'` against the reference sequence and `η n ω`.
    ext ω
    exact tendsto_nhds_unique (hS' Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu ω _ (hηc0 ω))
      (hS Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu ω _ (hηc0 ω))
  · -- 8. `ofReal (Λ^k M(X)) = Λ^k M(X)`, as `M(X) < ∞`.
    refine hSm.trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (NNReal.coe_nonneg Λ),
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXm.ne]
  · -- 11. Support, from the characterization of `S` along the reference sequence.
    exact Submission.dph_lpfex_support_subset_closure_image m m' k X S G Gs
      (fun n => (hGs n).continuous) (hGsu.mono hXO₀) (hS Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu)

/-- Part (II) of the Lipschitz push-forward: if `S` is the Lipschitz push-forward of `X`, with
`M(X), M(∂X) < ∞`, then `∂S` is that of `∂X`.  Part (I) applied to `∂X` gives a push-forward `S_∂`
of `∂X`.  For a reference sequence `Gₙ` of (RS) on `(spt X)_{r/2}` and forms `θₙ` compatible with
`(Gₙ, φ)` near `spt X`, `dθₙ` is compatible with `(Gₙ, dφ)` since `d` commutes with pull-back, so
`S_∂(φ) = lim ∂X(θₙ) = lim X(dθₙ) = S(dφ) = ∂S(φ)`. -/
theorem Submission.dph_lpf_boundary :
    (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r →
      IsClosed F → LipschitzOnWith Λ G (thickening r F) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) →
      ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧
        (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧
        TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧
        ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) →
    (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m')
      (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ →
      (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X →
        Y.boundary.mass < ∞) →
      0 < r → LipschitzOnWith Λ G (thickening r X.support) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) →
      ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k,
        (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
          (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
          (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
          ∀ (ω : TestFormOn (univ : Set (Eucl m')) k)
            (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
            (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
              (ηj n : DifferentialForm (Eucl m) k) x =
                ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                  (fderiv ℝ (Gj n) x)) →
            Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧
        (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k,
          (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
            (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
            (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
            ∀ (ω : TestFormOn (univ : Set (Eucl m')) k)
              (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
              (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
                (ηj n : DifferentialForm (Eucl m) k) x =
                  ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                    (fderiv ℝ (Gj n) x)) →
              Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧
        S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support)) →
    (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1))
      (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ)
      (S : GeometricCurrentOn (univ : Set (Eucl m')) (j + 1)),
      X.mass < ∞ → X.boundary.mass < ∞ → 0 < r → LipschitzOnWith Λ G (thickening r X.support) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1))
          (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) (j + 1)),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) (j + 1)) x =
              ((ω : DifferentialForm (Eucl m') (j + 1)) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O →
        X.boundary.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) j)
          (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) j),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.boundary.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) j) x =
              ((ω : DifferentialForm (Eucl m') j) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X.boundary (ηj n)) atTop (𝓝 (S.boundary ω)))) := by
  intro hRS hI m m' j X G Λ r S _ hXbm hr hLip hprop hS Gj O L hO hXO hGj hL hGjG ω ηj hη
  -- 1. `spt ∂X ⊆ spt X`; supports of currents on `univ` are closed.
  have hsub : X.boundary.support ⊆ X.support := Submission.iwl_cr_support_lemmas.1 m j univ X
  have hcl : ∀ {k : ℕ} (Z : GeometricCurrentOn (univ : Set (Eucl m)) k), IsClosed Z.support :=
    fun Z => isClosed_univ.sdiff Z.isOpen_zeroRegion
  -- 2. Part (I) applied to `∂X` (`∂∂X = 0` has mass `0`) gives a push-forward `Sb` of `∂X`.
  obtain ⟨Sb, hSb, -⟩ := hI m m' j X.boundary G Λ r hXbm (by
      intro j' Y hj hY
      subst hj
      obtain rfl := eq_of_heq hY
      rw [GeometricCurrentOn.boundary_boundary]
      refine lt_of_le_of_lt (sSup_le ?_) ENNReal.zero_lt_top
      rintro _ ⟨φ, -, rfl⟩
      simp) hr (hLip.mono (thickening_subset_of_subset r hsub)) fun K hK => by
    have h := (hprop K hK).inter_right (hcl X.boundary)
    rwa [inter_assoc, inter_eq_right.2 hsub] at h
  -- It remains to identify `Sb ω` with `∂S ω = S (dω)`.
  suffices key : Sb ω = S.boundary ω by
    rw [← key]
    exact hSb Gj O L hO hXO hGj hL hGjG ω ηj hη
  -- 3. A reference sequence `Gn` for `F = spt X` on `O₀ = (spt X)_{r/2}`, and forms `θ n`
  -- compatible with `(Gn n, ω)` near `spt X` whenever `Gn n` is proper on `spt X`.
  obtain ⟨Gn, hGns, hGnd, hGnu, hGnp⟩ := hRS m m' G Λ r X.support hr (hcl X) hLip hprop
  have hXO₀ : X.support ⊆ thickening (r / 2) X.support := self_subset_thickening (half_pos hr) _
  have hθ : ∀ n, ∃ θ : TestFormOn (univ : Set (Eucl m)) j,
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gn n ⁻¹' K ∩ X.support)) →
      ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        (θ : DifferentialForm (Eucl m) j) x =
          ((ω : DifferentialForm (Eucl m') j) (Gn n x)).compContinuousLinearMap
            (fderiv ℝ (Gn n) x) := by
    intro n
    by_cases hp : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gn n ⁻¹' K ∩ X.support)
    · obtain ⟨θ, -, N, hN, hXN, -, -, hθN, -⟩ := Submission.iwl_sp_exists_compatible_testForm
        m m' j univ univ X.support (Gn n) isOpen_univ (subset_univ _) (hGns n)
        (fun K hK _ => hp K hK) ω
      exact ⟨θ, fun _ => ⟨N, hN, hXN, hθN⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose θ hθ using hθ
  -- 4. `∂X (θ n) → Sb ω`.
  have h1 : Tendsto (fun n => X.boundary (θ n)) atTop (𝓝 (Sb ω)) :=
    hSb Gn (thickening (r / 2) X.support) Λ isOpen_thickening (hsub.trans hXO₀) hGns
      (Eventually.of_forall hGnd) hGnu ω θ (hGnp.mono fun n hn => by
        obtain ⟨N, hN, hXN, hθN⟩ := hθ n hn
        exact ⟨N, hN, hsub.trans hXN, hθN⟩)
  -- 5–6. `dθ n` is compatible with `(Gn n, dω)` near `spt X` (`d` commutes with pull-back), so
  -- `X (dθ n) → S (dω)`.
  have h2 : Tendsto (fun n => X (exteriorDerivativeTestOn univ j (θ n))) atTop
      (𝓝 (S (exteriorDerivativeTestOn univ j ω))) :=
    hS Gn (thickening (r / 2) X.support) Λ isOpen_thickening hXO₀ hGns
      (Eventually.of_forall hGnd) hGnu (exteriorDerivativeTestOn univ j ω)
      (fun n => exteriorDerivativeTestOn univ j (θ n)) (hGnp.mono fun n hn => by
        obtain ⟨N, hN, hXN, hθN⟩ := hθ n hn
        refine ⟨N, hN, hXN, fun x hx => ?_⟩
        have hev : (θ n : DifferentialForm (Eucl m) j) =ᶠ[𝓝 x] fun y =>
            ((ω : DifferentialForm (Eucl m') j) (Gn n y)).compContinuousLinearMap
              (fderiv ℝ (Gn n) y) :=
          eventually_of_mem (hN.mem_nhds hx) hθN
        change extDeriv (θ n : DifferentialForm (Eucl m) j) x =
          (extDeriv (ω : DifferentialForm (Eucl m') j) (Gn n x)).compContinuousLinearMap
            (fderiv ℝ (Gn n) x)
        rw [hev.extDeriv_eq]
        exact extDeriv_pullback ((ω.property.1.1.differentiable (by simp)).differentiableAt)
          (hGns n).contDiffAt (by simp))
  -- 7. `∂X (θ n) = X (dθ n)`, so the two limits agree.
  exact tendsto_nhds_unique h1 h2

/-- Linearity of the Lipschitz push-forward in the current (Part (III)).  With
`F = spt X ∪ spt X₁ ⊇ spt X₂`, one reference sequence `G_n` for `F` (with `O = F_{r/2}`, `L = Λ`)
and one sequence `η_n`, compatible with `(G_n, ω)` near `F` once `G_n` is proper on `F`, are
admissible for all three push-forwards; so `X₂(η_n) = a X(η_n) + a₁ X₁(η_n)` tends both to
`S₂(ω)` and to `a S(ω) + a₁ S₁(ω)`. -/
theorem Submission.dph_lpf_linearity :
    (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r →
      IsClosed F → LipschitzOnWith Λ G (thickening r F) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) →
      ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧
        (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧
        TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧
        ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) →
    (∀ (m m' k : ℕ) (X X₁ X₂ : GeometricCurrentOn (univ : Set (Eucl m)) k)
      (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ)
      (S S₁ S₂ : GeometricCurrentOn (univ : Set (Eucl m')) k) (a a₁ : ℝ),
      0 < r → LipschitzOnWith Λ G (thickening r (X.support ∪ X₁.support)) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ (X.support ∪ X₁.support))) →
      (∀ ω, X₂ ω = a * X ω + a₁ * X₁ ω) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) k) x =
              ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₁.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₁.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) k) x =
              ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X₁ (ηj n)) atTop (𝓝 (S₁ ω))) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₂.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₂.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) k) x =
              ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X₂ (ηj n)) atTop (𝓝 (S₂ ω))) →
      ∀ ω, S₂ ω = a * S ω + a₁ * S₁ ω) := by
  intro hRS m m' k X X₁ X₂ G Λ r S S₁ S₂ a a₁ hr hLip hprop hX₂ hS hS₁ hS₂ ω
  -- 1. `F = spt X ∪ spt X₁` is closed (supports in `univ` are closed) and contains `spt X₂`.
  have hFc : IsClosed (X.support ∪ X₁.support) :=
    (isClosed_univ.sdiff X.isOpen_zeroRegion).union (isClosed_univ.sdiff X₁.isOpen_zeroRegion)
  have hX₂F : X₂.support ⊆ X.support ∪ X₁.support :=
    Submission.iwl_cr_support_lemmas.2.2 m k univ isOpen_univ X X₁ X₂ a a₁ hX₂
  -- 2. One reference sequence `G_n`, admissible on the open `O = F_{r/2} ⊇ F` with `L = Λ`.
  obtain ⟨Gj, hGs, hGd, hGu, hGp⟩ := hRS m m' G Λ r _ hr hFc hLip hprop
  have hO : IsOpen (thickening (r / 2) (X.support ∪ X₁.support)) := isOpen_thickening
  have hFO : X.support ∪ X₁.support ⊆ thickening (r / 2) (X.support ∪ X₁.support) :=
    self_subset_thickening (half_pos hr) _
  have hdb : ∀ᶠ n in atTop, ∀ x ∈ thickening (r / 2) (X.support ∪ X₁.support),
      ‖fderiv ℝ (Gj n) x‖ ≤ (Λ : ℝ) :=
    Eventually.of_forall hGd
  -- 3. Test forms `η_n` compatible with `(G_n, ω)` near `F` whenever `G_n` is proper on `F`
  -- (the cut-off pull-back), and `η_n = 0` otherwise.
  have hη : ∀ n, ∃ η : TestFormOn (univ : Set (Eucl m)) k,
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ (X.support ∪ X₁.support))) →
      ∃ N : Set (Eucl m), IsOpen N ∧ X.support ∪ X₁.support ⊆ N ∧ ∀ x ∈ N,
        (η : DifferentialForm (Eucl m) k) x =
          ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
            (fderiv ℝ (Gj n) x) := by
    intro n
    by_cases hpn : ∀ K : Set (Eucl m'), IsCompact K →
        IsCompact (Gj n ⁻¹' K ∩ (X.support ∪ X₁.support))
    · obtain ⟨η, _, N, hN, hFN, _, _, hηN, _⟩ :=
        Submission.iwl_sp_exists_compatible_testForm m m' k univ univ _ (Gj n) isOpen_univ
          (subset_univ _) (hGs n) (fun K hK _ => hpn K hK) ω
      exact ⟨η, fun _ => ⟨N, hN, hFN, hηN⟩⟩
    · exact ⟨0, fun h => absurd h hpn⟩
  choose ηj hηj using hη
  have hcomp : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ∪ X₁.support ⊆ N ∧
      ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x =
        ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
          (fderiv ℝ (Gj n) x) :=
    hGp.mono fun n hn => hηj n hn
  -- 4. The three push-forward limits; `X₂(η_n) = a X(η_n) + a₁ X₁(η_n)` and uniqueness of limits.
  have h₀ := hS Gj _ Λ hO (subset_union_left.trans hFO) hGs hdb hGu ω ηj
    (hcomp.mono fun n ⟨N, hN, hFN, hηN⟩ => ⟨N, hN, subset_union_left.trans hFN, hηN⟩)
  have h₁ := hS₁ Gj _ Λ hO (subset_union_right.trans hFO) hGs hdb hGu ω ηj
    (hcomp.mono fun n ⟨N, hN, hFN, hηN⟩ => ⟨N, hN, subset_union_right.trans hFN, hηN⟩)
  have h₂ := hS₂ Gj _ Λ hO (hX₂F.trans hFO) hGs hdb hGu ω ηj
    (hcomp.mono fun n ⟨N, hN, hFN, hηN⟩ => ⟨N, hN, hX₂F.trans hFN, hηN⟩)
  exact tendsto_nhds_unique h₂
    (((h₀.const_mul a).add (h₁.const_mul a₁)).congr fun n => (hX₂ (ηj n)).symm)
/-- The mollifier behind Simon's `f^{(σ)}` (Ch. 6, §4, p. 158; parent Step 4): a smooth,
nonnegative, compactly supported `ρ` vanishing off `B(0, σ)` with `∫ ρ = 1`.  Take the bump `φ`
centred at `0` with radii `σ/2 < σ`; then `support φ = B(0, σ)`, so `c = ∫ φ > 0` and
`ρ = c⁻¹ φ` works. -/
theorem Submission.slicing_mb_sa_mollifier_exists :
    ∀ (P : ℕ) (σ : ℝ), 0 < σ → ∃ ρ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧ (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) ∧
      ∫ y, ρ y = 1 := by
  intro P σ hσ
  -- The smooth bump `φ` centred at `0` with `support φ = B(0, σ)`.
  let φ : ContDiffBump (0 : Eucl P) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
  have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  -- Its mass `c = ∫ φ` is positive since `B(0, σ)` has positive Lebesgue measure.
  have hc : 0 < ∫ y, φ y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
    exact measure_ball_pos _ _ hσ
  refine ⟨fun y => (∫ y, φ y)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, fun y => mul_nonneg (inv_nonneg.2 hc.le) φ.nonneg,
    fun y hy => mul_eq_zero_of_right _ (φ.zero_of_le_dist (by rwa [dist_zero_right])), ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hc.ne']

/-- Mollifying a Lipschitz map, as for Simon's `f^{(σ)} = f ∗ φ^{(σ)}` (Ch. 6, 2.29, p. 141): for
an `L`-Lipschitz `F : ℝ^m → ℝ^{m'}`, `F_σ(x) = ∫ ρ(w) F(x - w) dw`, with `ρ` the mollifier of
`slicing_mb_sa_mollifier_exists` at radius `σ/2`, is smooth, `L`-Lipschitz and `Lσ`-close to `F`.
If `F` is `Λ'`-Lipschitz on `B(x, 2σ)`, then `F_σ` is `Λ'`-Lipschitz on `B(x, σ)`,
`‖DF_σ(x)‖ ≤ Λ'` and `|F_σ(x) - F(x)| ≤ Λ'σ`; a coordinate of `F` constant on `B(x, σ)` keeps
its value at `x`. -/
theorem Submission.dph_sa_mollify_lipschitz :
    ∀ (m m' : ℕ) (F : Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L F → ∀ σ : ℝ, 0 < σ →
      ∃ Fs : Eucl m → Eucl m', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs ∧ LipschitzWith L Fs ∧
        (∀ x, ‖Fs x - F x‖ ≤ (L : ℝ) * σ) ∧
        (∀ (x : Eucl m) (Λ' : ℝ≥0), LipschitzOnWith Λ' F (ball x (2 * σ)) →
          LipschitzOnWith Λ' Fs (ball x σ) ∧ ‖fderiv ℝ Fs x‖ ≤ (Λ' : ℝ) ∧
            ‖Fs x - F x‖ ≤ (Λ' : ℝ) * σ) ∧
        ∀ (x : Eucl m) (i : Fin m') (c : ℝ), (∀ y ∈ ball x σ, F y i = c) → Fs x i = c := by
  intro m m' F L hF σ hσ
  -- The mollifier `ρ ≥ 0`, `∫ ρ = 1`, vanishing off `B(0, σ/2)`.
  obtain ⟨ρ, hρs, hρc, hρ0, hρz, hρ1⟩ :=
    Submission.slicing_mb_sa_mollifier_exists m (σ / 2) (half_pos hσ)
  have hρi : Integrable ρ := hρs.continuous.integrable_of_hasCompactSupport hρc
  -- `F_σ(x) = ∫ ρ(w) • F(x - w) dw`; each integrand is continuous with compact support.
  let Fs : Eucl m → Eucl m' := fun x => ∫ w, ρ w • F (x - w)
  have hint : ∀ x, Integrable (fun w => ρ w • F (x - w)) := fun x =>
    (hρs.continuous.smul (hF.continuous.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport hρc.smul_right
  -- `|∫ ρ • G| ≤ B` once `|G| ≤ B` on `B(0, σ/2)`, outside of which `ρ = 0`.
  have hbound : ∀ (G : Eucl m → Eucl m') (B : ℝ), (∀ w : Eucl m, ‖w‖ < σ / 2 → ‖G w‖ ≤ B) →
      ‖∫ w, ρ w • G w‖ ≤ B := by
    intro G B hG
    calc ‖∫ w, ρ w • G w‖ ≤ ∫ w, ρ w * B := by
          refine norm_integral_le_of_norm_le (hρi.mul_const B) (Eventually.of_forall fun w => ?_)
          by_cases hw : ‖w‖ < σ / 2
          · rw [norm_smul, Real.norm_of_nonneg (hρ0 w)]
            exact mul_le_mul_of_nonneg_left (hG w hw) (hρ0 w)
          · rw [hρz w (not_lt.1 hw), zero_smul, norm_zero, zero_mul]
      _ = B := by rw [integral_mul_const, hρ1, one_mul]
  -- Smoothness: `F_σ = ρ ⋆ F`.
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs := by
    have : Fs = convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext x
      rw [convolution_lsmul]
    rw [this]
    exact hρc.contDiff_convolution_left _ hρs hF.continuous.locallyIntegrable
  -- (E) `|F_σ(y) - F_σ(y')| ≤ Λ'|y - y'|` if `F` is `Λ'`-Lipschitz on a `U` containing
  -- `y - w` and `y' - w` for all `|w| < σ/2`.
  have hE : ∀ (U : Set (Eucl m)) (Λ' : ℝ≥0), LipschitzOnWith Λ' F U → ∀ y y' : Eucl m,
      (∀ w : Eucl m, ‖w‖ < σ / 2 → y - w ∈ U ∧ y' - w ∈ U) →
        ‖Fs y - Fs y'‖ ≤ Λ' * ‖y - y'‖ := by
    intro U Λ' hU y y' hyy'
    have : Fs y - Fs y' = ∫ w, ρ w • (F (y - w) - F (y' - w)) := by
      simp only [Fs, smul_sub]
      rw [integral_sub (hint y) (hint y')]
    rw [this]
    refine hbound _ _ fun w hw => ?_
    obtain ⟨h1, h2⟩ := hyy' w hw
    calc ‖F (y - w) - F (y' - w)‖ ≤ Λ' * ‖(y - w) - (y' - w)‖ := hU.norm_sub_le h1 h2
      _ = Λ' * ‖y - y'‖ := by rw [sub_sub_sub_cancel_right]
  -- (C) `|F_σ(x) - F(x)| ≤ Λ'σ` if `F` is `Λ'`-Lipschitz on a `U` containing `x` and `x - w`
  -- for all `|w| < σ/2`.
  have hC : ∀ (U : Set (Eucl m)) (Λ' : ℝ≥0), LipschitzOnWith Λ' F U → ∀ x : Eucl m, x ∈ U →
      (∀ w : Eucl m, ‖w‖ < σ / 2 → x - w ∈ U) → ‖Fs x - F x‖ ≤ Λ' * σ := by
    intro U Λ' hU x hx hxw
    have h1 : ∫ w, ρ w • F x = F x := by rw [integral_smul_const, hρ1, one_smul]
    have : Fs x - F x = ∫ w, ρ w • (F (x - w) - F x) := by
      simp only [Fs, smul_sub]
      rw [integral_sub (hint x) (hρi.smul_const (F x)), h1]
    rw [this]
    refine hbound _ _ fun w hw => ?_
    calc ‖F (x - w) - F x‖ ≤ Λ' * ‖(x - w) - x‖ := hU.norm_sub_le (hxw w hw) hx
      _ = Λ' * ‖w‖ := by rw [sub_sub_cancel_left, norm_neg]
      _ ≤ Λ' * σ := by gcongr; linarith
  refine ⟨Fs, hsmooth, ?_, ?_, ?_, ?_⟩
  -- Global bounds: `U = ℝ^m`, `Λ' = L`.
  · refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hE univ L hF.lipschitzOnWith y y' fun w _ => ⟨mem_univ _, mem_univ _⟩
  · exact fun x => hC univ L hF.lipschitzOnWith x (mem_univ _) fun w _ => mem_univ _
  -- Local bounds: `U = B(x, 2σ)` contains `y - w` for `y ∈ B(x, σ)`, `|w| < σ/2`.
  · intro x Λ' hΛ
    have hmem : ∀ y ∈ ball x σ, ∀ w : Eucl m, ‖w‖ < σ / 2 → y - w ∈ ball x (2 * σ) := by
      intro y hy w hw
      rw [mem_ball, dist_eq_norm] at hy ⊢
      calc ‖y - w - x‖ = ‖(y - x) - w‖ := by rw [sub_right_comm]
        _ ≤ ‖y - x‖ + ‖w‖ := norm_sub_le _ _
        _ < 2 * σ := by linarith
    have hLoc : LipschitzOnWith Λ' Fs (ball x σ) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      exact hE _ Λ' hΛ y y' fun w hw => ⟨hmem y hy w hw, hmem y' hy' w hw⟩
    refine ⟨hLoc, norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hσ) hLoc, ?_⟩
    exact hC _ Λ' hΛ x (mem_ball_self (by linarith)) (hmem x (mem_ball_self hσ))
  -- Locality of coordinates: `F_σ(x)_i = ∫ ρ(w) F(x - w)_i dw = c ∫ ρ = c`.
  · intro x i c hc
    have h1 : Fs x i = ∫ w, ρ w * F (x - w) i := by
      have := (EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ).integral_comp_comm (hint x)
      simpa [Fs] using this.symm
    rw [h1]
    have h2 : ∀ w, ρ w * F (x - w) i = ρ w * c := by
      intro w
      by_cases hw : ‖w‖ < σ / 2
      · rw [hc (x - w) (by rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; linarith)]
      · rw [hρz w (not_lt.1 hw), zero_mul, zero_mul]
    simp_rw [h2]
    rw [integral_mul_const, hρ1, one_mul]
/-- Multilinear-algebra step of the smoothing argument in the proof of the Deformation Theorem
(Simon Ch. 6, §5): a `k`-covector `γ` on `ℝ^{m'}` with `γ(e_{α(0)}, …, e_{α(k-1)}) = 0` pulls back
to `0` under every linear `T` with image in `span {e_{α(q)}}`.  With `S c = ∑_q c_q e_{α(q)}` on
`ℝ^k`, `T v = S ((T v)_{α(q)})_q`, and the alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes because
its value on the standard basis is `γ(e_{α(0)}, …, e_{α(k-1)}) = 0`. -/
theorem Submission.dph_sa_covector_comp_eq_zero :
    ∀ (m m' k : ℕ) (α : SimonMultiIndex k m') (γ : Eucl m' [⋀^Fin k]→L[ℝ] ℝ) (T : Eucl m →L[ℝ] Eucl m'), γ (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0 → (∀ (v : Eucl m) (i : Fin m'), i ∉ range α → T v i = 0) → γ.compContinuousLinearMap T = 0 := by
  intro m m' k α γ T hγ hT
  -- `S c = ∑_q c_q e_{α(q)}` on `ℝ^k`.
  let S : (Fin k → ℝ) →ₗ[ℝ] Eucl m' :=
    Fintype.linearCombination ℝ fun q => EuclideanSpace.single (α q) (1 : ℝ)
  -- `T` factors through `S`: coordinates in `range α` agree as `α` is injective, the others vanish.
  have hfac : ∀ v, T v = S fun q => T v (α q) := by
    intro v
    refine PiLp.ext fun i => ?_
    simp only [S, Fintype.linearCombination_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ range α
    · obtain ⟨q₀, rfl⟩ := hi
      simp [α.injective.eq_iff]
    · rw [hT v i hi, Finset.sum_eq_zero fun q _ => ite_eq_right fun h => hi ⟨q, h.symm⟩]
  -- The alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes on the standard basis, hence is `0`.
  have h0 : γ.toAlternatingMap.compLinearMap S = 0 := by
    have hb : (fun q => S (Pi.basisFun ℝ (Fin k) q)) =
        fun j => EuclideanSpace.single (α j) (1 : ℝ) := by
      funext q
      simp [S]
    rw [← AlternatingMap.map_basis_eq_zero_iff (Pi.basisFun ℝ (Fin k)),
      AlternatingMap.compLinearMap_apply, ContinuousAlternatingMap.coe_toAlternatingMap, hb]
    exact hγ
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rw [show ⇑T ∘ v = fun p => S fun q => T (v p) (α q) from funext fun p => hfac (v p)]
  exact AlternatingMap.congr_fun h0 fun p q => T (v p) (α q)

/-- The smoothings `f_σ = f ∗ φ_σ` of Simon Ch. 6, 2.29 (p. 141), for the Lipschitz push-forward
homotopy of the deformation theorem (§5): extend `G` from `A_δ = thickening δ A` to a Lipschitz
`G'` on `ℝ^m` (McShane) and mollify it at the scales `σ_j = (δ / 8) / (j + 1)`.  The
`2σ_j`-balls about points of `A_{δ/2}` stay in `A_δ`, where `G' = G` is `Λ`-Lipschitz, so
`‖D(Gj j)‖ ≤ Λ` there.  Near `A`, wherever `Gj j` meets `spt ω` the normal coordinates
`i ∉ range α` of `G` equal `z i` on a `2σ_j`-ball, so those of `Gj j` are locally constant,
`D(Gj j)` maps into `span e_α`, and `ω` without `e_α`-component pulls back to `0`. -/
theorem Submission.dph_lipschitz_smooth_approx :
    ∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ →
      LipschitzOnWith Λ G (thickening δ A) →
      ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0),
        LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧
        (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧
        TendstoUniformly Gj G' atTop ∧
        (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧
        ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m')
          (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε →
          (∀ x ∈ thickening ε A,
            G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) →
              ∀ i, i ∉ range α → G x i = z i) →
          (∀ y, (ω : DifferentialForm (Eucl m') k) y
            (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) →
          ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A,
            ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap
              (fderiv ℝ (Gj j) x) = 0 := by
  intro m m' G Λ A δ hδ hG
  -- Step 1 (McShane): a global Lipschitz extension `G'` of `G|A_δ`.
  obtain ⟨G', L, hG'L, hG'⟩ : ∃ (G' : Eucl m → Eucl m') (L : ℝ≥0),
      LipschitzWith L G' ∧ EqOn G' G (thickening δ A) :=
    let ⟨G', hG'L, hGG'⟩ := hG.extend_finite_dimension
    ⟨G', _, hG'L, hGG'.symm⟩
  -- The scales `σ_j = (δ / 8) / (j + 1)`: positive, at most `δ / 8`, tending to `0`.
  obtain ⟨σ, hσ, hσδ, hσ0⟩ : ∃ σ : ℕ → ℝ, (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ δ / 8) ∧
      Tendsto σ atTop (𝓝 0) := by
    refine ⟨fun j => δ / 8 * (1 / ((j : ℝ) + 1)), fun j => by positivity, fun j => ?_, ?_⟩
    · dsimp only
      rw [mul_one_div]
      exact div_le_self (by positivity) (by linarith [j.cast_nonneg (α := ℝ)])
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 8)
  -- Step 2: `Gj j` is the mollification of `G'` at scale `σ j`.
  choose Gj hGj hGjL hGjG' hGjloc hGjc using fun j =>
    Submission.dph_sa_mollify_lipschitz m m' G' L hG'L (σ j) (hσ j)
  -- For `x ∈ A_{δ/2}` the ball `B(x, 2σ_j)` lies in `A_δ`, where `G' = G` is `Λ`-Lipschitz.
  have hball : ∀ j, ∀ x ∈ thickening (δ / 2) A, ball x (2 * σ j) ⊆ thickening δ A :=
    fun j x hx => (ball_subset_thickening hx (2 * σ j)).trans
      ((thickening_thickening_subset (2 * σ j) (δ / 2) A).trans
        (thickening_mono (by linarith [hσδ j]) A))
  have hlocal : ∀ j, ∀ x ∈ thickening (δ / 2) A, LipschitzOnWith Λ G' (ball x (2 * σ j)) :=
    fun j x hx => LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => by
      rw [hG' (hball j x hx hy), hG' (hball j x hx hy')]
      exact hG.dist_le_mul y (hball j x hx hy) y' (hball j x hx hy')
  refine ⟨G', Gj, L, hG'L, hG', hGj, hGjL, ?_,
    fun j x hx => (hGjloc j x Λ (hlocal j x hx)).2.1, ?_⟩
  · -- Step 3: `‖Gj j - G'‖ ≤ L σ_j → 0`.
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    have hL := hσ0.const_mul (L : ℝ)
    rw [mul_zero] at hL
    filter_upwards [hL.eventually_lt_const hη] with j hj x
    rw [dist_comm, dist_eq_norm]
    exact (hGjG' j x).trans_lt hj
  -- Step 4 (tangential vanishing) on `A_{μ/4}`, `μ = min ε δ`, once `σ_j < μ / 8` and
  -- `(4Λ + 4) σ_j < ε`.
  intro k α z ω ε hε hH1 hH2
  obtain ⟨μ, hμ, hμε, hμδ⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ ε ∧ μ ≤ δ :=
    ⟨min ε δ, lt_min hε hδ, min_le_left _ _, min_le_right _ _⟩
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  refine ⟨μ / 4, by positivity, ?_⟩
  have hc : 0 < min (μ / 8) (ε / (4 * Λ + 4)) := lt_min (by positivity) (by positivity)
  filter_upwards [hσ0.eventually_lt_const hc] with j hj x hx
  have hj1 : σ j < μ / 8 := hj.trans_le (min_le_left _ _)
  have hj2 : σ j * (4 * Λ + 4) < ε :=
    (lt_div_iff₀ (by positivity)).1 (hj.trans_le (min_le_right _ _))
  have hx2 : x ∈ thickening (δ / 2) A := thickening_mono (by linarith) A hx
  have hxδ : x ∈ thickening δ A := thickening_mono (by linarith) A hx
  by_cases hsupp : Gj j x ∈ tsupport (ω : DifferentialForm (Eucl m') k)
  · refine Submission.dph_sa_covector_comp_eq_zero m m' k α _ _ (hH2 _) fun v i hi => ?_
    -- On `B(x, 2σ_j)` the normal coordinates of `G' = G` are those of `z`: such `y` lie in
    -- `A_ε ∩ A_δ`, and `|G y - Gj j x| ≤ 2Λσ_j + Λσ_j < ε` with `Gj j x ∈ spt ω`.
    have hnormal : ∀ y ∈ ball x (2 * σ j), G' y i = z i := by
      intro y hy
      have hyA : y ∈ thickening (2 * σ j + μ / 4) A :=
        thickening_thickening_subset (2 * σ j) (μ / 4) A (ball_subset_thickening hx _ hy)
      have hyδ : y ∈ thickening δ A := thickening_mono (by linarith) A hyA
      rw [hG' hyδ]
      refine hH1 y (thickening_mono (by linarith) A hyA) ?_ i hi
      refine mem_thickening_iff.2 ⟨Gj j x, hsupp, ?_⟩
      have h1 : dist (G y) (G x) ≤ Λ * dist y x := hG.dist_le_mul y hyδ x hxδ
      have h2 : ‖Gj j x - G' x‖ ≤ Λ * σ j := (hGjloc j x Λ (hlocal j x hx2)).2.2
      rw [hG' hxδ, ← dist_eq_norm] at h2
      have h3 : dist y x < 2 * σ j := hy
      calc dist (G y) (Gj j x) ≤ dist (G y) (G x) + dist (Gj j x) (G x) :=
            dist_triangle_right _ _ _
        _ ≤ Λ * (2 * σ j) + Λ * σ j :=
            add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3.le hΛ)) h2
        _ < ε := by nlinarith [mul_nonneg hΛ (hσ j).le, hσ j]
    -- Hence the `i`-th coordinate of `Gj j` is `z i` on `B(x, σ_j)` and `D(Gj j)(x)` has
    -- vanishing `i`-th coordinate.
    have hconst : (EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ) ∘ Gj j =ᶠ[𝓝 x] fun _ => z i :=
      Filter.mem_of_superset (ball_mem_nhds x (hσ j)) fun x' hx' =>
        hGjc j x' i (z i) fun y hy => hnormal y (by
          rw [mem_ball] at hx' hy ⊢
          linarith [dist_triangle y x' x])
    have hD := ((EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ).hasFDerivAt.comp x
      (((hGj j).differentiable (by simp)).differentiableAt.hasFDerivAt)).unique
      ((hasFDerivAt_const (z i) x).congr_of_eventuallyEq hconst)
    simpa using congrArg (fun T : Eucl m →L[ℝ] ℝ => T v) hD
  · -- Off `spt ω` the covector `ω (Gj j x)` is already `0`.
    rw [image_eq_zero_of_notMem_tsupport hsupp]
    ext v
    simp

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
