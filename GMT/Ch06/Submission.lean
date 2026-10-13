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
/-- **Covector evaluation bound** (for `M(T) < ∞` in the proof of Simon Ch. 6, 6.1, p. 169).
If `|τ_j| ≤ 1` for all `j`, then `|α(τ_1, …, τ_n)| ≤ P^n |α|`, `|α|` the Euclidean coefficient
norm of Remark 2.6.  Expanding each `τ_j` in the standard basis `e_1, …, e_P` gives
`α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)` over the `P^n` maps `f : Fin n → Fin P`.  Each coefficient has
absolute value at most `1`, and `|α(e_f)| ≤ |α|`: `α(e_f) = 0` unless `f` is injective, and then
`α(e_f) = ±α(e_{f ∘ σ})` for the permutation `σ` sorting `f`, where `f ∘ σ` is strictly
increasing. -/
theorem Submission.isoperimetric_abs_covector_apply_le : ∀ (P n : ℕ) (α : Covector (Eucl P) n) (τ : Fin n → Eucl P), (∀ j, ‖τ j‖ ≤ 1) → |α τ| ≤ (P : ℝ) ^ n * covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `|α(e_f)| ≤ |α|` for every `f : Fin n → Fin P`.
  have hcoef : ∀ f : Fin n → Fin P,
      |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| ≤ covectorEuclideanNorm α := by
    intro f
    by_cases hf : Function.Injective f
    · -- Sort `f`: `f ∘ σ` is monotone and injective, hence strictly increasing.
      set σ := Tuple.sort f
      have hmono : StrictMono (f ∘ σ) :=
        (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
      have hperm : α (fun j => EuclideanSpace.basisFun (Fin P) ℝ ((f ∘ σ) j)) =
          Equiv.Perm.sign σ • α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) :=
        α.toAlternatingMap.map_perm (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) σ
      have habs : |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| =
          |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ ((f ∘ σ) j))| := by
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      -- `α(e_{f ∘ σ})²` is one of the summands of `|α|²`.
      rw [habs]
      unfold covectorEuclideanNorm
      apply Real.abs_le_sqrt
      have := Finset.single_le_sum (f := fun I : Fin n → Fin P =>
          if StrictMono I then (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ (f ∘ σ))
      simpa only [hmono, ite_true] using this
    · -- Two equal arguments: `α(e_f) = 0`.
      have hv : ¬Function.Injective fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j) :=
        fun hv => hf (Function.Injective.of_comp (f := EuclideanSpace.basisFun (Fin P) ℝ) hv)
      rw [α.map_eq_zero_of_not_injective _ hv, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  -- Step 2: multilinear expansion `α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)`.
  have hexp : α τ = ∑ f : Fin n → Fin P,
      (∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) := by
    have h1 : α τ = α (fun j => ∑ a, τ j a • EuclideanSpace.basisFun (Fin P) ℝ a) := by
      congr 1
      funext j
      simpa only [EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (τ j)).symm
    rw [h1, α.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [α.map_smul_univ, smul_eq_mul]
  -- Step 3: `|∏_j τ_j(f j)| ≤ 1`, as `|τ_j(a)| ≤ |τ_j| ≤ 1`.
  have hprod : ∀ f : Fin n → Fin P, |∏ j, τ j (f j)| ≤ 1 := by
    intro f
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ =>
      (show |τ j (f j)| ≤ ‖τ j‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (τ j) (f j)).trans (hτ j)
  -- Step 4: sum the bound `|α|` over the `P ^ n` maps `f`.
  calc |α τ| = |∑ f : Fin n → Fin P,
        (∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| := by
          rw [hexp]
    _ ≤ ∑ f : Fin n → Fin P,
        |(∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : Fin n → Fin P, covectorEuclideanNorm α := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul]
        calc |∏ j, τ j (f j)| * |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))|
            ≤ 1 * covectorEuclideanNorm α :=
              mul_le_mul (hprod f) (hcoef f) (abs_nonneg _) zero_le_one
          _ = covectorEuclideanNorm α := one_mul _
    _ = (P : ℝ) ^ n * covectorEuclideanNorm α := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
/-- Smoothness of a parametric interval integral, with all derivatives under the integral sign:
for `G : ℝ × ℝ^P → V` of class `C^∞` (`V` complete), `g x = ∫_a^b G(t, x) dt` is `C^∞`, every
`x`-derivative `(t, x) ↦ ∂_x^j G(t, x)` is continuous, and `D^j g(x) = ∫_a^b ∂_x^j G(t, x) dt`.

Proof.  For smooth `H : ℝ × ℝ^P → W` the `x`-derivative `H'(t, x) = DH(t, x) ∘ inr` is smooth with
values in the complete space `ℝ^P →L W`.  Bounding `‖H'‖` on the compact set
`[[a, b]] × closedBall x₀ 1` and differentiating under the integral sign gives
`D(∫_a^b H(t, ·) dt) = ∫_a^b H'(t, ·) dt`.  Induction on `j`, over all complete codomains at once,
identifies `D^{j+1}` with `D^j ∘ D` through the currying isometry, which commutes with the
interval integral; `C^j` for every `j` is `C^∞`. -/
theorem Submission.iwl_cr_ro_intervalIntegral_contDiff :
    ∀ (P : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (G : ℝ × Eucl P → V) (a b : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl P => ∫ t in a..b, G (t, x)) ∧ (∀ j : ℕ, Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => G (p.1, z)) p.2)) ∧ ∀ (j : ℕ) (x : Eucl P), iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, G (t, y)) x = ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => G (t, z)) x := by
  intro P V _ _ _ G a b hG
  -- The partial derivative of a smooth `H` in `x` is `H'(t, x) = DH(t, x) ∘ inr` (chain rule).
  have hderiv : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (H : ℝ × Eucl P → W),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ (t : ℝ) (x : Eucl P),
      HasFDerivAt (fun z : Eucl P => H (t, z))
        ((fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x := by
    intro W _ _ H hH t x
    exact (hH.differentiable (by simp) (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- One differentiation under the integral sign: `‖H'‖ ≤ K` on `[[a, b]] × closedBall x₀ 1`.
  have hstep : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ x₀ : Eucl P,
      HasFDerivAt (fun x : Eucl P => ∫ t in a..b, H (t, x))
        (∫ t in a..b, (fderiv ℝ H (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x₀ := by
    intro W _ _ _ H hH x₀
    have hHc : Continuous H := hH.continuous
    have hH'c : Continuous fun p : ℝ × Eucl P =>
        (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) :=
      (hH.continuous_fderiv (by simp)).clm_comp continuous_const
    obtain ⟨K, hK⟩ := (isCompact_uIcc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      hH'c.continuousOn
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => H (t, x))
      (F' := fun x t => (fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)))
      (bound := fun _ => K) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x =>
        (hHc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      ((hHc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hH'c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx =>
        hK (t, x) ⟨uIoc_subset_uIcc ht, ball_subset_closedBall hx⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun t x _ => hderiv W H hH t x)
  -- Induction on `j` over all complete codomains: `C^j`, continuity of `∂_x^j H`, and
  -- `D^j (∫_a^b H(t, ·) dt) = ∫_a^b ∂_x^j H(t, ·) dt`.
  have claim : ∀ j : ℕ, ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H →
      ContDiff ℝ j (fun x : Eucl P => ∫ t in a..b, H (t, x)) ∧
      Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => H (p.1, z)) p.2) ∧
      ∀ x : Eucl P, iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, H (t, y)) x =
        ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => H (t, z)) x := by
    intro j
    induction j with
    | zero =>
      intro W _ _ _ H hH
      have hHc : Continuous H := hH.continuous
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_zero, contDiff_zero]
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun x t => H (t, x)) (hHc.comp continuous_swap) a b
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
        exact (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.continuous.comp hHc
      · intro x
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact (LinearIsometry.intervalIntegral_comp_comm
          (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.toLinearIsometry
          (fun t => H (t, x))).symm
    | succ j ih =>
      intro W _ _ _ H hH
      set H' : ℝ × Eucl P → (Eucl P →L[ℝ] W) :=
        fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) with hH'
      have hH'smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H' :=
        (hH.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_comp contDiff_const
      obtain ⟨ih1, ih2, ih3⟩ := ih (Eucl P →L[ℝ] W) H' hH'smooth
      have hg : fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) =
          fun x => ∫ t in a..b, H' (t, x) := by
        funext x
        exact (hstep W H hH x).fderiv
      have hgd : Differentiable ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) :=
        fun x => (hstep W H hH x).differentiableAt
      have hpart : ∀ t : ℝ, fderiv ℝ (fun z : Eucl P => H (t, z)) = fun z => H' (t, z) :=
        fun t => funext fun z => (hderiv W H hH t z).fderiv
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
        refine ⟨hgd, fun h => absurd h (by simp), ?_⟩
        rw [hg]
        exact ih1
      · have : (fun p : ℝ × Eucl P => iteratedFDeriv ℝ (j + 1) (fun z : Eucl P => H (p.1, z)) p.2) =
            fun p => (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm
              (iteratedFDeriv ℝ j (fun z : Eucl P => H' (p.1, z)) p.2) := by
          funext p
          rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
          congr 2
          exact hpart p.1
        rw [this]
        exact (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm.continuous.comp ih2
      · intro x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        have : (fun y => fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) y) =
            fun x => ∫ t in a..b, H' (t, x) := hg
        rw [this, ih3 x]
        have hint : IntervalIntegrable
            (fun t : ℝ => iteratedFDeriv ℝ j (fun z : Eucl P => H' (t, z)) x) volume a b :=
          (ih2.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
        have e := ContinuousLinearMap.intervalIntegral_comp_comm
          ((continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm :
            (Eucl P [×j]→L[ℝ] (Eucl P →L[ℝ] W)) →L[ℝ] (Eucl P [×(j + 1)]→L[ℝ] W)) hint
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe] at e
        rw [← e]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        congr 2
        exact (hpart t).symm
  exact ⟨contDiff_infty.2 fun n => (claim n V G hG).1,
    fun j => (claim j V G hG).2.1,
    fun j x => (claim j V G hG).2.2 x⟩
/-- Integrand of the radial homotopy operator.  For a `C^∞` `(k + 1)`-form `ω` and `a ∈ ℕ`, the map
`F(t, x) = tᵃ • (ω(t • x)).curryLeft x`, i.e. `F(t, x)(v) = tᵃ ω(tx)(x, v)`, is `C^∞` on
`ℝ × ℝ^P`, and for fixed `t` the derivative of `F(t, ·)` at `x` is
`w ↦ (v ↦ tᵃ (t Dω(tx)[w](x, v) + ω(tx)(w, v)))`, where `(y, v) = Fin.cons y v`. -/
theorem Submission.iwl_cr_ro_integrand_contDiff_fderiv :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) ∧
          ∀ (t : ℝ) (x w : Eucl P) (v : Fin k → Eucl P),
            fderiv ℝ (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x w v =
              t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v)) := by
  intro P k a ω hω
  -- The interior product `α ↦ α.curryLeft` as an (opaque) continuous linear map `B`.
  obtain ⟨B, hB⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      ∀ α, B α = α.curryLeft :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
        (n := k)).toContinuousLinearMap, fun α => rfl⟩
  refine ⟨?_, ?_⟩
  · -- `F(p) = p.1ᵃ • B (ω (p.1 • p.2)) p.2` is built from `C^∞` pieces.
    have hfun : (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) =
        fun p => p.1 ^ a • B (ω (p.1 • p.2)) p.2 := by
      funext p; rw [hB]
    rw [hfun]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    -- Naming the codomain `F` lets the normed instances on `Covector` be unified with `B`'s.
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => B (ω (p.1 • p.2))) := by
      exact (ContinuousLinearMap.contDiff (F := Eucl P →L[ℝ] Covector (Eucl P) k) B).comp
        (hω.comp hs)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × Eucl P => B (ω (p.1 • p.2)) p.2) :=
      h1.clm_apply contDiff_snd
    exact (contDiff_fst.pow a).smul h2
  · intro t x w v
    have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
        fun z => t ^ a • B (ω (t • z)) z := by
      funext z; rw [hB]
    rw [hfun]
    have hω' : HasFDerivAt ω (fderiv ℝ ω (t • x)) (t • x) :=
      (hω.differentiable (by simp) (t • x)).hasFDerivAt
    have hs : HasFDerivAt (fun z : Eucl P => t • z) (t • ContinuousLinearMap.id ℝ (Eucl P)) x :=
      (hasFDerivAt_id x).const_smul t
    -- Chain rule for `z ↦ B (ω (t • z))`.
    have hc : HasFDerivAt (fun z : Eucl P => B (ω (t • z)))
        (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))) x := by
      exact HasFDerivAt.comp (F := Covector (Eucl P) (k + 1))
        (G := Eucl P →L[ℝ] Covector (Eucl P) k) x
        (ContinuousLinearMap.hasFDerivAt (F := Eucl P →L[ℝ] Covector (Eucl P) k) B)
        (hω'.comp x hs)
    -- Product rule for `z ↦ B (ω (t • z)) z`, then scaling by `tᵃ`.
    have happ := hc.clm_apply (hasFDerivAt_id x)
    have hf : HasFDerivAt (fun z : Eucl P => t ^ a • B (ω (t • z)) z)
        (t ^ a • ((B (ω (t • x))).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
          (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))).flip x)) x :=
      happ.const_smul (t ^ a)
    -- Evaluate at `w` and `v`; `Matrix.vecCons` is definitionally `Fin.cons`.
    rw [hf.fderiv]
    simp only [_root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, hB,
      ContinuousAlternatingMap.curryLeft_apply_apply, map_smul, smul_eq_mul,
      ContinuousAlternatingMap.curryLeft_smul]
    rw [add_comm]
    rfl
/-- Bound on the `j`-th derivative of the radial-homotopy integrand: for `t ∈ [0, 1]` and
`‖x‖ ≤ R`, `‖D^j (z ↦ t^a • ι_z ω(t z))(x)‖ ≤ (R + j) D` when `‖D^i ω‖ ≤ D` on `closedBall 0 R`
for all `i ≤ j`.  Writing the integrand as `t^a • B (g z) z` with `g z = ω (t • z)` and `B` the
interior product (`‖B u v‖ ≤ ‖u‖ ‖v‖`), the Leibniz rule for `z ↦ B (g z) z`, proved below by
induction on the order, gives `‖D^j (B (g ·) ·)(x)‖ ≤ ‖x‖ ‖D^j g(x)‖ + j ‖D^(j-1) g(x)‖`, and
`‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` since `‖t x‖ ≤ R`. -/
theorem Submission.iwl_cr_ro_integrand_iteratedFDeriv_le :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
        (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R,
          ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤
            (R + j) * D := by
  intro P k a ω hω j R D hD hbound t ht x hx
  -- Leibniz bound for `z ↦ B (g z) z`.  Since `D (B (g ·) ·)(z) = B (g z) + B' (Dg z) z` with
  -- `B' A z h = B (A h) z`, again of the same shape, induction on the order gives
  -- `‖D^n (B (g ·) ·)(y)‖ ≤ ‖y‖ ‖D^n g(y)‖ + n ‖D^(n-1) g(y)‖`.
  have leibniz : ∀ (n : ℕ) (F G : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : F →L[ℝ] Eucl P →L[ℝ] G),
      (∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) →
      ∀ g : Eucl P → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ y : Eucl P,
        ‖iteratedFDeriv ℝ n (fun z => B (g z) z) y‖ ≤
          ‖y‖ * ‖iteratedFDeriv ℝ n g y‖ + n * ‖iteratedFDeriv ℝ (n - 1) g y‖ := by
    intro n
    induction n with
    | zero =>
      intro F G _ _ _ _ B hB g hg y
      rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, Nat.cast_zero, zero_mul, add_zero,
        mul_comm]
      exact hB (g y) y
    | succ n ih =>
      intro F G _ _ _ _ B hB g hg y
      obtain ⟨B', hB'apply, hB'bound⟩ :
          ∃ B' : (Eucl P →L[ℝ] F) →L[ℝ] Eucl P →L[ℝ] Eucl P →L[ℝ] G,
            (∀ A z h, B' A z h = B (A h) z) ∧ ∀ A z, ‖B' A z‖ ≤ ‖A‖ * ‖z‖ := by
        refine ⟨((ContinuousLinearMap.compL ℝ (Eucl P) F G).comp B.flip).flip,
          fun A z h => rfl, fun A z => ?_⟩
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        show ‖B (A h) z‖ ≤ ‖A‖ * ‖z‖ * ‖h‖
        calc ‖B (A h) z‖ ≤ ‖A h‖ * ‖z‖ := hB (A h) z
          _ ≤ ‖A‖ * ‖h‖ * ‖z‖ := by gcongr; exact A.le_opNorm h
          _ = ‖A‖ * ‖z‖ * ‖h‖ := by ring
      have hBnorm : ‖B‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [one_mul]
        exact hB u v
      have hgd : Differentiable ℝ g := (contDiff_infty_iff_fderiv.1 hg).1
      have hdg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
        (contDiff_infty_iff_fderiv.1 hg).2
      have hderiv : fderiv ℝ (fun z => B (g z) z) = fun z => B (g z) + B' (fderiv ℝ g z) z := by
        funext z
        have h1 : HasFDerivAt (fun z => B (g z)) (B.comp (fderiv ℝ g z)) z :=
          B.hasFDerivAt.comp z (hgd z).hasFDerivAt
        have h2 : HasFDerivAt (fun z => B (g z) z)
            ((B (g z)).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
              (B.comp (fderiv ℝ g z)).flip z) z :=
          h1.clm_apply (hasFDerivAt_id z)
        rw [h2.fderiv]
        ext h
        simp [hB'apply]
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B (g z)) := B.contDiff.comp hg
      have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B' (fderiv ℝ g z) z) :=
        B'.isBoundedBilinearMap.contDiff.comp (hdg.prodMk contDiff_id)
      have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
      have hadd : iteratedFDeriv ℝ n (fun z => B (g z) + B' (fderiv ℝ g z) z) y =
          iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y :=
        iteratedFDeriv_add_apply (hc1.contDiffAt.of_le hle) (hc2.contDiffAt.of_le hle)
      have hcomp : iteratedFDeriv ℝ n (fun z => B (g z)) y =
          B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y) :=
        B.iteratedFDeriv_comp_left hg.contDiffAt hle
      have e1 : ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ ≤ ‖iteratedFDeriv ℝ n g y‖ := by
        rw [hcomp]
        calc ‖B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y)‖
            ≤ ‖B‖ * ‖iteratedFDeriv ℝ n g y‖ := B.norm_compContinuousMultilinearMap_le _
          _ ≤ 1 * ‖iteratedFDeriv ℝ n g y‖ := by gcongr
          _ = ‖iteratedFDeriv ℝ n g y‖ := one_mul _
      have e2 := ih (Eucl P →L[ℝ] F) (Eucl P →L[ℝ] G) B' hB'bound (fderiv ℝ g) hdg y
      rw [norm_iteratedFDeriv_fderiv] at e2
      have e3 : (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) (fderiv ℝ g) y‖ =
          n * ‖iteratedFDeriv ℝ n g y‖ := by
        rcases n with _ | m
        · simp
        · rw [norm_iteratedFDeriv_fderiv, Nat.add_sub_cancel]
      rw [e3] at e2
      rw [← norm_iteratedFDeriv_fderiv, hderiv, hadd, Nat.add_sub_cancel]
      calc ‖iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖
          ≤ ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ +
            ‖iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ n g y‖ +
            (‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ + n * ‖iteratedFDeriv ℝ n g y‖) :=
              add_le_add e1 e2
        _ = ‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ +
            ((n + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ n g y‖ := by push_cast; ring
  -- The interior product `B α = α.curryLeft`, a linear isometry, so `‖B u v‖ ≤ ‖u‖ ‖v‖`.
  obtain ⟨B, hB, hBbound⟩ :
      ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] Eucl P →L[ℝ] Covector (Eucl P) k,
        (∀ α, B α = α.curryLeft) ∧ ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖ := by
    refine ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
      (n := k)).toContinuousLinearMap, fun α => rfl, fun u v => ?_⟩
    calc ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u v‖
        ≤ ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖u‖ * ‖v‖ := by
          rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hR : 0 ≤ R := (norm_nonneg x).trans hx'
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
      fun z => t ^ a • B (ω (t • z)) z := by
    funext z; rw [hB]
  rw [hfun]
  -- `g z = ω (L z)` with `L = t • id`, `‖L‖ ≤ 1`, so `‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` for `i ≤ j`.
  set L : Eucl P →L[ℝ] Eucl P := t • ContinuousLinearMap.id ℝ (Eucl P) with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖ContinuousLinearMap.id ℝ (Eucl P)‖ ≤ 1 * 1 :=
          mul_le_mul ht1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgfun : (fun z : Eucl P => ω (t • z)) = ω ∘ L := by
    funext z; simp [hL]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => ω (t • z)) := by
    rw [hgfun]; exact hω.comp L.contDiff
  have hgnorm : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ ≤ D := by
    intro i hi
    rw [hgfun, L.iteratedFDeriv_comp_right hω x (by exact_mod_cast le_top)]
    have hLx : L x ∈ closedBall (0 : Eucl P) R := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ 1 * R := mul_le_mul hLnorm hx' (norm_nonneg x) zero_le_one
        _ = R := one_mul R
    calc ‖(iteratedFDeriv ℝ i ω (L x)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ i ω (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ D * 1 := by
          apply mul_le_mul (hbound i hi _ hLx) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
      _ = D := mul_one D
  -- Pull out `t^a` (`0 ≤ t^a ≤ 1`) and apply the Leibniz bound.
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => B (ω (t • z)) z) :=
    B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)
  have hsmul : iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • B (ω (t • z)) z) x =
      t ^ a • iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x :=
    iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [hsmul, norm_smul]
  have hta : ‖t ^ a‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1
  have key := leibniz j _ _ B hBbound (fun z => ω (t • z)) hg x
  have hsum : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ +
      j * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ (R + j) * D := by
    have e1 : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ ≤ R * D :=
      mul_le_mul hx' (hgnorm j le_rfl) (norm_nonneg _) hR
    have e2 : (j : ℝ) * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ j * D :=
      mul_le_mul_of_nonneg_left (hgnorm (j - 1) (Nat.sub_le j 1)) (Nat.cast_nonneg j)
    linarith
  calc ‖t ^ a‖ * ‖iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x‖
      ≤ 1 * ((R + j) * D) := mul_le_mul hta (key.trans hsum) (norm_nonneg _) zero_le_one
    _ = (R + j) * D := one_mul _

/-- The radial homotopy operator `ψ(x) = ∫₀¹ tᵃ x ⌟ ω(t x) dt` (proof of Simon Ch. 6, 8.2,
Part I): for a smooth `(k + 1)`-form `ω`, `ψ` is a smooth `k`-form with
(i) `ψ(x)(v) = ∫₀¹ tᵃ ω(t x)(x, v) dt`,
(ii) `Dψ(x)[w](v) = ∫₀¹ tᵃ (t Dω(t x)[w](x, v) + ω(t x)(w, v)) dt`, and
(iii) `‖Dʲψ(x)‖ ≤ (R + j) D` on `B̄_R(0)` whenever `‖Dⁱω‖ ≤ D` there for all `i ≤ j`.
The integrand `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is jointly smooth, so `ψ = ∫₀¹ F(t, ·) dt`
is smooth with `Dʲψ = ∫₀¹ Dʲ_x F dt`; evaluation commutes with the integral. -/
theorem Submission.iwl_cr_radial_operator :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∃ ψ : DifferentialForm (Eucl P) k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
        (∀ (x : Eucl P) (v : Fin k → Eucl P),
          ψ x v = ∫ t in (0 : ℝ)..1, t ^ a * ω (t • x) (Fin.cons x v)) ∧
        (∀ (x w : Eucl P) (v : Fin k → Eucl P),
          fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1,
            t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v))) ∧
        ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
          (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
          ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D := by
  intro P k a ω hω
  -- `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is smooth; `ψ = ∫₀¹ F(t, ·) dt` and
  -- `Dʲψ(x) = ∫₀¹ Dʲ(F(t, ·))(x) dt`, with `(t, x) ↦ Dʲ(F(t, ·))(x)` continuous.
  obtain ⟨hGsmooth, hGderiv⟩ := Submission.iwl_cr_ro_integrand_contDiff_fderiv P k a ω hω
  obtain ⟨hψsmooth, hGcont, hψiter⟩ :=
    Submission.iwl_cr_ro_intervalIntegral_contDiff P (Covector (Eucl P) k) _ 0 1 hGsmooth
  dsimp only at hψsmooth hGcont hψiter
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, t ^ a • (ω (t • x)).curryLeft x, hψsmooth, ?_, ?_, ?_⟩
  · -- (i): evaluation at `v` is a continuous linear map, so it commutes with the integral.
    intro x v
    have hc : Continuous fun t : ℝ => t ^ a • (ω (t • x)).curryLeft x :=
      hGsmooth.continuous.comp (continuous_id.prodMk continuous_const)
    have e := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousAlternatingMap.apply_apply] at e
    beta_reduce
    rw [← e]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      smul_eq_mul]
    rfl
  · -- (ii): `Dψ(x)[w] = D¹ψ(x)(w)`; evaluate `∫₀¹ D¹(F(t, ·))(x) dt` at `w`, then at `v`.
    intro x w v
    have hc₁ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x :=
      (hGcont 1).comp (continuous_id.prodMk continuous_const)
    have hc₂ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x (fun _ => w) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
        (fun _ => w)).continuous.comp hc₁
    have e₁ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
      (fun _ => w)).intervalIntegral_comp_comm (hc₁.intervalIntegrable (μ := volume) 0 1)
    have e₂ := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc₂.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousMultilinearMap.apply_apply, ContinuousAlternatingMap.apply_apply] at e₁ e₂
    have e₀ : ∀ f : Eucl P → Covector (Eucl P) k,
        fderiv ℝ f x w = iteratedFDeriv ℝ 1 f x (fun _ => w) :=
      fun f => (iteratedFDeriv_one_apply (fun _ : Fin 1 => w)).symm
    rw [e₀, hψiter 1 x, ← e₁, ← e₂]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [iteratedFDeriv_one_apply]
    exact hGderiv t x w v
  · -- (iii): `‖Dʲψ(x)‖ ≤ ∫₀¹ ‖Dʲ(F(t, ·))(x)‖ dt ≤ (R + j) D`.
    intro j R D hD hω_le x hx
    rw [hψiter j x]
    have hle : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun z => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Submission.iwl_cr_ro_integrand_iteratedFDeriv_le P k a ω hω j R D hD hω_le t
        ⟨ht.1.le, ht.2⟩ x hx
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rwa [sub_zero, abs_one, mul_one] at h
/-- Pointwise integrand identity of the radial homotopy formula: for `L : E →L[ℝ] Λ^{k+1}(E)`,
`α ∈ Λ^{k+1}(E)`, `x ∈ E`, `u ∈ E^{k+1}`, `t ∈ ℝ` and `û_j = removeNth j u`,
`t^{k+1} Alt(L)(x, u) + ∑_j (-1)^j t^k (t L(u_j)(x, û_j) + α(u_j, û_j))
  = t^{k+1} L(x)(u) + (k + 1) t^k α(u)`.
Expanding `Alt(L)(x, u) = L(x)(u) - ∑_j (-1)^j L(u_j)(x, û_j)` cancels the `t^{k+1}` cross
terms, and `alternatizeUncurryFin (curryLeft α) = (k + 1) • α` evaluates the `α`-sum. -/
theorem Submission.iwl_cr_rh_integrand_identity :
    ∀ (P k : ℕ) (L : Eucl P →L[ℝ] Covector (Eucl P) (k + 1)) (α : Covector (Eucl P) (k + 1))
      (x : Eucl P) (u : Fin (k + 1) → Eucl P) (t : ℝ),
      t ^ (k + 1) * ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) +
          ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
            (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) +
              α (Fin.cons (u j) (Fin.removeNth j u)))) =
        t ^ (k + 1) * L x u + ((k : ℝ) + 1) * t ^ k * α u := by
  intro P k L α x u t
  -- `removeNth (j + 1) (x, u) = (x, removeNth j u)`.
  have hrem : ∀ j : Fin (k + 1),
      Fin.removeNth j.succ (Fin.cons x u : Fin (k + 2) → Eucl P) =
        Fin.cons x (Fin.removeNth j u) :=
    fun j => Fin.cons_comp_succ_succAbove x u j
  -- Split `Alt(L)(x, u)` into the index `0` and the indices `j.succ`.
  have hA : ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) =
      L x u - ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
        L (u j) (Fin.cons x (Fin.removeNth j u)) := by
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
      Fin.val_succ, Fin.cons_succ, hrem, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      pow_succ, mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  -- `∑_j (-1)^j α(u_j, û_j) = (k + 1) α(u)`: evaluate `Alt(curryLeft α) = (k + 1) • α` at `u`.
  have hB : ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * α (Fin.cons (u j) (Fin.removeNth j u)) =
      ((k : ℝ) + 1) * α u := by
    have h := congrArg (fun f => f u) (ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft α)
    simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.smul_apply,
      zsmul_eq_mul, nsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.cast_add,
      Nat.cast_one] at h
    exact h
  -- Distribute `(-1)^j t^k (t a_j + b_j) = t^{k+1} (-1)^j a_j + t^k (-1)^j b_j` over the sum.
  have hsum : ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
        (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) +
          α (Fin.cons (u j) (Fin.removeNth j u)))) =
      t ^ (k + 1) * ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
          L (u j) (Fin.cons x (Fin.removeNth j u)) +
        t ^ k * ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
          α (Fin.cons (u j) (Fin.removeNth j u)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hA, hsum, hB]
  ring

/-- Radial fundamental theorem of calculus: for a smooth form `φ`,
`∫₀¹ (t^(m+1) Dφ(t x)[x](u) + (m + 1) t^m φ(t x)(u)) dt = φ(x)(u)`, since the integrand is the
derivative of `g(t) = t^(m+1) φ(t x)(u)` and `g(1) - g(0) = φ(x)(u)`. -/
theorem Submission.iwl_cr_rh_radial_ftc :
    ∀ (P n m : ℕ) (φ : DifferentialForm (Eucl P) n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ (x : Eucl P) (u : Fin n → Eucl P),
        ∫ t in (0 : ℝ)..1, (t ^ (m + 1) * fderiv ℝ φ (t • x) x u +
          ((m : ℝ) + 1) * t ^ m * φ (t • x) u) = φ x u := by
  intro P n m φ hφ x u
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- `g(s) = s^(m+1) φ(s x)(u)` has the integrand as derivative at every `t`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s ^ (m + 1) * φ (s • x) u)
        (t ^ (m + 1) * fderiv ℝ φ (t • x) x u + ((m : ℝ) + 1) * t ^ m * φ (t • x) u) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => φ (s • x)) (fderiv ℝ φ (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun s : ℝ => φ (s • x) u) (fderiv ℝ φ (t • x) x u) t :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).hasFDerivAt.comp_hasDerivAt t h2
    refine ((hasDerivAt_pow (m + 1) t).fun_mul h3).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  -- The integrand is continuous, hence interval integrable.
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (m + 1) * fderiv ℝ φ (t • x) x u +
      ((m : ℝ) + 1) * t ^ m * φ (t • x) u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hc1 : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x u := by
      have : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x :=
        (hcont.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
      exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).continuous.comp this
    have hc2 : Continuous fun t : ℝ => φ (t • x) u :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).continuous.comp
        (hφ.continuous.comp (continuous_id.smul continuous_const))
    exact ((continuous_pow (m + 1)).mul hc1).add
      ((continuous_const.mul (continuous_pow m)).mul hc2)
  -- Fundamental theorem of calculus on `[0, 1]`: `g(1) - g(0) = φ(x)(u) - 0`.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- Radial homotopy formula in degree zero: if `χ(x)(v) = ∫₀¹ t⁰ dφ(t x)(x, v) dt` for a smooth
`0`-form `φ`, then `χ(x) = φ(x) - φ(0)` (fundamental theorem of calculus along `t ↦ t x`). -/
theorem Submission.iwl_cr_rh_degree_zero :
    ∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ (x : Eucl P) (v : Fin 0 → Eucl P),
        χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) →
      ∀ x, χ x = φ x - φ 0 := by
  intro P φ χ hφ hχ x
  ext v
  -- `dφ(t x)(x, v) = Dφ(t x)[x](v)`: the alternating sum has the single term `i = 0`.
  have hd : ∀ t : ℝ, extDeriv φ (t • x) (Fin.cons x v) = fderiv ℝ φ (t • x) x v := by
    intro t
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [hχ x v, ContinuousAlternatingMap.sub_apply]
  simp only [pow_zero, one_mul, hd]
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- `s ↦ φ(s x)(v)` has derivative `Dφ(t x)[x](v)` at every `t`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => φ (s • x) v) (fderiv ℝ φ (t • x) x v) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => φ (s • x)) (fderiv ℝ φ (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).hasFDerivAt.comp_hasDerivAt t h2
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ φ (t • x) x v) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x :=
      (hcont.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).continuous.comp this
  -- Fundamental theorem of calculus on `[0, 1]`.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **Radial homotopy formula on `ℝ^P`** (the form version of Simon Ch. 6, 2.25–2.26 and 2.31 for
the homotopy `(t, x) ↦ t x`, used by the cone construction in the proof of 8.2).
(a) If `φ` is a smooth `(k + 1)`-form, `Dψ(x)[w](v) = ∫₀¹ tᵏ (t Dφ(tx)[w](x, v) + φ(tx)(w, v)) dt`
and `χ(x)(v) = ∫₀¹ tᵏ⁺¹ dφ(tx)(x, v) dt`, then `χ + dψ = φ`, i.e. `H(dφ) + d(H′φ) = φ`.
(b) For a smooth `0`-form `φ`, `H(dφ)(x) = φ(x) − φ(0)`.

For (a), `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ)` with `ûⱼ = removeNth j u`.  All integrands are
continuous, so `χ(x)(u) + dψ(x)(u)` is a single integral over `[0, 1]`.  The cross terms cancel and
`∑ⱼ (-1)ʲ α(uⱼ, ûⱼ) = (k + 1) α(u)`, so its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`,
the derivative of `t ↦ tᵏ⁺¹ φ(tx)(u)`, whose integral over `[0, 1]` is `φ(x)(u)`. -/
theorem Submission.iwl_cr_radial_homotopy : (∀ (P k : ℕ) (φ : DifferentialForm (Eucl P) (k + 1)) (ψ : DifferentialForm (Eucl P) k) (χ : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x w : Eucl P) (v : Fin k → Eucl P), fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1, t ^ k * (t * fderiv ℝ φ (t • x) w (Fin.cons x v) + φ (t • x) (Fin.cons w v))) → (∀ (x : Eucl P) (v : Fin (k + 1) → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ (k + 1) * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x + extDeriv ψ x = φ x) ∧ (∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x : Eucl P) (v : Fin 0 → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x = φ x - φ 0) := by
  refine ⟨fun P k φ ψ χ hφ hψ hχ x => ?_, Submission.iwl_cr_rh_degree_zero⟩
  -- `φ`, `Dφ`, `dφ = alternatizeUncurryFinCLM ∘ Dφ` and `t ↦ t • x` are continuous.
  have hφc : Continuous φ := hφ.continuous
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hdφ : Continuous (extDeriv φ) :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp hDφ
  have hsx : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
  ext u
  -- The `j`-th integrand of `dψ(x)(u)` and the integrand of `χ(x)(u)` are continuous in `t`.
  have hg : ∀ j : Fin (k + 1), Continuous fun t : ℝ => t ^ k * (t * fderiv ℝ φ (t • x) (u j)
      (Fin.cons x (Fin.removeNth j u)) + φ (t • x) (Fin.cons (u j) (Fin.removeNth j u))) := by
    intro j
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (t • x) (u j) (Fin.cons x (Fin.removeNth j u)) :=
      ((hDφ.comp hsx).clm_apply continuous_const).eval_const _
    have h2 : Continuous fun t : ℝ => φ (t • x) (Fin.cons (u j) (Fin.removeNth j u)) :=
      (hφc.comp hsx).eval_const _
    exact (continuous_pow k).mul ((continuous_id.mul h1).add h2)
  have hf : Continuous fun t : ℝ => t ^ (k + 1) * extDeriv φ (t • x) (Fin.cons x u) :=
    (continuous_pow (k + 1)).mul ((hdφ.comp hsx).eval_const _)
  -- `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ) = ∑ⱼ (-1)ʲ ∫₀¹ tᵏ (t Dφ(tx)[uⱼ](x, ûⱼ) + φ(tx)(uⱼ, ûⱼ)) dt`.
  have hdψ : extDeriv ψ x u = ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
      ∫ t in (0 : ℝ)..1, t ^ k * (t * fderiv ℝ φ (t • x) (u j) (Fin.cons x (Fin.removeNth j u)) +
        φ (t • x) (Fin.cons (u j) (Fin.removeNth j u))) := by
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψ x (u j) (Fin.removeNth j u), zsmul_eq_mul]
    push_cast
    rfl
  rw [ContinuousAlternatingMap.add_apply, hχ x u, hdψ]
  -- Collect `χ(x)(u) + dψ(x)(u)` into a single integral over `[0, 1]`.
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun j _ => ((hg j).const_mul _).intervalIntegrable 0 1,
    ← intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
      ((continuous_finsetSum _ fun j _ => (hg j).const_mul _).intervalIntegrable 0 1)]
  -- Its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`, so the integral is `φ(x)(u)`.
  rw [← Submission.iwl_cr_rh_radial_ftc P (k + 1) k φ hφ x u]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact Submission.iwl_cr_rh_integrand_identity P k (fderiv ℝ φ (t • x)) (φ (t • x)) x u t

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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
