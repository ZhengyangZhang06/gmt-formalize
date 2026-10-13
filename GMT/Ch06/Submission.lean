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

/-- The orientation induced by a linear map (Simon Ch. 6, 3.4–3.5, p. 147, at a single point):
if `τ` is orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₙ` and `A_# w ≠ 0`, then `Aτ₁, …, Aτₙ` are linearly
independent, and for their Gram–Schmidt orthonormalization `σ` (same span)
`A_# w = ±|A_# w| σ₁ ∧ ⋯ ∧ σₙ`.  Writing `Aτᵢ = ∑ⱼ Bᵢⱼ σⱼ`, the determinant identity of the
hypothesis gives `A_# w = ±det B σ₁ ∧ ⋯ ∧ σₙ`, and `|σ₁ ∧ ⋯ ∧ σₙ| = 1`
(`Submission.lpf_pi_simple_unit_facts`), so `|A_# w| = |det B|`. -/
theorem Submission.lpf_pi_induced_orientation :
    ((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 =
        (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧
      ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
        simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) →
    ∀ (P Q n : ℕ) (τ : Fin n → Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (w : NVector (Eucl P) n),
      Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) →
      nVectorPushforward n A w ≠ 0 →
      LinearIndependent ℝ (fun i => A (τ i)) ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧
        Submodule.span ℝ (range σ) = Submodule.span ℝ (range (fun i => A (τ i))) ∧
        (nVectorPushforward n A w = ‖nVectorPushforward n A w‖ • simpleNVector σ ∨
          nVectorPushforward n A w = -(‖nVectorPushforward n A w‖ • simpleNVector σ)) := by
  intro hsna P Q n τ A w _hτ hw hne
  -- `‖c • s‖ = |c| ‖s‖` for the operator norm on `n`-vectors (`NormSMulClass` is not inferred).
  have hnorm_smul : ∀ (c : ℝ) (s : NVector (Eucl Q) n), ‖c • s‖ = |c| * ‖s‖ := by
    intro c s
    apply le_antisymm
    · simpa [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c s
    · rcases eq_or_ne c 0 with rfl | hc
      · simp only [abs_zero, zero_mul]
        exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • s)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv, Real.norm_eq_abs] at h
        have hc' : 0 < |c| := abs_pos.mpr hc
        calc |c| * ‖s‖ ≤ |c| * (|c|⁻¹ * ‖c • s‖) := by gcongr
          _ = ‖c • s‖ := by rw [← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]
  set v : Fin n → Eucl Q := fun i => A (τ i)
  -- `A_# w = ε • (Aτ₁ ∧ ⋯ ∧ Aτₙ)` with `ε = ±1`.
  have hsimple : nVectorPushforward n A (simpleNVector τ) = simpleNVector v :=
    nVectorPushforward_simple A τ
  obtain ⟨ε, hpush⟩ : ∃ ε : ℝ, nVectorPushforward n A w = ε • simpleNVector v := by
    rcases hw with rfl | rfl
    · exact ⟨1, by rw [hsimple, one_smul]⟩
    · refine ⟨-1, ?_⟩
      ext α
      show -(α (fun i => A (τ i))) = (-1 : ℝ) * α (fun i => A (τ i))
      ring
  -- (i): covectors vanish on linearly dependent families, so `Aτ₁ ∧ ⋯ ∧ Aτₙ` would be `0`.
  have hli : LinearIndependent ℝ v := by
    by_contra h
    apply hne
    have h0 : simpleNVector v = 0 := by
      ext α
      simp only [simpleNVector_apply]
      exact α.toAlternatingMap.map_linearDependent v h
    rw [hpush, h0, smul_zero]
  refine ⟨hli, ?_⟩
  -- (ii): the Gram–Schmidt orthonormalization `σ` of `Aτ` spans the same space.
  set σ := InnerProductSpace.gramSchmidtNormed ℝ v
  have hσ : Orthonormal ℝ σ := InnerProductSpace.gramSchmidtNormed_orthonormal hli
  have hspan : Submodule.span ℝ (range σ) = Submodule.span ℝ (range v) :=
    (InnerProductSpace.span_gramSchmidtNormed_range v).trans
      (InnerProductSpace.span_gramSchmidt ℝ v)
  refine ⟨σ, hσ, hspan, ?_⟩
  -- `Aτᵢ = ∑ⱼ Bᵢⱼ σⱼ`, so `Aτ₁ ∧ ⋯ ∧ Aτₙ = det B • σ₁ ∧ ⋯ ∧ σₙ`.
  have hmem : ∀ i, v i ∈ Submodule.span ℝ (range σ) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, ∀ i, ∑ j, B i j • σ j = v i := by
    choose B hB using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem i)
    exact ⟨B, hB⟩
  have hdet := hsna.2 Q n B σ
  rw [show (fun i => ∑ j, B i j • σ j) = v from funext hB] at hdet
  have hpush' : nVectorPushforward n A w = (ε * B.det) • simpleNVector σ := by
    rw [hpush, hdet, smul_smul]
  -- `‖σ₁ ∧ ⋯ ∧ σₙ‖ = 1`, so `‖A_# w‖ = |ε det B|`; the sign of `ε det B` decides the case.
  have hnorm : ‖nVectorPushforward n A w‖ = |ε * B.det| := by
    rw [hpush', hnorm_smul, (Submission.lpf_pi_simple_unit_facts hsna).1 Q n σ hσ, mul_one]
  rcases le_or_gt 0 (ε * B.det) with h | h
  · left
    rw [hnorm, abs_of_nonneg h]
    exact hpush'
  · right
    rw [hnorm, abs_of_neg h, hpush']
    ext α
    show (ε * B.det) * simpleNVector σ α = -(-(ε * B.det) * simpleNVector σ α)
    ring
/-- Step 2 of Simon Ch. 6, Lemma 3.9 (p. 148): local essential bound for the tangential Jacobian
of the push-forward (3.6).  If `(M, θ, ξ)` is a rectifiable triple in `U`, `f` is locally Lipschitz
on `U` and `L x` agrees `Hⁿ⌞M`-a.e. with the directional derivatives of `f` along the approximate
tangent space, then `‖(L x)_# ξ(x)‖` is essentially bounded on `M ∩ K` for compact `K ⊆ U`: with
`Λ` a Lipschitz constant of `f` on a compact neighbourhood of `K` in `U`, `|L(x) τᵢ| ≤ Λ` for the
orthonormal frame `τ` of `TₓM`, so `‖(L x)_# (±τ₁ ∧ ⋯ ∧ τₙ)‖ ≤ ∏ᵢ |L(x) τᵢ| ≤ Λⁿ`. -/
theorem Submission.lpf_pi_jacobian_local_bound :
    ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
      (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U →
      IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f →
      (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt n M θ x Tx →
          ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) →
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ C : ℝ,
        ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ K →
          ‖nVectorPushforward n (L x) (ξ x)‖ ≤ C := by
  intro P Q n U M θ ξ f L hU htri hf hderiv K hK hKU
  -- A Lipschitz constant `Λ` of `f` on a compact `K'` with `K ⊆ interior K'` and `K' ⊆ U`.
  obtain ⟨K', hK'c, hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨Λ, hΛ⟩ := (hf.mono hK'U).exists_lipschitzOnWith_of_compact hK'c
  refine ⟨(Λ : ℝ) ^ n, ?_⟩
  -- At a.e. `x`: `ξ x = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal frame `τ` of `TₓM`, and the
  -- derivative clause holds.
  filter_upwards [htri.orients, hderiv] with x hor hdx hxK
  obtain ⟨τ, hτ, htan, hξ⟩ := hor
  -- `|L(x) τᵢ| ≤ Λ`: `t ↦ f (x + t • τᵢ)` is `Λ`-Lipschitz near `0` with derivative `L(x) τᵢ`.
  have hbound : ∀ i, ‖L x (τ i)‖ ≤ Λ := by
    intro i
    have hd := hdx _ htan (τ i) (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x (hKK' hxK)
    have hg : LipschitzOnWith 1 (fun t : ℝ => x + t • τ i) (Metric.ball 0 ρ) := by
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro s t
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hτ.1 i,
        mul_one, NNReal.coe_one, one_mul]
    have hmaps : MapsTo (fun t : ℝ => x + t • τ i) (Metric.ball 0 ρ) K' := by
      intro t ht
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hτ.1 i, mul_one]
      simpa using ht
    have hlip : LipschitzOnWith Λ (fun t : ℝ => f (x + t • τ i)) (Metric.ball 0 ρ) := by
      have := hΛ.comp hg hmaps
      rwa [mul_one] at this
    exact hd.le_of_lipschitzOn (Metric.ball_mem_nhds 0 hρ) hlip
  -- `(L x)_# (±simpleNVector τ) = ±simpleNVector (L x ∘ τ)`.
  have hpush : ‖nVectorPushforward n (L x) (ξ x)‖ = ‖simpleNVector (fun i => L x (τ i))‖ := by
    rcases hξ with h | h
    · rw [h, nVectorPushforward_simple]; rfl
    · rw [h]
      have : nVectorPushforward n (L x) (-simpleNVector τ) =
          -simpleNVector (fun i => L x (τ i)) := by
        ext α; rfl
      rw [this]
      exact norm_neg (simpleNVector (fun i => L x (τ i)))
  -- `‖simpleNVector u‖ ≤ ∏ᵢ ‖uᵢ‖`, the bound `simpleNVector` is built with.
  rw [hpush]
  calc ‖simpleNVector (fun i => L x (τ i))‖ ≤ ∏ i, ‖L x (τ i)‖ :=
        LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun i _ => norm_nonneg _) _
    _ ≤ ∏ _i : Fin n, (Λ : ℝ) := by
        gcongr with i
        exact hbound i
    _ = (Λ : ℝ) ^ n := by simp
/-- Measurability part of Step 1 of the integrality of the Lipschitz push-forward (Simon Ch. 6,
(3.6) and Lemma 3.9, pp. 147–148): for a rectifiable triple `(M, θ, ξ)` in an open `U` and an
`Hⁿ⌞M`-a.e. strongly measurable `L`, the multiplicity `θ` is `Hⁿ⌞M`-a.e. measurable and
`x ↦ L(x)_# ξ(x)` is `Hⁿ⌞M`-a.e. strongly measurable. -/
theorem Submission.lpf_pi_measurability : ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → AEStronglyMeasurable L ((μHE[n] : Measure (Eucl P)).restrict M) → AEMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) ∧ AEStronglyMeasurable (fun x => nVectorPushforward n (L x) (ξ x)) ((μHE[n] : Measure (Eucl P)).restrict M) := by
  intro P Q n U M θ ξ L hU hT hL
  constructor
  · -- `θ` is locally `Hⁿ`-integrable on `M` (compact neighbourhoods inside the open `U`), hence
    -- `Hⁿ⌞M`-a.e. strongly measurable since `ℝ^P` is second countable.
    have hloc : LocallyIntegrableOn θ M (μHE[n] : Measure (Eucl P)) := by
      intro x hx
      obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU (hT.subset hx)
      exact ⟨M ∩ K, inter_mem_nhdsWithin M (mem_interior_iff_mem_nhds.mp hxK),
        hT.integrableOn K hK hKU⟩
    exact hloc.aestronglyMeasurable.aemeasurable
  · -- `(A, v) ↦ A_# v = v ∘ A^#` is continuous, as `A ↦ A^#` and composition are.
    have hΦ : Continuous fun p : (Eucl P →L[ℝ] Eucl Q) × NVector (Eucl P) n =>
        nVectorPushforward n p.1 p.2 :=
      continuous_snd.clm_comp
        (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp continuous_fst)
    -- Compose with the `Hⁿ⌞M`-a.e. strongly measurable pair `x ↦ (L x, ξ x)`.
    exact hΦ.comp_aestronglyMeasurable (hL.prodMk hT.aestronglyMeasurable)

/-- **Local finiteness of the pushed-forward weight (Step 4(b) of the integrality of `f_# T`,
Simon Ch. 6, Lemma 3.9).**  Let `T = τ(M, θ, ξ)` in the open `U`, `f` locally Lipschitz on `U`
with `f⁻¹(K) ∩ spt T` compact for every compact `K ⊆ V`, and `L` given by the derivative clause.
Then `∫_{M ∩ f⁻¹(K)} θ ‖L_# ξ‖ dHⁿ < ∞` for compact `K ⊆ V`.  Off the `Hⁿ`-null set
`M \ spt T` (hypothesis (RSN), the statement of `lpf_rectifiable_support_null`), `M ∩ f⁻¹(K)`
lies in the compact `K' = f⁻¹(K) ∩ spt T ⊆ U`.  There `‖L_# ξ‖ ≤ C` a.e.
(`lpf_pi_jacobian_local_bound`) and `θ` is integrable (`IsRectifiableTriple.integrableOn`). -/
theorem Submission.lpf_pi_local_finite_weight : (∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0) → ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → LocallyLipschitzOn U f → (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ ∂(μHE[n] : Measure (Eucl P)) < ∞ := by
  intro hRSN P Q n U V T M θ ξ f L hU htri hT hf hprop hderiv K hK hKV
  -- `K' = f⁻¹(K) ∩ spt T` is compact and lies in `U`, as `spt T ⊆ U`.
  have hK'c : IsCompact (f ⁻¹' K ∩ T.support) := hprop K hK hKV
  have hK'U : f ⁻¹' K ∩ T.support ⊆ U := fun x hx => T.support_subset_domain hx.2
  -- `‖L_# ξ‖ ≤ C` holds `Hⁿ`-a.e. on `M ∩ K'`, and `M \ spt T` is `Hⁿ`-null.
  obtain ⟨C, hC⟩ :=
    Submission.lpf_pi_jacobian_local_bound P Q n U M θ ξ f L hU htri hf hderiv _ hK'c hK'U
  have hnull : (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := hRSN P n U T M θ ξ htri hT
  have hK'meas : MeasurableSet (f ⁻¹' K ∩ T.support) := hK'c.isClosed.measurableSet
  have hsub : M ∩ f ⁻¹' K ⊆ (M ∩ (f ⁻¹' K ∩ T.support)) ∪ (M \ T.support) := by
    intro x hx
    by_cases hxT : x ∈ T.support
    · exact Or.inl ⟨hx.1, hx.2, hxT⟩
    · exact Or.inr ⟨hx.1, hxT⟩
  -- `θ` is integrable on `M ∩ K'`.
  have hint : IntegrableOn θ (M ∩ (f ⁻¹' K ∩ T.support)) (μHE[n] : Measure (Eucl P)) :=
    htri.integrableOn _ hK'c hK'U
  have hθfin : ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support), ENNReal.ofReal (θ x)
      ∂(μHE[n] : Measure (Eucl P)) < ∞ :=
    hint.setLIntegral_lt_top
  -- On `M ∩ K'` the integrand is at most `θ · max C 0` almost everywhere.
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ (f ⁻¹' K ∩ T.support))),
      ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ ≤
        ENNReal.ofReal (θ x) * ENNReal.ofReal (max C 0) := by
    have h1 : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ (f ⁻¹' K ∩ T.support))),
        x ∈ f ⁻¹' K ∩ T.support → ‖nVectorPushforward n (L x) (ξ x)‖ ≤ C :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hC
    have h2 : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ (f ⁻¹' K ∩ T.support))),
        x ∈ M ∩ (f ⁻¹' K ∩ T.support) :=
      ae_restrict_mem₀ (htri.nullMeasurableSet.inter hK'meas.nullMeasurableSet)
    filter_upwards [h1, h2] with x hx1 hx2
    have h3 : ‖nVectorPushforward n (L x) (ξ x)‖ₑ ≤ ENNReal.ofReal (max C 0) := by
      rw [← ofReal_norm (nVectorPushforward n (L x) (ξ x))]
      exact ENNReal.ofReal_le_ofReal ((hx1 hx2.2).trans (le_max_left _ _))
    exact mul_le_mul' le_rfl h3
  -- Split off the null part `M \ spt T`, then bound by `max C 0 · ∫_{M ∩ K'} θ < ∞`.
  calc ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
        ∂(μHE[n] : Measure (Eucl P))
      ≤ ∫⁻ x in (M ∩ (f ⁻¹' K ∩ T.support)) ∪ (M \ T.support),
          ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_set hsub
    _ ≤ ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support),
          ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) +
        ∫⁻ x in M \ T.support, ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) := lintegral_union_le _ _ _
    _ = ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support),
          ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero]
    _ ≤ ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support), ENNReal.ofReal (θ x) * ENNReal.ofReal (max C 0)
          ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hbound
    _ = (∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support), ENNReal.ofReal (θ x)
          ∂(μHE[n] : Measure (Eucl P))) * ENNReal.ofReal (max C 0) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top hθfin ENNReal.ofReal_lt_top
/-- Signed form of a fibre-sum area identity.  If `∫⁻_A h J dμ = ∫⁻ ∑'_{x ∈ A, f x = y} h x dν(y)`
for every `μ⌞A`-a.e. measurable `h : X → [0, ∞]`, and `g : X → ℝ` is `μ⌞A`-a.e. strongly measurable
with `∫⁻_A ‖g‖ₑ J dμ < ∞`, then for `ν`-a.e. `y` the fibre family of `g` over `y` is summable, the
fibre sum of `g` is `ν`-integrable and `∫_A g J dμ = ∫ ∑'_{x ∈ A, f x = y} g x dν(y)`.  Apply the
identity to `ofReal ∘ g` and `ofReal ∘ (-g)`: both sides equal the difference of the two finite
lintegrals, the source side because `g = 0` a.e. where `J = ∞`. -/
theorem Submission.lpf_pi_signed_fibre_sum :
    ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
      (f : X → Y) (A : Set X) (J : X → ℝ≥0∞), AEMeasurable J (μ.restrict A) →
      (∀ h : X → ℝ≥0∞, AEMeasurable h (μ.restrict A) →
        AEMeasurable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) ν ∧
          ∫⁻ x in A, h x * J x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x ∂ν) →
      ∀ g : X → ℝ, AEStronglyMeasurable g (μ.restrict A) → ∫⁻ x in A, ‖g x‖ₑ * J x ∂μ < ∞ →
        (∀ᵐ y ∂ν, Summable (fun x : {x : X // x ∈ A ∧ f x = y} => g x)) ∧
          Integrable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, g x) ν ∧
          ∫ x in A, g x * (J x).toReal ∂μ = ∫ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, g x ∂ν := by
  intro X Y _ _ μ ν f A J hJ harea g hg hfin
  -- The area identity for the parts `ofReal ∘ g` and `ofReal ∘ (-g)`, both bounded by `‖g‖ₑ`.
  have hp_meas : AEMeasurable (fun x => ENNReal.ofReal (g x)) (μ.restrict A) :=
    hg.aemeasurable.ennreal_ofReal
  have hm_meas : AEMeasurable (fun x => ENNReal.ofReal (-g x)) (μ.restrict A) :=
    hg.aemeasurable.neg.ennreal_ofReal
  obtain ⟨hNp_meas, hNp_eq⟩ := harea _ hp_meas
  obtain ⟨hNm_meas, hNm_eq⟩ := harea _ hm_meas
  have hp_le : ∀ x, ENNReal.ofReal (g x) ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hm_le : ∀ x, ENNReal.ofReal (-g x) ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  -- Both fibre sums have finite `ν`-lintegral, hence are finite `ν`-a.e.
  have hIp_lt : ∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun x => mul_le_mul' (hp_le x) le_rfl) hfin
  have hIm_lt : ∫⁻ x in A, ENNReal.ofReal (-g x) * J x ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun x => mul_le_mul' (hm_le x) le_rfl) hfin
  have hNp_fin : ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x) ∂ν ≠ ∞ := by
    rw [← hNp_eq]; exact hIp_lt.ne
  have hNm_fin : ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x) ∂ν ≠ ∞ := by
    rw [← hNm_eq]; exact hIm_lt.ne
  have hNp_ae : ∀ᵐ y ∂ν, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x) < ∞ :=
    ae_lt_top' hNp_meas hNp_fin
  have hNm_ae : ∀ᵐ y ∂ν, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x) < ∞ :=
    ae_lt_top' hNm_meas hNm_fin
  -- On a fibre where both sums are finite, `g = (ofReal ∘ g).toReal - (ofReal ∘ (-g)).toReal` is
  -- a difference of summable families, so it is summable with the difference of the sums.
  have hg_eq : ∀ x, g x = (ENNReal.ofReal (g x)).toReal - (ENNReal.ofReal (-g x)).toReal :=
    fun x => by
      rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
  have hfib : ∀ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x) < ∞ →
      ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x) < ∞ →
      Summable (fun x : {x : X // x ∈ A ∧ f x = y} => g x) ∧
      ∑' x : {x : X // x ∈ A ∧ f x = y}, g x =
        (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x)).toReal -
          (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x)).toReal := by
    intro y hy1 hy2
    have hs1 : Summable (fun x : {x : X // x ∈ A ∧ f x = y} => (ENNReal.ofReal (g x)).toReal) :=
      ENNReal.summable_toReal hy1.ne
    have hs2 : Summable
        (fun x : {x : X // x ∈ A ∧ f x = y} => (ENNReal.ofReal (-g x)).toReal) :=
      ENNReal.summable_toReal hy2.ne
    refine ⟨(hs1.sub hs2).congr (fun x => (hg_eq x).symm), ?_⟩
    rw [tsum_congr (fun x : {x : X // x ∈ A ∧ f x = y} => hg_eq x), hs1.tsum_sub hs2,
      ENNReal.tsum_toReal_eq (f := fun x : {x : X // x ∈ A ∧ f x = y} => ENNReal.ofReal (g x))
        (fun _ => ENNReal.ofReal_ne_top),
      ENNReal.tsum_toReal_eq (f := fun x : {x : X // x ∈ A ∧ f x = y} => ENNReal.ofReal (-g x))
        (fun _ => ENNReal.ofReal_ne_top)]
  -- Target side: the fibre sum of `g` is `ν`-a.e. the difference of the two real fibre sums, so
  -- it is integrable, with integral
  -- `(∫⁻_A (ofReal ∘ g) J).toReal - (∫⁻_A (ofReal ∘ (-g)) J).toReal`.
  have hae_eq : (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, g x) =ᵐ[ν]
      fun y => (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x)).toReal -
        (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x)).toReal := by
    filter_upwards [hNp_ae, hNm_ae] with y hy1 hy2
    exact (hfib y hy1 hy2).2
  have hintp : Integrable
      (fun y => (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hNp_meas hNp_fin
  have hintm : Integrable
      (fun y => (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hNm_meas hNm_fin
  have hint : Integrable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, g x) ν :=
    (hintp.sub' hintm).congr hae_eq.symm
  refine ⟨?_, hint, ?_⟩
  · filter_upwards [hNp_ae, hNm_ae] with y hy1 hy2
    exact (hfib y hy1 hy2).1
  have htarget : ∫ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, g x ∂ν =
      (∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μ).toReal -
        (∫⁻ x in A, ENNReal.ofReal (-g x) * J x ∂μ).toReal := by
    rw [integral_congr_ae hae_eq, integral_sub hintp hintm, integral_toReal hNp_meas hNp_ae,
      integral_toReal hNm_meas hNm_ae, ← hNp_eq, ← hNm_eq]
  -- Source side: `‖g‖ₑ J < ∞` a.e. on `A`, so `g = 0` a.e. where `J = ∞`; hence `g J.toReal` is
  -- integrable, and its positive and negative parts are a.e. `(ofReal ∘ g) J` and
  -- `(ofReal ∘ (-g)) J`, giving the same difference of lintegrals.
  have hgJ_meas : AEMeasurable (fun x => ‖g x‖ₑ * J x) (μ.restrict A) := hg.enorm.mul hJ
  have hgJ_fin : ∀ᵐ x ∂(μ.restrict A), ‖g x‖ₑ * J x < ∞ := ae_lt_top' hgJ_meas hfin.ne
  have hG_int : Integrable (fun x => g x * (J x).toReal) (μ.restrict A) := by
    refine ⟨hg.mul hJ.ennreal_toReal.aestronglyMeasurable, ?_⟩
    show ∫⁻ x, ‖g x * (J x).toReal‖ₑ ∂(μ.restrict A) < ∞
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
    rw [enorm_mul, Real.enorm_eq_ofReal_abs ((J x).toReal), abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
  have hg0 : ∀ᵐ x ∂(μ.restrict A), J x = ∞ → g x = 0 := by
    filter_upwards [hgJ_fin] with x hx hJx
    by_contra hne
    have h1 : ‖g x‖ₑ ≠ 0 := enorm_ne_zero.mpr hne
    rw [hJx, ENNReal.mul_top h1] at hx
    exact lt_irrefl _ hx
  have hpos : ∀ᵐ x ∂(μ.restrict A),
      ENNReal.ofReal (g x * (J x).toReal) = ENNReal.ofReal (g x) * J x := by
    filter_upwards [hg0] with x hx
    by_cases hJx : J x = ∞
    · simp [hx hJx]
    · rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hJx]
  have hneg : ∀ᵐ x ∂(μ.restrict A),
      ENNReal.ofReal (-(g x * (J x).toReal)) = ENNReal.ofReal (-g x) * J x := by
    filter_upwards [hg0] with x hx
    by_cases hJx : J x = ∞
    · simp [hx hJx]
    · rw [← neg_mul, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hJx]
  have hsource : ∫ x in A, g x * (J x).toReal ∂μ =
      (∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μ).toReal -
        (∫⁻ x in A, ENNReal.ofReal (-g x) * J x ∂μ).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG_int, lintegral_congr_ae hpos,
      lintegral_congr_ae hneg]
  rw [hsource, htarget]
/-- The space of `n`-covectors on `ℝ^Q` is finite-dimensional: `α ↦ (α(e_{r(1)}, …, e_{r(n)}))_r`
(`r : Fin n → Fin Q`) is a linear injection into the finite coordinate space
`(Fin n → Fin Q) → ℝ`. -/
theorem Submission.lpf_pi_covector_finiteDimensional :
    ∀ (Q n : ℕ), FiniteDimensional ℝ (Covector (Eucl Q) n) := by
  intro Q n
  classical
  let e : Fin Q → Eucl Q := fun j => EuclideanSpace.single j 1
  -- `F α r = α(e_{r(1)}, …, e_{r(n)})`: the values of `α` on tuples of basis vectors.
  let F : Covector (Eucl Q) n →ₗ[ℝ] ((Fin n → Fin Q) → ℝ) :=
    { toFun := fun α r => α (fun i => e (r i))
      map_add' := by intro a b; ext r; simp
      map_smul' := by intro c a; ext r; simp }
  refine Module.Finite.of_injective F ?_
  intro a b hab
  ext v
  -- Expand each `v i` in the standard basis and use multilinearity.
  have hv : v = fun i => ∑ j, v i j • e j := by
    funext i
    exact ((EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr (v i)).symm.trans (by simp [e])
  have key : ∀ c : Covector (Eucl Q) n, c (fun i => ∑ j, v i j • e j) =
      ∑ r : Fin n → Fin Q, c (fun i => v i (r i) • e (r i)) :=
    fun c => c.toMultilinearMap.map_sum (fun i j => v i j • e j)
  rw [hv, key a, key b]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 := congrFun hab r
  simp only [F, LinearMap.coe_mk, AddHom.coe_mk] at h1
  rw [a.map_smul_univ, b.map_smul_univ, h1]
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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
