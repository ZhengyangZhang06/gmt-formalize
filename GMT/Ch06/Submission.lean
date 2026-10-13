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

/-- For a.e. `t`, the slice `M ∩ f⁻¹{t}` of an `Hᵐ⁺¹`-null-measurable `M` by a measurable `f`
is `Hᵐ`-null-measurable, given that `Hᵐ⁺¹⌞M`-a.e. properties hold `Hᵐ⌞(M ∩ f⁻¹{t})`-a.e. for
a.e. `t`.  With a Borel `B ⊆ M`, `B = M` `Hᵐ⁺¹`-a.e., the slice is the Borel set `B ∩ f⁻¹{t}`
plus the part outside `B`, which is `Hᵐ`-null for a.e. `t`. -/
theorem Submission.slicing_im_st_mf_slice_null_measurable :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (f : Eucl P → ℝ),
      NullMeasurableSet M (μHE[m + 1] : Measure (Eucl P)) → Measurable f →
      (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) →
      ∀ᵐ t ∂(volume : Measure ℝ),
        NullMeasurableSet (M ∩ f ⁻¹' {t}) (μHE[m] : Measure (Eucl P)) := by
  intro P m M f hM hf hNT
  -- A Borel kernel `B ⊆ M` with `B = M` `Hᵐ⁺¹`-a.e.; then `x ∈ B` for `Hᵐ⁺¹⌞M`-a.e. `x`.
  obtain ⟨B, hBM, hB, hBM_ae⟩ := hM.exists_measurable_subset_ae_eq
  have hmemB : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ B := by
    rw [← Measure.restrict_congr_set hBM_ae]
    exact ae_restrict_mem hB
  filter_upwards [hNT (· ∈ B) hmemB] with t ht
  -- The part of the slice outside `B` is `Hᵐ`-null.
  have hnull : (μHE[m] : Measure (Eucl P)) ({x | x ∉ B} ∩ (M ∩ f ⁻¹' {t})) = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans_eq (ae_iff.1 ht))
  -- `M ∩ f⁻¹{t} = (B ∩ f⁻¹{t}) ∪ ({x ∉ B} ∩ M ∩ f⁻¹{t})`: a Borel set plus a null set.
  have hsplit : M ∩ f ⁻¹' {t} = B ∩ f ⁻¹' {t} ∪ {x | x ∉ B} ∩ (M ∩ f ⁻¹' {t}) := by
    ext x
    by_cases hx : x ∈ B
    · simp [hx, hBM hx]
    · simp [hx]
  rw [hsplit]
  exact (hB.inter (hf (measurableSet_singleton t))).nullMeasurableSet.union_null hnull
/-- Exhaustion of an open `U ⊆ ℝ^P` by open sets `W i ⊂⊂ U` such that every compact `K ⊆ U`
lies in some `W i`: `W i = {x : |x| < i, (i + 1)⁻¹ < infEDist x (ℝ^P ∖ U)}`. -/
theorem Submission.cmb_exists_compactly_contained_exhaustion :
    ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ W : ℕ → Set (Eucl P),
      (∀ i, CompactlyContainedOpen (W i) U) ∧
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ i, K ⊆ W i := by
  intro P U hU
  -- `d x = infEDist x Uᶜ` is continuous and positive exactly on `U`.
  have hd : Continuous fun x : Eucl P => infEDist x Uᶜ := continuous_infEDist
  have hpos : ∀ x ∈ U, 0 < infEDist x Uᶜ := fun x hx => by
    rw [infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq, notMem_compl_iff]
    exact hx
  refine ⟨fun i => {x | ‖x‖ < i} ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}, fun i => ?_,
    fun K hK hKU => ?_⟩
  · -- `closure (W i) ⊆ closedBall 0 i ∩ {(i + 1)⁻¹ ≤ d}`, a compact subset of `U`.
    have hcl : closure ({x : Eucl P | ‖x‖ < i} ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}) ⊆
        closedBall 0 i ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ} :=
      closure_minimal (fun x hx => ⟨mem_closedBall_zero_iff.2 hx.1.le,
        show ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ from hx.2.le⟩)
        (isClosed_closedBall.inter (isClosed_le continuous_const hd))
    refine ⟨(isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd),
      (isCompact_closedBall 0 _).of_isClosed_subset isClosed_closure (hcl.trans inter_subset_left),
      fun x hx => ?_⟩
    by_contra hxU
    have h : ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ := (hcl hx).2
    rw [infEDist_zero_of_mem hxU, nonpos_iff_eq_zero, ENNReal.inv_eq_zero] at h
    exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top i, ENNReal.one_ne_top⟩ h
  · -- A compact `K ⊆ U` is bounded and `d` has a positive minimum on it.
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, empty_subset _⟩
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
    obtain ⟨i₁, hi₁⟩ := exists_nat_gt R
    obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hd.continuousOn
    obtain ⟨i₂, hi₂⟩ := ENNReal.exists_inv_nat_lt (hpos x₀ (hKU hx₀K)).ne'
    refine ⟨max i₁ i₂, fun x hx => ⟨?_, ?_⟩⟩
    · show ‖x‖ < ((max i₁ i₂ : ℕ) : ℝ)
      calc ‖x‖ ≤ R := hR x hx
        _ < i₁ := hi₁
        _ ≤ (max i₁ i₂ : ℕ) := Nat.cast_le.2 (le_max_left _ _)
    · show (((max i₁ i₂ : ℕ) : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ
      calc (((max i₁ i₂ : ℕ) : ℝ≥0∞) + 1)⁻¹ ≤ (i₂ : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.2 (by exact_mod_cast (le_max_right i₁ i₂).trans (Nat.le_succ _))
        _ < infEDist x₀ Uᶜ := hi₂
        _ ≤ infEDist x Uᶜ := isMinOn_iff.1 hx₀ x hx

/-- For `L¹`-a.e. `t`, `θ` is `Hᵐ`-integrable on `M ∩ f⁻¹{t} ∩ K` for every compact `K ⊆ U`:
co-area with `g = 1_{Kᵢ} |θ₀|` over a compact exhaustion `Kᵢ` of `U`, `θ₀` a Borel version of
`θ` on `M`, transferred to the slices by the null-transfer hypothesis. -/
theorem Submission.slicing_im_st_mf_slice_integrable :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (f : Eucl P → ℝ) (L : ℝ≥0)
      (G : Eucl P → Eucl P), IsOpen U → M ⊆ U →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) →
      (∀ x, ‖G x‖ ≤ L) →
      (∀ g : Eucl P → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
          (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) =
          ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) →
      (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) →
      ∀ᵐ t ∂(volume : Measure ℝ), ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ (M ∩ f ⁻¹' {t} ∩ K) (μHE[m] : Measure (Eucl P)) := by
  intro P m U M θ f L G hU hMU hθ hG hCA hNT
  -- Compact Borel sets `closure (W i) ⊆ U`; every compact `C ⊆ U` lies in one of them.
  obtain ⟨W, hW, hWK⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
  have hKU : ∀ i, closure (W i) ⊆ U := fun i => (hW i).2.2
  have hKm : ∀ i, MeasurableSet (closure (W i)) := fun _ => isClosed_closure.measurableSet
  have hK : ∀ C : Set (Eucl P), IsCompact C → C ⊆ U → ∃ i, C ⊆ closure (W i) := fun C hC hCU =>
    (hWK C hC hCU).imp fun _ h => h.trans subset_closure
  -- `θ` is a.e. strongly measurable on `M = ⋃ i, M ∩ closure (W i)`; `θ₀` is a Borel version.
  have hM : M = ⋃ i, M ∩ closure (W i) := by
    refine (iUnion_subset fun _ => inter_subset_left).antisymm' fun x hx => ?_
    obtain ⟨i, hi⟩ := hK {x} isCompact_singleton (singleton_subset_iff.2 (hMU hx))
    exact mem_iUnion.2 ⟨i, hx, hi rfl⟩
  have hθm : AEStronglyMeasurable θ ((μHE[m + 1] : Measure (Eucl P)).restrict M) := by
    rw [hM, aestronglyMeasurable_iUnion_iff]
    exact fun i => (hθ _ (hW i).2.1 (hKU i)).aestronglyMeasurable
  obtain ⟨θ₀, hθ₀, hθθ₀⟩ := hθm
  have hGL : ∀ x, ‖G x‖ₑ ≤ (L : ℝ≥0∞) := fun x =>
    enorm_le_coe.2 (NNReal.coe_le_coe.1 (by simpa only [coe_nnnorm] using hG x))
  -- Co-area with `g = 1_{closure (W i)} ‖θ₀‖ₑ`: `∫ J_i dt ≤ L ∫_{M ∩ closure (W i)} ‖θ‖ₑ < ∞`,
  -- so the slice integral `J_i t` is finite for a.e. `t`, simultaneously for all `i`.
  have hfin : ∀ᵐ t ∂(volume : Measure ℝ), ∀ i, ∫⁻ x in M ∩ f ⁻¹' {t},
      (closure (W i)).indicator (fun y => ‖θ₀ y‖ₑ) x ∂(μHE[m] : Measure (Eucl P)) < ∞ := by
    refine ae_all_iff.2 fun i => ?_
    obtain ⟨hJm, hJ⟩ := hCA _ (hθ₀.measurable.enorm.indicator (hKm i))
    refine ae_lt_top' hJm (ne_top_of_le_ne_top ?_ hJ.le)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => mul_le_mul_left (hGL x) _)
    have h₁ : ∫⁻ x in M ∩ closure (W i), ‖θ x‖ₑ ∂(μHE[m + 1] : Measure (Eucl P)) =
        ∫⁻ x in M ∩ closure (W i), ‖θ₀ x‖ₑ ∂(μHE[m + 1] : Measure (Eucl P)) :=
      lintegral_congr_ae ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hθθ₀).mono
        fun x hx => congrArg (‖·‖ₑ) hx)
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_indicator (hKm i),
      Measure.restrict_restrict (hKm i), inter_comm (closure (W i)), ← h₁]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hθ _ (hW i).2.1 (hKU i)).2.ne
  -- For such `t` (with `θ = θ₀` a.e. on the slice), `θ` is integrable on each
  -- `M ∩ f⁻¹{t} ∩ closure (W i)`, hence on `M ∩ f⁻¹{t} ∩ K`.
  filter_upwards [hNT (fun x => θ x = θ₀ x) hθθ₀, hfin] with t ht hti K hKc hKsub
  obtain ⟨i, hi⟩ := hK K hKc hKsub
  have hS : ∀ᵐ x ∂(μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t} ∩ closure (W i)),
      θ x = θ₀ x := ae_restrict_of_ae_restrict_of_subset inter_subset_left ht
  have h₂ : ∫⁻ x in M ∩ f ⁻¹' {t} ∩ closure (W i), ‖θ x‖ₑ ∂(μHE[m] : Measure (Eucl P)) =
      ∫⁻ x in M ∩ f ⁻¹' {t}, (closure (W i)).indicator (fun y => ‖θ₀ y‖ₑ) x
        ∂(μHE[m] : Measure (Eucl P)) := by
    rw [lintegral_indicator (hKm i), Measure.restrict_restrict (hKm i),
      inter_comm (closure (W i))]
    exact lintegral_congr_ae (hS.mono fun x hx => congrArg (‖·‖ₑ) hx)
  have hint : IntegrableOn θ (M ∩ f ⁻¹' {t} ∩ closure (W i)) (μHE[m] : Measure (Eucl P)) :=
    ⟨hθ₀.aestronglyMeasurable.congr (hS.mono fun x hx => hx.symm), h₂.trans_lt (hti i)⟩
  exact hint.mono_set (inter_subset_inter_right _ hi)
/-- Null transfer to slices (Simon Ch. 6, §4; Step 1 of the slice triple): under the co-area
identity for `(M, f, G)`, a property holding `H^{m+1}`-a.e. on `M` holds `H^m`-a.e. on
`M ∩ f⁻¹{t}` for `L¹`-a.e. `t`.  Apply the co-area identity to the indicator of a measurable
null hull `Z` of `{¬p}`: the right side vanishes, so `H^m⌞(M ∩ f⁻¹{t})(Z) = 0` for a.e. `t`. -/
theorem Submission.slicing_im_st_ae_transfer :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P),
      (∀ g : Eucl P → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
          (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) =
          ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) →
      ∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x := by
  intro P m M f G hcoarea p hp
  -- A measurable null hull `Z` of the exceptional set `{¬p}` for `H^{m+1}⌞M`.
  set Z := toMeasurable ((μHE[m + 1] : Measure (Eucl P)).restrict M) {x | ¬p x}
  have hZ : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hZ0 : (μHE[m + 1] : Measure (Eucl P)).restrict M Z = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hp
  -- The co-area identity for `g = 1_Z`; its right side vanishes.
  obtain ⟨hmeas, hint⟩ := hcoarea (Z.indicator 1) (measurable_one.indicator hZ)
  have hright : ∫⁻ x in M, ‖G x‖ₑ * Z.indicator 1 x ∂(μHE[m + 1] : Measure (Eucl P)) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ0] with x hx
    simp [hx]
  rw [hright, lintegral_eq_zero_iff' hmeas] at hint
  -- For a.e. `t`, `H^m⌞(M ∩ f⁻¹{t})(Z) = 0`, and `{¬p} ⊆ Z`.
  filter_upwards [hint] with t ht
  rw [Pi.zero_apply, lintegral_indicator_one hZ] at ht
  exact ae_iff.2 (measure_mono_null (subset_toMeasurable _ _) ht)
/-- `v ↦ ι(v)`, `ι(v) α = alternatizeUncurryFin ((innerSL ℝ v).smulRight α) = v♭ ∧ α`, is
`(m + 1)`-Lipschitz from `ℝ^P` to `Λ^m →L Λ^{m+1}` with the operator norm. -/
theorem Submission.slicing_im_st_mf_contraction_lipschitz :
    ∀ (P m : ℕ), LipschitzWith ((m : ℝ≥0) + 1) (fun v : Eucl P =>
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ v))) := by
  intro P m
  let ι : Eucl P → (Covector (Eucl P) m →L[ℝ] Covector (Eucl P) (m + 1)) := fun v =>
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
      (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ v))
  -- Step 1: `ι(v) α = alternatizeUncurryFin ((innerSL ℝ v).smulRight α)` by definition.
  have hform (v : Eucl P) (α : Covector (Eucl P) m) :
      ι v α = ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ v).smulRight α) := rfl
  -- Step 2: `ι(v) - ι(w) = ι(v - w)`, checked at every `α` and `σ = (σ₀, …, σₘ)`.
  have hsub (v w : Eucl P) : ι v - ι w = ι (v - w) := by
    ext α σ
    simp only [_root_.sub_apply, ContinuousAlternatingMap.sub_apply, hform,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousAlternatingMap.smul_apply, innerSL_apply_apply, inner_sub_left, sub_smul,
      smul_sub, Finset.sum_sub_distrib]
  -- Step 3: `‖ι(u)‖ ≤ (m + 1) |u|`.
  have hnorm (u : Eucl P) : ‖ι u‖ ≤ ((m : ℝ) + 1) * ‖u‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
    rw [hform]
    calc ‖ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ u).smulRight α)‖
        ≤ ((m : ℝ) + 1) * ‖(innerSL ℝ u).smulRight α‖ :=
          ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _
      _ = ((m : ℝ) + 1) * ‖u‖ * ‖α‖ := by
          rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_assoc]
  -- Step 4: `dist (ι v) (ι w) = ‖ι (v - w)‖ ≤ (m + 1) dist v w`.
  change LipschitzWith ((m : ℝ≥0) + 1) ι
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [dist_eq_norm, dist_eq_norm, hsub, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  exact hnorm (v - w)

/-- For `L¹`-a.e. `t`, the sliced orientation `x ↦ ξ(x) ∘ ι(|G x|⁻¹ G x)`, where
`ι v = (v♭ ∧ ·) : Λᵐ → Λᵐ⁺¹`, is a.e. strongly measurable for `Hᵐ` on `M ∩ f⁻¹{t}`:
it agrees there with `x ↦ ξ₀(x) ∘ ι(|G x|⁻¹ G x)` for a strongly measurable version `ξ₀` of `ξ`. -/
theorem Submission.slicing_im_st_mf_slice_orientation_aesm :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ)
      (G : Eucl P → Eucl P),
      AEStronglyMeasurable ξ ((μHE[m + 1] : Measure (Eucl P)).restrict M) → Measurable G →
      (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) →
      ∀ᵐ t ∂(volume : Measure ℝ), AEStronglyMeasurable (fun x => (ξ x).comp
        ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
          (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)
            (innerSL ℝ (‖G x‖⁻¹ • G x)))))
        ((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})) := by
  intro P m M ξ f G hξ hG hNT
  -- `x ↦ ι(|G x|⁻¹ G x)` is strongly measurable: `ι` is Lipschitz and `G` is measurable.
  have hν : StronglyMeasurable fun x => ‖G x‖⁻¹ • G x :=
    (hG.norm.inv.smul hG).stronglyMeasurable
  have hιν := (Submission.slicing_im_st_mf_contraction_lipschitz P m).continuous
    |>.comp_stronglyMeasurable hν
  -- With `ξ₀` a strongly measurable version of `ξ`, `F x = ξ₀ x ∘ ι(|G x|⁻¹ G x)` is strongly
  -- measurable, as operator composition is continuous.
  have hF : StronglyMeasurable fun x => (hξ.mk ξ x).comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)
          (innerSL ℝ (‖G x‖⁻¹ • G x)))) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
      (hξ.stronglyMeasurable_mk.prodMk hιν)
  -- Null transfer of `ξ = ξ₀` to the slices; there `F` agrees a.e. with the sliced orientation.
  filter_upwards [hNT (fun x => ξ x = hξ.mk ξ x) hξ.ae_eq_mk] with t ht
  exact hF.aestronglyMeasurable.congr (ht.mono fun x hx => by simp only [hx])

/-- Measure-theoretic fields of the slice triple (Simon Ch. 6, §4; Steps 2, 4, 5 and 6 of the
slice triple): under the co-area identity for `(M, f, G)`, for `L¹`-a.e. `t` the set
`M_t = {x ∈ M : f x = t, G x ≠ 0}` is `H^m`-null-measurable, `θ` is `H^m`-integrable on
`M_t ∩ K` for every compact `K ⊆ U`, and `ξ_t = ξ ∘ ι(|G|⁻¹ G)` is `H^m⌞M_t`-a.e. strongly
measurable.  The null transfer moves the fields of `(M, θ, ξ)` to the whole slice
`M ∩ f⁻¹{t}`, and `M_t = (M ∩ f⁻¹{t}) ∩ G⁻¹{0}ᶜ` inherits them. -/
theorem Submission.slicing_im_st_measure_fields : ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → Measurable f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) → ∀ᵐ t ∂(volume : Measure ℝ), NullMeasurableSet {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} (μHE[m] : Measure (Eucl P)) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ ({x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ∩ K) (μHE[m] : Measure (Eucl P))) ∧ AEStronglyMeasurable (fun x => (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))) ((μHE[m] : Measure (Eucl P)).restrict {x | x ∈ M ∧ f x = t ∧ G x ≠ 0}) := by
  intro P m U M θ ξ f L G hU hT hf hG hGL hcoarea
  -- Null transfer: `H^{m+1}⌞M`-a.e. properties hold `H^m⌞(M ∩ f⁻¹{t})`-a.e. for a.e. `t`.
  have hNT := Submission.slicing_im_st_ae_transfer P m M f G hcoarea
  -- The three fields on the whole slice `M ∩ f⁻¹{t}`, each for a.e. `t`.
  have hnull := Submission.slicing_im_st_mf_slice_null_measurable P m M f hT.nullMeasurableSet
    hf hNT
  have hint := Submission.slicing_im_st_mf_slice_integrable P m U M θ f L G hU hT.subset
    hT.integrableOn hGL hcoarea hNT
  have haesm := Submission.slicing_im_st_mf_slice_orientation_aesm P m M ξ f G
    hT.aestronglyMeasurable hG hNT
  filter_upwards [hnull, hint, haesm] with t hnull_t hint_t haesm_t
  -- `M_t = (M ∩ f⁻¹{t}) ∩ G⁻¹{0}ᶜ`, a subset of the slice.
  have hMt : {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} = M ∩ f ⁻¹' {t} ∩ G ⁻¹' {0}ᶜ :=
    Set.ext fun _ => and_assoc.symm
  have hsub : {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ⊆ M ∩ f ⁻¹' {t} := fun x hx => ⟨hx.1, hx.2.1⟩
  refine ⟨?_, fun K hK hKU => (hint_t K hK hKU).mono_set (inter_subset_inter_left K hsub),
    haesm_t.mono_set hsub⟩
  rw [hMt]
  exact hnull_t.inter (hG (measurableSet_singleton 0).compl).nullMeasurableSet

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
