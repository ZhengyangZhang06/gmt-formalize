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

/-- Horizontal slices for the product `[[0,1]] × X`: for `ψ ∈ 𝒟^q(ℝ^{m+1})` and `s ∈ ℝ`, the
pull-backs `j_s^# ψ` and `j_s^# ∂_s ψ` along `j_s(x) = (s, x)`, i.e. `x ↦ ψ(s, x)(ι ·)` and
`x ↦ Dψ(s, x)(e₀)(ι ·)` with `ι v = (0, v)`, are test forms in `𝒟^q(ℝ^m)`. -/
theorem Submission.dph_iprod_horizontal_slices :
    ∀ (m q : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) q),
      ∃ Ψ Ψ' : ℝ → TestFormOn (univ : Set (Eucl m)) q,
        (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m),
          (Ψ s : DifferentialForm (Eucl m) q) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) q)
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
        ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m),
          (Ψ' s : DifferentialForm (Eucl m) q) x v =
            fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q)
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (EuclideanSpace.single 0 1)
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
  have hCF := Submission.iwl_sp_exists_compatible_testForm
  intro m q ψ
  -- 1. `ι v = (0, v)` is a continuous linear map `ℝ^m → ℝ^{m+1}`.
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    { toFun := fun w => Fin.cons 0 w
      map_add' := by
        intro a b; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro c a; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let ι : Eucl m →L[ℝ] Eucl (m + 1) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
      LinearMap.toContinuousLinearMap L ∘L (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap
  have hιv : ∀ v : Eucl m, ι v = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)) :=
    fun v => rfl
  -- 2. `j_s(x) = (s, 0) + ι x` is affine, so smooth with derivative `ι`.
  have hj : ∀ s : ℝ, (fun x : Eucl m =>
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) =
      fun x => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s 0) + ι x := by
    intro s
    funext x
    rw [hιv]
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- 3. `‖x‖ ≤ ‖j_s(x)‖`, so `j_s` is proper.
  have hnorm : ∀ (s : ℝ) (x : Eucl m), ‖x‖ ≤ ‖(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))‖ := by
    intro s x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    apply Real.sqrt_le_sqrt
    simp
    positivity
  -- 4. Slices of any test form, by the cut-off pull-back along `j_s` (proper on `A = univ`).
  have hslice : ∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) q) (s : ℝ),
      ∃ η : TestFormOn (univ : Set (Eucl m)) q, ∀ (x : Eucl m) (v : Fin q → Eucl m),
        (η : DifferentialForm (Eucl m) q) x v = (ω : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => ι (v i)) := by
    intro ω s
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl m =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) := by
      rw [hj s]
      exact contDiff_const.add ι.contDiff
    have hfd : ∀ x, fderiv ℝ (fun x : Eucl m =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) x = ι := by
      intro x
      rw [hj s]
      exact ((ι.hasFDerivAt).const_add _).fderiv
    have hpr : ∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ univ →
        IsCompact ((fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ⁻¹' K ∩ univ) := by
      intro K hK _
      rw [inter_univ]
      apply Metric.isCompact_of_isClosed_isBounded
      · exact hK.isClosed.preimage hsm.continuous
      · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
        refine (Metric.isBounded_closedBall (x := (0 : Eucl m)) (r := R)).subset ?_
        intro x hx
        have := hR hx
        rw [mem_closedBall, dist_zero_right] at this ⊢
        exact (hnorm s x).trans this
    obtain ⟨η, ζ, N, -, hAN, -, -, hη2, -⟩ := hCF m (m + 1) q univ univ univ _ isOpen_univ
      (subset_univ _) hsm hpr ω
    refine ⟨η, fun x v => ?_⟩
    rw [hη2 x (hAN (mem_univ x)), hfd x]
    rfl
  -- 5. `ψ' = Dψ(·)(e₀)` is a test form.
  have hψ' : ∃ ψ' : TestFormOn (univ : Set (Eucl (m + 1))) q, ∀ y,
      (ψ' : DifferentialForm (Eucl (m + 1)) q) y =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y (EuclideanSpace.single 0 1) := by
    refine ⟨⟨fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y
        (EuclideanSpace.single 0 1), ⟨⟨?_, ?_⟩, subset_univ _⟩⟩, fun y => rfl⟩
    · exact (ψ.property.1.1.fderiv_right (by simp)).clm_apply contDiff_const
    · exact (ψ.property.1.2.fderiv ℝ).comp_left (g := fun L => L (EuclideanSpace.single 0 1)) rfl
  -- 6. Choose the slices of `ψ` and `ψ'` for every `s`.
  obtain ⟨ψ', hψ'⟩ := hψ'
  choose Ψ hΨ using fun s => hslice ψ s
  choose Ψ' hΨ' using fun s => hslice ψ' s
  refine ⟨Ψ, Ψ', fun s x v => ?_, fun s x v => ?_⟩
  · rw [hΨ s x v]
    rfl
  · rw [hΨ' s x v, hψ']
    rfl
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
/-- Euclidean coefficient norms `|γ| = covectorEuclideanNorm γ` of slices of covectors, with
`ι(v) = (0, v) ∈ ℝ^{m+1}` and `e₀ = EuclideanSpace.single 0 1`: (C1) if `γ'(v) = γ(e₀, ι ∘ v)`
then `|γ'| ≤ |γ|`; (C2) if `γ'(v) = γ(ι ∘ v)` then `|γ'| ≤ |γ|`; (C3) `|α| ≤ √(P^n) · ‖α‖`.
For (C1) and (C2), `e₀ = b_0` and `ι(b_j) = b_{j+1}` for the standard bases `b`, so the
coefficients of `γ'` are coefficients of `γ` on distinct strictly increasing multi-indices; for
(C3), each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` is at most
`‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.dph_iprod_slice_covector_norm_le :
    (∀ (m k : ℕ) (γ : Covector (Eucl (m + 1)) (k + 1)) (γ' : Covector (Eucl m) k),
      (∀ v : Fin k → Eucl m, γ' v = γ (Fin.cons (EuclideanSpace.single 0 1) fun i =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      covectorEuclideanNorm γ' ≤ covectorEuclideanNorm γ) ∧
    (∀ (m q : ℕ) (γ : Covector (Eucl (m + 1)) q) (γ' : Covector (Eucl m) q),
      (∀ v : Fin q → Eucl m, γ' v = γ (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      covectorEuclideanNorm γ' ≤ covectorEuclideanNorm γ) ∧
    (∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖) := by
  -- `e₀` is the first standard basis vector of `ℝ^{m+1}`.
  have hb0 : ∀ m : ℕ, (EuclideanSpace.single 0 1 : Eucl (m + 1)) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0 := by
    intro m; simp [EuclideanSpace.basisFun_apply]
  -- `ι` maps the `j`-th standard basis vector of `ℝ^m` to the `(j+1)`-st one of `ℝ^{m+1}`.
  have hbι : ∀ (m : ℕ) (j : Fin m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (EuclideanSpace.basisFun (Fin m) ℝ j))) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ j.succ := by
    intro m j
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [EuclideanSpace.basisFun_apply]
  -- A sum dominated termwise, along an injection, by nonnegative terms is at most the full sum.
  have key : ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (g : A → B),
      Function.Injective g → ∀ (F : B → ℝ) (G : A → ℝ), (∀ b, 0 ≤ F b) →
      (∀ a, G a ≤ F (g a)) → ∑ a, G a ≤ ∑ b, F b := by
    intro A B _ _ _ g hg F G hF hG
    calc ∑ a, G a ≤ ∑ a, F (g a) := Finset.sum_le_sum (fun a _ => hG a)
      _ = ∑ b ∈ Finset.univ.image g, F b := (Finset.sum_image (fun a _ b _ h => hg h)).symm
      _ ≤ ∑ b, F b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hF b)
  refine ⟨?_, ?_, ?_⟩
  · -- (C1): compare along `I ↦ (0, I + 1)`.
    intro m k γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin k → Fin m =>
      (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i.succ
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)) := by
          intro a b hab
          induction a using Fin.cases with
          | zero =>
            induction b using Fin.cases with
            | zero => exact absurd hab (lt_irrefl _)
            | succ j => simp [Fin.succ_pos]
          | succ i =>
            induction b using Fin.cases with
            | zero => exact absurd hab (Fin.not_lt_zero _)
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_lt_succ_iff] at hab ⊢
              exact h1 hab
        rw [ite_eq_left h1, ite_eq_left h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.cons_zero]
          exact hb0 m
        · simp only [Fin.cons_succ]
          exact hbι m (I i)
      · rw [ite_eq_right h1]
        split_ifs <;> positivity
  · -- (C2): compare along `I ↦ I + 1`.
    intro m q γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin q → Fin m => (fun i => (I i).succ : Fin q → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (fun i => (I i).succ : Fin q → Fin (m + 1)) :=
          fun a b hab => Fin.succ_lt_succ_iff.mpr (h1 hab)
        rw [ite_eq_left h1, ite_eq_left h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        exact hbι m (I i)
      · rw [ite_eq_right h1]
        split_ifs <;> positivity
  · -- (C3): every coefficient is at most `‖α‖`, and there are `P ^ n` of them.
    intro P n α
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

/-- **Continuity along slices** (step 3 of the interval product).  Let `X` be a current in `ℝ^m`
with `M(X) < ∞`; write `(s, x) ∈ ℝ^{m+1}` for `Fin.cons s x`, `ι(w) = (0, w)`, `e₀ = (1, 0)`.
(D1) If `X ∈ 𝒟_k`, `η ∈ 𝒟^{k+1}(ℝ^{m+1})` and `φ(s)(x)(v) = η(s, x)(e₀, ι ∘ v)` for
`s ∈ [0, 1]`, then `s ↦ X(φ(s))` is continuous on `[0, 1]` and `|X(φ(s))| ≤ M(X) · sup |η|`.
(D2) If `X ∈ 𝒟_q`, `ω` is a continuous compactly supported `q`-form on `ℝ^{m+1}` and
`Ψ(s)(x)(v) = ω(s, x)(ι ∘ v)` for all `s`, then `s ↦ X(Ψ(s))` is continuous and
`|X(Ψ(s))| ≤ M(X) · sup |ω|`.  By the mass bound, `X` is `M(X)`-Lipschitz for the sup of the
Euclidean covector norm; slices are bounded by the sliced covector
(`dph_iprod_slice_covector_norm_le`), and `η`, `ω` are uniformly continuous. -/
theorem Submission.dph_iprod_slice_continuity : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → ContinuousOn (fun s => X (φ s)) (Icc (0 : ℝ) 1) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((η : DifferentialForm (Eucl (m + 1)) (k + 1)) y) ≤ C) → ∀ s ∈ Icc (0 : ℝ) 1, |X (φ s)| ≤ X.mass.toReal * C) ∧ (∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ → ∀ (ω : DifferentialForm (Eucl (m + 1)) q) (Ψ : ℝ → TestFormOn (univ : Set (Eucl m)) q), Continuous ω → HasCompactSupport ω → (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v = ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Continuous (fun s => X (Ψ s)) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm (ω y) ≤ C) → ∀ s : ℝ, |X (Ψ s)| ≤ X.mass.toReal * C) := by
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  -- (MB) If `|ω(x)| ≤ C` for all `x`, then `|X(ω)| ≤ M(X) · C` (mass bound with `U = W = univ`).
  have hMB : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ →
      ∀ (ω : TestFormOn (univ : Set (Eucl m)) q) (C : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m) q) x) ≤ C) →
          |X ω| ≤ X.mass.toReal * C := by
    intro m q X hX ω C hC
    refine Submission.cmb_abs_apply_le_of_massOn_le m q univ univ X ω X.mass.toReal C
      ENNReal.toReal_nonneg ?_ (subset_univ _) hC
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  -- If `F(s) - F(s₀)` is uniformly small for close `s, s₀ ∈ S`, then `s ↦ X(F(s))` is
  -- continuous on `S`, by (MB) and linearity of `X`.
  have hcont : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ →
      ∀ (F : ℝ → TestFormOn (univ : Set (Eucl m)) q) (S : Set ℝ),
        (∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, ∀ s₀ ∈ S, |s - s₀| < δ → ∀ x,
          covectorEuclideanNorm (((F s - F s₀ : TestFormOn (univ : Set (Eucl m)) q) :
            DifferentialForm (Eucl m) q) x) ≤ ε) →
        ContinuousOn (fun s => X (F s)) S := by
    intro m q X hX F S hF s₀ hs₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hB : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hB1 : 0 < X.mass.toReal + 1 := by linarith
    obtain ⟨δ, hδ, hFδ⟩ := hF (ε / (X.mass.toReal + 1)) (div_pos hε hB1)
    refine ⟨δ, hδ, fun {s} hs hss₀ => ?_⟩
    rw [Real.dist_eq] at hss₀ ⊢
    have hsub : X (F s - F s₀) = X (F s) - X (F s₀) := map_sub X.toCurrent _ _
    rw [← hsub]
    calc |X (F s - F s₀)| ≤ X.mass.toReal * (ε / (X.mass.toReal + 1)) :=
          hMB m q X hX _ _ (hFδ s hs s₀ hs₀ hss₀)
      _ < (X.mass.toReal + 1) * (ε / (X.mass.toReal + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) (div_pos hε hB1)
      _ = ε := by field_simp
  -- `dist ((s, x), (s₀, x)) = |s - s₀|`: only the `0`-th coordinates differ.
  have hdist : ∀ (m : ℕ) (s s₀ : ℝ) (x : Eucl m),
      dist ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))) = |s - s₀| := by
    intro m s s₀ x
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_succ]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hfrac : ∀ c ε : ℝ, 0 ≤ c → 0 < ε → c * (ε / (c + 1)) ≤ ε := by
    intro c ε hc hε
    have hc1 : 0 < c + 1 := by linarith
    calc c * (ε / (c + 1)) ≤ (c + 1) * (ε / (c + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_pos hε hc1).le
      _ = ε := by field_simp
  refine ⟨?_, ?_⟩
  · -- (D1) `dt`-slices of `η`: (C1) and (C3).
    intro m k X hX η φ hφ
    have hC1 := hSN.1 m k
    have hC3 := hSN.2.2 (m + 1) (k + 1)
    have hc0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ (k + 1)) := Real.sqrt_nonneg _
    have huc : UniformContinuous (η : DifferentialForm (Eucl (m + 1)) (k + 1)) :=
      η.property.1.2.uniformContinuous_of_continuous η.property.1.1.continuous
    refine ⟨hcont m k X hX φ (Icc 0 1) fun ε hε => ?_, fun C hC s hs =>
      hMB m k X hX (φ s) C fun x => (hC1 _ _ fun v => hφ s hs x v).trans (hC _)⟩
    obtain ⟨δ, hδ, hηδ⟩ := Metric.uniformContinuous_iff.mp huc
      (ε / (Real.sqrt (((m + 1 : ℕ) : ℝ) ^ (k + 1)) + 1)) (by positivity)
    refine ⟨δ, hδ, fun s hs s₀ hs₀ hss₀ x => ?_⟩
    -- `(φ s - φ s₀)(x)` is the `dt`-slice of `η(s, x) - η(s₀, x)`.
    have h1 := hC1 ((η : DifferentialForm (Eucl (m + 1)) (k + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
      (η : DifferentialForm (Eucl (m + 1)) (k + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
      (((φ s - φ s₀ : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x) (by
        intro v
        show ((φ s : DifferentialForm (Eucl m) k) - (φ s₀ : DifferentialForm (Eucl m) k)) x v = _
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hφ s hs x v, hφ s₀ hs₀ x v]
        rfl)
    refine h1.trans ((hC3 _).trans ((mul_le_mul_of_nonneg_left ?_ hc0).trans (hfrac _ ε hc0 hε)))
    rw [← dist_eq_norm]
    exact (hηδ (by rwa [hdist])).le
  · -- (D2) horizontal slices of `ω`: (C2) and (C3).
    intro m q X hX ω Ψ hωc hωs hΨ
    have hC2 := hSN.2.1 m q
    have hC3 := hSN.2.2 (m + 1) q
    have hc0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ q) := Real.sqrt_nonneg _
    have huc : UniformContinuous ω := hωs.uniformContinuous_of_continuous hωc
    refine ⟨continuousOn_univ.mp (hcont m q X hX Ψ univ fun ε hε => ?_), fun C hC s =>
      hMB m q X hX (Ψ s) C fun x => (hC2 _ _ fun v => hΨ s x v).trans (hC _)⟩
    obtain ⟨δ, hδ, hωδ⟩ := Metric.uniformContinuous_iff.mp huc
      (ε / (Real.sqrt (((m + 1 : ℕ) : ℝ) ^ q) + 1)) (by positivity)
    refine ⟨δ, hδ, fun s _ s₀ _ hss₀ x => ?_⟩
    -- `(Ψ s - Ψ s₀)(x)` is the horizontal slice of `ω(s, x) - ω(s₀, x)`.
    have h1 := hC2
      (ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
        ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
      (((Ψ s - Ψ s₀ : TestFormOn (univ : Set (Eucl m)) q) : DifferentialForm (Eucl m) q) x) (by
        intro v
        show ((Ψ s : DifferentialForm (Eucl m) q) - (Ψ s₀ : DifferentialForm (Eucl m) q)) x v = _
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hΨ s x v, hΨ s₀ x v]
        rfl)
    refine h1.trans ((hC3 _).trans ((mul_le_mul_of_nonneg_left ?_ hc0).trans (hfrac _ ε hc0 hε)))
    rw [← dist_eq_norm]
    exact (hωδ (by rwa [hdist])).le
/-- The `dt`-slice of `dψ` (`e₀ = EuclideanSpace.single 0 1`, `ι(w) = (0, w)`, `(s, x)` the point
of `ℝ^{m+1}` with first coordinate `s`): for a `0`-form `ψ`, `dψ(y)(e₀) = Dψ(y)(e₀)`; for a
`(j+1)`-form `ψ` whose slice at `s` is `φ(x)(w) = ψ(s, x)(e₀, ι ∘ w)`,
`dψ(s, x)(e₀, ι ∘ v) = Dψ(s, x)(e₀)(ι ∘ v) − dφ(x)(v)`.
Both exterior derivatives are alternating sums of directional derivatives; by the chain rule
along `x ↦ (s, x)` (derivative `ι`), the `l`-th term of `dφ(x)(v)` is the `(l+1)`-st term of
`dψ(s, x)(e₀, ι ∘ v)` with the opposite sign, and the `0`-th term is `Dψ(s, x)(e₀)(ι ∘ v)`. -/
theorem Submission.dph_iprod_slice_extDeriv :
    (∀ (m : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0) (y : Eucl (m + 1))
      (v : Fin 0 → Eucl m),
      ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) 0 ψ :
        TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) : DifferentialForm (Eucl (m + 1)) (0 + 1))
        y (Fin.cons (EuclideanSpace.single 0 1) fun i =>
          (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) =
      fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) 0) y (EuclideanSpace.single 0 1)
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
    (∀ (m j : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1))
      (φ : TestFormOn (univ : Set (Eucl m)) j) (s : ℝ),
      (∀ (x : Eucl m) (w : Fin j → Eucl m), (φ : DifferentialForm (Eucl m) j) x w =
        (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (Fin.cons (EuclideanSpace.single 0 1) fun i =>
            (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (w i))))) →
      ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
        ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) (j + 1) ψ :
          TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) :
            DifferentialForm (Eucl (m + 1)) (j + 1 + 1))
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (Fin.cons (EuclideanSpace.single 0 1) fun i =>
            (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (EuclideanSpace.single 0 1)
          (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) -
        ((exteriorDerivativeTestOn (univ : Set (Eucl m)) j φ :
          TestFormOn (univ : Set (Eucl m)) (j + 1)) : DifferentialForm (Eucl m) (j + 1)) x v) := by
  refine ⟨?_, ?_⟩
  · -- `dψ(y)(e₀)` is the one-term alternating sum `Dψ(y)(e₀)`.
    intro m ψ y v
    have hd : DifferentiableAt ℝ (ψ : DifferentialForm (Eucl (m + 1)) 0) y :=
      ψ.property.1.1.differentiable (by simp) y
    show exteriorDerivative (ψ : DifferentialForm (Eucl (m + 1)) 0) y _ = _
    rw [exteriorDerivative_apply hd, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
    rw [fderiv_continuousAlternatingMap_apply_const_apply hd]
    congr 1
  · intro m j ψ φ s hφ x v
    -- `ι(w) = (0, w)` is a continuous linear map `ℝ^m → ℝ^{m+1}`.
    obtain ⟨ι, hιv⟩ : ∃ ι : Eucl m →L[ℝ] Eucl (m + 1), ∀ w : Eucl m,
        ι w = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ w)) := by
      let L : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
        { toFun := fun w => Fin.cons 0 w
          map_add' := by
            intro a b; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
          map_smul' := by
            intro c a; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
      exact ⟨(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
        LinearMap.toContinuousLinearMap L ∘L
          (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap, fun w => rfl⟩
    -- The slice `x ↦ (s, x) = (s, 0) + ι x` has derivative `ι`.
    have hslice : HasFDerivAt (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ι x := by
      have heq : (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) =
          fun x => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s 0) + ι x := by
        funext x
        rw [hιv]
        apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
        simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [heq]
      exact ι.hasFDerivAt.const_add _
    have hd : DifferentiableAt ℝ (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) :=
      ψ.property.1.1.differentiable (by simp) _
    have hdφ : DifferentiableAt ℝ (φ : DifferentialForm (Eucl m) j) x :=
      φ.property.1.1.differentiable (by simp) x
    -- Chain rule: `D(φ(·)(w))(x) = D(ψ(·)(e₀, ι ∘ w))(s, x) ∘ ι`.
    have hchain : ∀ w : Fin j → Eucl m,
        fderiv ℝ (fun x' => (φ : DifferentialForm (Eucl m) j) x' w) x =
          (fderiv ℝ (fun z => (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) z
            (Fin.cons (EuclideanSpace.single 0 1) fun i => ι (w i)))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))).comp ι := by
      intro w
      have hfun : (fun x' => (φ : DifferentialForm (Eucl m) j) x' w) =
          (fun z => (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) z
            (Fin.cons (EuclideanSpace.single 0 1) fun i => ι (w i))) ∘
          (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) := by
        funext x'
        simp only [Function.comp_apply, hφ x' w, hιv]
      rw [hfun]
      exact ((hd.continuousAlternatingMap_apply_const _).hasFDerivAt.comp x hslice).fderiv
    show exteriorDerivative (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) _ _ =
      _ - exteriorDerivative (φ : DifferentialForm (Eucl m) j) x v
    -- Split off the `0`-th term of `dψ`; the remaining terms are those of `-dφ`.
    rw [exteriorDerivative_apply hd, exteriorDerivative_apply hdφ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero,
      Fin.tail_cons]
    rw [fderiv_continuousAlternatingMap_apply_const_apply hd, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hchain, ContinuousLinearMap.comp_apply,
      fderiv_continuousAlternatingMap_apply_const_apply hd,
      fderiv_continuousAlternatingMap_apply_const_apply hd]
    -- Removing the `(l+1)`-st entry of `(e₀, ι ∘ v)` gives `(e₀, ι ∘ removeNth l v)`.
    have hrm : Fin.removeNth l.succ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (m + 1))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) :
            Fin (j + 1 + 1) → Eucl (m + 1)) =
        (Fin.cons (EuclideanSpace.single 0 1 : Eucl (m + 1)) (fun i => ι (Fin.removeNth l v i)) :
          Fin (j + 1) → Eucl (m + 1)) := by
      show (Fin.cons (EuclideanSpace.single 0 1 : Eucl (m + 1))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) :
            Fin (j + 1 + 1) → Eucl (m + 1)) ∘ (l.succ).succAbove = _
      rw [Fin.cons_comp_succ_succAbove]
      congr 1
      funext i
      simp only [Fin.removeNth, hιv]
    rw [hrm, Fin.cons_succ, hιv, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]

/-- Fundamental theorem of calculus along horizontal slices: for `M(X) < ∞`, the slices
`Ψ(s) = ψ(s, ·)` and `Ψ'(s) = ∂ₛψ(s, ·)` of `ψ ∈ 𝒟^q(ℝ^{m+1})` (tested on horizontal vectors)
satisfy `d/ds X(Ψ(s)) = X(Ψ'(s))`, with `s ↦ X(Ψ'(s))` continuous and
`∫₀¹ X(Ψ'(s)) ds = X(Ψ(1)) - X(Ψ(0))`. -/
theorem Submission.dph_iprod_horizontal_ftc :
    ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q)
      (ψ : TestFormOn (univ : Set (Eucl (m + 1))) q) (Ψ Ψ' : ℝ → TestFormOn (univ : Set (Eucl m)) q),
      X.mass < ∞ →
      (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v =
        (ψ : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (EuclideanSpace.single 0 1)
          (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      Continuous (fun s => X (Ψ' s)) ∧ (∀ s : ℝ, HasDerivAt (fun t => X (Ψ t)) (X (Ψ' s)) s) ∧
        ∫ s in (0 : ℝ)..1, X (Ψ' s) = X (Ψ 1) - X (Ψ 0) := by
  have hMB := Submission.cmb_abs_apply_le_of_massOn_le
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  have hC := Submission.dph_iprod_slice_continuity
  intro m q X ψ Ψ Ψ' hX hΨ hΨ'
  -- Mass estimate `|X(ω)| ≤ M(X) · sup |ω|`, from `M(X) < ∞`.
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  have hmb : X.massOn univ ≤ ENNReal.ofReal X.mass.toReal := by
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  -- Restriction to horizontal vectors and comparison with the operator norm.
  have hC2 := hSN.2.1 m q
  have hC3 := hSN.2.2 (m + 1) q
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt ((((m + 1 : ℕ)) : ℝ) ^ q) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Real.sqrt_nonneg _
  -- The form `ψ' = Dψ(·)(e₀)` is continuous with compact support.
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Eucl (m + 1), e₀ = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'eq⟩ : ∃ ψ' : Eucl (m + 1) → Covector (Eucl (m + 1)) q,
      ψ' = fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y e₀ := ⟨_, rfl⟩
  have hψd : Differentiable ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) :=
    ψ.property.1.1.differentiable (by simp)
  have hψ'c : Continuous ψ' := by
    rw [hψ'eq]
    exact (ψ.property.1.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ's : HasCompactSupport ψ' := by
    rw [hψ'eq]
    exact (ψ.property.1.2.fderiv ℝ).comp_left
      (g := fun L : Eucl (m + 1) →L[ℝ] Covector (Eucl (m + 1)) q => L e₀) rfl
  have hΨ'2 : ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v =
      ψ' ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
    intro s x v
    rw [hΨ' s x v, hψ'eq, he₀]
  -- Continuity of `s ↦ X(Ψ'(s))`.
  have hcont := (hC.2 m q X hX ψ' Ψ' hψ'c hψ's hΨ'2).1
  -- Lines in the time direction: `cons(s + τ, x) = cons(s, x) + τ e₀`.
  have hpath : ∀ (s τ : ℝ) (x : Eucl m),
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons (s + τ) (EuclideanSpace.equiv (Fin m) ℝ x)) =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) +
        τ • e₀ := by
    intro s τ x
    rw [he₀]
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- Differentiability: `|X(Ψ(s+h)) - X(Ψ(s)) - h X(Ψ'(s))| ≤ ε |h|` for small `h`, by the mean
  -- value inequality and the uniform continuity of `ψ'`.
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t => X (Ψ t)) (X (Ψ' s)) s := by
    intro s
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have huc := hψ's.uniformContinuous_of_continuous hψ'c
    obtain ⟨ε', hε', hε'ε⟩ : ∃ ε' > 0, X.mass.toReal * c * ε' ≤ ε := by
      refine ⟨ε / (X.mass.toReal * c + 1), by positivity, ?_⟩
      have hpos : 0 < X.mass.toReal * c + 1 := by positivity
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith [mul_nonneg hB0 hc0]
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc ε' hε'
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    obtain ⟨Θ, hΘdef⟩ : ∃ Θ : TestFormOn (univ : Set (Eucl m)) q, Θ = Ψ (s + h) - Ψ s - h • Ψ' s :=
      ⟨_, rfl⟩
    have hΘx : ∀ (x : Eucl m) (v : Fin q → Eucl m), (Θ : DifferentialForm (Eucl m) q) x v =
        (Ψ (s + h) : DifferentialForm (Eucl m) q) x v - (Ψ s : DifferentialForm (Eucl m) q) x v -
          h * (Ψ' s : DifferentialForm (Eucl m) q) x v := by
      intro x v
      rw [hΘdef]
      rfl
    have hΘ : ∀ x, covectorEuclideanNorm ((Θ : DifferentialForm (Eucl m) q) x) ≤ c * (ε' * |h|) := by
      intro x
      obtain ⟨y, hy⟩ : ∃ y : Eucl (m + 1),
          y = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) :=
        ⟨_, rfl⟩
      obtain ⟨f, hfdef⟩ : ∃ f : ℝ → Covector (Eucl (m + 1)) q,
          f = fun τ => (ψ : DifferentialForm (Eucl (m + 1)) q) (y + τ • e₀) - τ • ψ' y := ⟨_, rfl⟩
      have hf : ∀ τ ∈ Set.uIcc (0 : ℝ) h,
          HasDerivWithinAt f (ψ' (y + τ • e₀) - ψ' y) (Set.uIcc (0 : ℝ) h) τ := by
        intro τ _
        have h1 : HasDerivAt (fun τ : ℝ => y + τ • e₀) e₀ τ := by
          simpa using ((hasDerivAt_id τ).smul_const e₀).const_add y
        have h2 : HasDerivAt (fun τ : ℝ => (ψ : DifferentialForm (Eucl (m + 1)) q) (y + τ • e₀))
            (ψ' (y + τ • e₀)) τ := by
          rw [hψ'eq]
          exact (hψd _).hasFDerivAt.comp_hasDerivAt τ h1
        have h3 : HasDerivAt (fun τ : ℝ => τ • ψ' y) (ψ' y) τ := by
          simpa using (hasDerivAt_id τ).smul_const (ψ' y)
        rw [hfdef]
        exact (h2.sub h3).hasDerivWithinAt
      have hbound : ∀ τ ∈ Set.uIcc (0 : ℝ) h, ‖ψ' (y + τ • e₀) - ψ' y‖ ≤ ε' := by
        intro τ hτ
        rw [← dist_eq_norm]
        apply le_of_lt
        apply hδ'
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he₀, PiLp.norm_single, norm_one, mul_one,
          Real.norm_eq_abs]
        have : |τ| ≤ |h| := by
          rcases le_total 0 h with h0 | h0
          · rw [Set.uIcc_of_le h0] at hτ
            rw [abs_of_nonneg hτ.1, abs_of_nonneg h0]; exact hτ.2
          · rw [Set.uIcc_of_ge h0] at hτ
            rw [abs_of_nonpos hτ.2, abs_of_nonpos h0]; linarith [hτ.1]
        exact lt_of_le_of_lt this hh
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound (convex_uIcc 0 h)
        Set.left_mem_uIcc Set.right_mem_uIcc
      rw [sub_zero, Real.norm_eq_abs] at hmv
      have hγ : ∀ v : Fin q → Eucl m, (f h - f 0) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) = (Θ : DifferentialForm (Eucl m) q) x v := by
        intro v
        rw [hΘx, hΨ, hΨ, hΨ'2, hfdef, hpath, ← hy]
        simp only [zero_smul, add_zero, ContinuousAlternatingMap.sub_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
        ring
      have h4 := hC2 (f h - f 0) ((Θ : DifferentialForm (Eucl m) q) x) (fun v => (hγ v).symm)
      refine h4.trans ((hC3 _).trans ?_)
      rw [← hc]
      exact mul_le_mul_of_nonneg_left hmv hc0
    have h5 := hMB m q univ univ X Θ X.mass.toReal (c * (ε' * |h|)) hB0 hmb (subset_univ _) hΘ
    have hlin : X Θ = X (Ψ (s + h)) - X (Ψ s) - h • X (Ψ' s) := by
      rw [hΘdef]
      have e1 := map_sub X.toCurrent (Ψ (s + h) - Ψ s) (h • Ψ' s)
      have e2 := map_sub X.toCurrent (Ψ (s + h)) (Ψ s)
      have e3 := map_smul X.toCurrent h (Ψ' s)
      exact e1.trans (by rw [e2, e3])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hlin]
    calc |X Θ| ≤ X.mass.toReal * (c * (ε' * |h|)) := h5
      _ = (X.mass.toReal * c * ε') * |h| := by ring
      _ ≤ ε * |h| := mul_le_mul_of_nonneg_right hε'ε (abs_nonneg h)
  -- Fundamental theorem of calculus.
  refine ⟨hcont, hderiv, ?_⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcont.intervalIntegrable 0 1)
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

/-- Boundary of a current `Z` with the product characterization `ProdChar(X, Z)` of
`[[0,1]] × X`: `Z(η) = ∫₀¹ X(φ(s)) ds` whenever `φ(s)(x)(v) = η((s, x))(e₀, ι ∘ v)` on `[0,1]`.
With `ψᵢ(x)(v) = ψ((i, x))(ι ∘ v)` and `φ(s)(x)(v) = ψ((s, x))(e₀, ι ∘ v)`:
(II) `∂Z(ψ) = X(ψ₁) − X(ψ₀)` in degree `0`; (III) `∂Z(ψ) = X(ψ₁) − X(ψ₀) − ∫₀¹ ∂X(φ(s)) ds` in
positive degree; (N) `M(∂Z) ≤ 2 M(X) + M(∂X) < ∞` (no `M(∂X)` term in degree `0`). -/
theorem Submission.dph_iprod_boundary :
    (∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0)
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)), X.mass < ∞ →
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m),
              (φ s : DifferentialForm (Eucl m) 0) x v =
                (η : DifferentialForm (Eucl (m + 1)) (0 + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
        ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0)
          (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) 0),
          (∀ (x : Eucl m) (v : Fin 0 → Eucl m),
            (ψ₀ : DifferentialForm (Eucl m) 0) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) 0)
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          (∀ (x : Eucl m) (v : Fin 0 → Eucl m),
            (ψ₁ : DifferentialForm (Eucl m) 0) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) 0)
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          Z.boundary ψ = X ψ₁ - X ψ₀) ∧
    (∀ (m j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1))
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)), X.mass < ∞ →
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
              (φ s : DifferentialForm (Eucl m) (j + 1)) x v =
                (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
        ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1))
          (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) (j + 1))
          (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j),
          (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
            (ψ₀ : DifferentialForm (Eucl m) (j + 1)) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
            (ψ₁ : DifferentialForm (Eucl m) (j + 1)) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m),
            (φ s : DifferentialForm (Eucl m) j) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          Z.boundary ψ = X ψ₁ - X ψ₀ - ∫ s in (0 : ℝ)..1, X.boundary (φ s)) ∧
    (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k)
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)), X.mass < ∞ →
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
              (φ s : DifferentialForm (Eucl m) k) x v =
                (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
        ((∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 →
            HEq Y X → Y.boundary.mass < ∞) →
          Z.boundary.mass < ∞)) := by
  have hSF := Submission.iwl_cr_ci_slice_testForm
  have hHS := Submission.dph_iprod_horizontal_slices
  have hC := Submission.dph_iprod_slice_continuity
  have hD := Submission.dph_iprod_slice_extDeriv
  have hF := Submission.dph_iprod_horizontal_ftc
  -- (N) uses (II) and (III): prove the conjunction in the form `A`, `B`, `A → B → C`.
  have key : ∀ {A B C : Prop}, A → B → (A → B → C) → A ∧ B ∧ C :=
    fun a b h => ⟨a, b, h a b⟩
  refine key ?_ ?_ ?_
  · -- (II): the `e₀`-derivative slices `Ψ'` are `dt`-slices of `dψ`, so
    -- `∂Z(ψ) = Z(dψ) = ∫₀¹ X(Ψ'(s)) ds = X(Ψ(1)) − X(Ψ(0))`.
    intro m X Z hX hZ ψ ψ₀ ψ₁ h₀ h₁
    obtain ⟨Ψ, Ψ', hΨ, hΨ'⟩ := hHS m 0 ψ
    have hftc := hF m 0 X ψ Ψ Ψ' hX hΨ hΨ'
    have hslice : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m),
        (Ψ' s : DifferentialForm (Eucl m) 0) x v =
          ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) 0 ψ :
              TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) :
            DifferentialForm (Eucl (m + 1)) (0 + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
      intro s _ x v
      rw [hΨ' s x v, hD.1 m ψ _ v]
    have e0 : ψ₀ = Ψ 0 := by
      apply Subtype.ext; funext x; ext v; rw [h₀ x v, hΨ 0 x v]
    have e1 : ψ₁ = Ψ 1 := by
      apply Subtype.ext; funext x; ext v; rw [h₁ x v, hΨ 1 x v]
    rw [GeometricCurrentOn.boundary_apply, hZ _ Ψ' hslice, hftc.2.2, e0, e1]
  · -- (III): `F(s) = Ψ'(s) − dφ(s)` are `dt`-slices of `dψ` on `[0,1]`, so
    -- `∂Z(ψ) = ∫₀¹ X(F(s)) ds = ∫₀¹ X(Ψ'(s)) ds − ∫₀¹ ∂X(φ(s)) ds`, both integrands being
    -- continuous on `[0,1]`.
    intro m j X Z hX hZ ψ ψ₀ ψ₁ φ h₀ h₁ hφ
    obtain ⟨Ψ, Ψ', hΨ, hΨ'⟩ := hHS m (j + 1) ψ
    have hftc := hF m (j + 1) X ψ Ψ Ψ' hX hΨ hΨ'
    let F : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1) :=
      fun s => Ψ' s - exteriorDerivativeTestOn univ j (φ s)
    have hslice : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
        (F s : DifferentialForm (Eucl m) (j + 1)) x v =
          ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) (j + 1) ψ :
              TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) :
            DifferentialForm (Eucl (m + 1)) (j + 1 + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
      intro s hs x v
      rw [hD.2 m j ψ (φ s) s (fun x w => hφ s hs x w) x v, ← hΨ' s x v]
      rfl
    have hXF : ∀ s, X (F s) = X (Ψ' s) - X.boundary (φ s) := fun s =>
      map_sub X.toCurrent (Ψ' s) (exteriorDerivativeTestOn univ j (φ s))
    have hcont := (hC.1 m (j + 1) X hX _ F hslice).1
    have hI₁ : IntervalIntegrable (fun s => X (Ψ' s)) volume 0 1 :=
      hftc.1.intervalIntegrable 0 1
    have hI₂ : IntervalIntegrable (fun s => X.boundary (φ s)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
      refine (hftc.1.continuousOn.sub hcont).congr fun s _ => ?_
      simp only [Pi.sub_apply, hXF s]
      ring
    have e0 : ψ₀ = Ψ 0 := by
      apply Subtype.ext; funext x; ext v; rw [h₀ x v, hΨ 0 x v]
    have e1 : ψ₁ = Ψ 1 := by
      apply Subtype.ext; funext x; ext v; rw [h₁ x v, hΨ 1 x v]
    rw [GeometricCurrentOn.boundary_apply, hZ _ F hslice]
    simp only [hXF]
    rw [intervalIntegral.integral_sub hI₁ hI₂, hftc.2.2, e0, e1]
  · -- (N): bound `∂Z(ψ)` uniformly over the mass-admissible `ψ` by (II), resp. (III), and the
    -- slice bounds `|X(Ψ(s))| ≤ M(X)`, `|∂X(φ(s))| ≤ M(∂X)`.
    intro hII hIII m k X Z hX hZ hN
    have hmass : ∀ A : ℝ, (∀ ψ ∈ massAdmissibleOn (univ : Set (Eucl (m + 1))) k univ,
        Z.boundary ψ ≤ A) → Z.boundary.mass < ∞ := by
      intro A hA
      have hle : Z.boundary.mass ≤ ENNReal.ofReal A := by
        apply sSup_le
        rintro _ ⟨ψ, hψ, rfl⟩
        exact ENNReal.ofReal_le_ofReal (hA ψ hψ)
      exact hle.trans_lt ENNReal.ofReal_lt_top
    cases k with
    | zero =>
      refine hmass (2 * X.mass.toReal) fun ψ hψ => ?_
      obtain ⟨Ψ, Ψ', hΨ, -⟩ := hHS m 0 ψ
      have hb := hII m X Z hX hZ ψ (Ψ 0) (Ψ 1) (hΨ 0) (hΨ 1)
      have hB := (hC.2 m 0 X hX (ψ : DifferentialForm (Eucl (m + 1)) 0) Ψ
        ψ.2.1.1.continuous ψ.2.1.2 hΨ).2 1 hψ.2
      have h0 := abs_le.mp (hB 0)
      have h1 := abs_le.mp (hB 1)
      rw [hb]
      linarith [h0.1, h1.2]
    | succ j =>
      have hXb : X.boundary.mass < ∞ := hN j X rfl HEq.rfl
      refine hmass (2 * X.mass.toReal + X.boundary.mass.toReal) fun ψ hψ => ?_
      obtain ⟨Ψ, Ψ', hΨ, -⟩ := hHS m (j + 1) ψ
      obtain ⟨φ, -, hφ⟩ := hSF m j ψ
      have hb := hIII m j X Z hX hZ ψ (Ψ 0) (Ψ 1) φ (hΨ 0) (hΨ 1) fun s _ => hφ s
      have hB := (hC.2 m (j + 1) X hX (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) Ψ
        ψ.2.1.1.continuous ψ.2.1.2 hΨ).2 1 hψ.2
      have hB' := (hC.1 m j X.boundary hXb ψ φ fun s _ => hφ s).2 1 hψ.2
      have hI : ‖∫ s in (0 : ℝ)..1, X.boundary (φ s)‖ ≤
          X.boundary.mass.toReal * 1 * |1 - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
        rw [uIoc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs]
        exact hB' s (Ioc_subset_Icc_self hs)
      rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one, mul_one] at hI
      have h0 := abs_le.mp (hB 0)
      have h1 := abs_le.mp (hB 1)
      have h2 := abs_le.mp hI
      rw [hb]
      linarith [h0.1, h1.2, h2.1]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
