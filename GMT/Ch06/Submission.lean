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

/-- Source charts for Simon Ch. 6, Lemma 3.9 (p. 148): under (SNA), (CRC), (CCR) and (LCIP),
countably many `C¹` maps `G k`, antilipschitz on open `O k`, carry the push-forward orientation:
for `Hⁿ`-a.e. `x ∈ M` with `L(x)_# ξ(x) ≠ 0` there are `k` and `w ∈ O k` with `G k w = f x` and
`L(x)_# ξ(x) = ±‖L(x)_# ξ(x)‖ σ₁ ∧ ⋯ ∧ σₙ` for an orthonormal basis `σ` of `range DG_k(w)`. -/
theorem Submission.lpf_pi_source_charts : ((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → (∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0) → (∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), HasWeightedApproximateTangentSpaceAt n M θ (Φ w) (LinearMap.range (fderiv ℝ Φ w).toLinearMap) ∧ HasFDerivAt (f ∘ Φ) ((L (Φ w)).comp (fderiv ℝ Φ w)) w) → (∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → ∃ (G : ℕ → Eucl n → Eucl Q) (O E : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ (∀ k, MeasurableSet (E k)) ∧ (∀ k, E k ⊆ O k ∩ Ω) ∧ Pairwise (Function.onFun Disjoint E) ∧ (∀ k, ∀ w ∈ E k, u w = G k w ∧ HasFDerivAt u (fderiv ℝ (G k) w) w) ∧ ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω → (∃ D : Eucl n →L[ℝ] Eucl Q, HasFDerivAt u D w ∧ Function.Injective D) → w ∈ ⋃ k, E k) → ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → ∃ (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), nVectorPushforward n (L x) (ξ x) ≠ 0 → ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧ (nVectorPushforward n (L x) (ξ x) = ‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ ∨ nVectorPushforward n (L x) (ξ x) = -(‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ)) := by
  intro hsna CRC CCR LCIP P Q n U M θ ξ f L hU htri hf hderiv
  -- antilipschitz chart preimage of an Hⁿ-null set is Lⁿ-null
  have hnull : ∀ (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c →
      (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ (Z : Set (Eucl P)),
      (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
    intro Φ Ω c hc hanti Z hZ
    classical
    have hinj : InjOn Φ Ω := by
      intro w hw w' hw' h
      have h1 := hanti w hw w' hw'
      rw [h, sub_self, norm_zero] at h1
      have h2 : ‖w - w'‖ ≤ 0 := by
        by_contra hcon
        linarith [mul_pos hc (not_le.mp hcon)]
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
    have hΨlip : LipschitzOnWith (Real.toNNReal c⁻¹) (Function.invFunOn Φ Ω) (Φ '' Ω) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      rw [hinj.leftInvOn_invFunOn hw, hinj.leftInvOn_invFunOn hw', dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hanti w hw w' hw'
    have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω) := by
      rintro w ⟨hw, hwZ⟩
      exact ⟨Φ w, ⟨hwZ, w, hw, rfl⟩, hinj.leftInvOn_invFunOn hw⟩
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    apply measure_mono_null hsub
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl n)) (Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω))
        ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) ^ n * μHE[n] (Z ∩ Φ '' Ω) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hΨlip.mono inter_subset_right)
      _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
  -- linear algebra of step 6(iv)-(v)
  have hlinalg : ∀ (D : Eucl n →L[ℝ] Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (τ : Fin n → Eucl P),
      LinearMap.range D.toLinearMap = Submodule.span ℝ (range τ) →
      LinearIndependent ℝ (fun i => A (τ i)) →
      Function.Injective (A.comp D) ∧
        LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
    intro D A τ hD hAτ
    have hrange : LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
      rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, hD, Submodule.map_span, ← range_comp]
      rfl
    refine ⟨?_, hrange⟩
    have hfr : Module.finrank ℝ (LinearMap.range (A.comp D).toLinearMap) = n := by
      rw [hrange, finrank_span_eq_card hAτ, Fintype.card_fin]
    have hker := LinearMap.finrank_range_add_finrank_ker (A.comp D).toLinearMap
    rw [hfr, finrank_euclideanSpace_fin] at hker
    have hker0 : Module.finrank ℝ (LinearMap.ker (A.comp D).toLinearMap) = 0 := by omega
    have : LinearMap.ker (A.comp D).toLinearMap = ⊥ := Submodule.finrank_eq_zero.mp hker0
    exact LinearMap.ker_eq_bot.mp this
  -- covering argument of steps 1, 4, 7
  have hcover_null : ∀ (Φ : ℕ → Eucl n → Eucl P) (Ω Ω' : ℕ → Set (Eucl n)), (∀ j, Ω' j ⊆ Ω j) →
      (∀ j, ∀ w ∈ Ω j, Φ j w ∈ M → w ∈ Ω' j) →
      (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) →
      (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 →
      ∀ (good : Eucl P → Prop),
      (∀ j, (volume : Measure (Eucl n)) {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} = 0) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), good x := by
    intro Φ Ω Ω' hΩ'sub hΩ'cov hΦlip hcover good hbad
    rw [ae_iff, Measure.restrict_apply₀' htri.nullMeasurableSet]
    have hsub : {x | ¬ good x} ∩ M ⊆
        (M \ ⋃ j, Φ j '' Ω j) ∪ ⋃ j, Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} := by
      rintro x ⟨hx, hxM⟩
      by_cases hc : x ∈ ⋃ j, Φ j '' Ω j
      · right
        obtain ⟨j, hj⟩ := mem_iUnion.mp hc
        obtain ⟨w, hw, rfl⟩ := hj
        exact mem_iUnion.mpr ⟨j, w, ⟨hΩ'cov j w hw hxM, hxM, hx⟩, rfl⟩
      · left; exact ⟨hxM, hc⟩
    refine measure_mono_null hsub (measure_union_null hcover (measure_iUnion_null fun j => ?_))
    obtain ⟨K, hK⟩ := hΦlip j
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl P)) (Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hK.mono fun w hw => hΩ'sub j hw.1)
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbad j, mul_zero]
  have hio := Submission.lpf_pi_induced_orientation hsna
  obtain ⟨Φ, Ω, hΩo, hΦc, hΦlip, hΦanti, hcover⟩ := CRC P n M htri.countablyRectifiable
  have hΩ'o : ∀ j, IsOpen (Ω j ∩ Φ j ⁻¹' U) := fun j =>
    (hΩo j).inter ((hΦc j).continuous.isOpen_preimage U hU)
  have hΦanti' : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j ∩ Φ j ⁻¹' U, ∀ w' ∈ Ω j ∩ Φ j ⁻¹' U,
      c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖ := by
    intro j
    obtain ⟨c, hc, h⟩ := hΦanti j
    exact ⟨c, hc, fun w hw w' hw' => h w hw.1 w' hw'.1⟩
  have hloc : ∀ j, LocallyLipschitzOn (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) := by
    intro j w hw
    obtain ⟨K, hK⟩ := hΦlip j
    obtain ⟨Λ, t, ht, hft⟩ := hf hw.2
    rw [hU.nhdsWithin_eq hw.2] at ht
    refine ⟨Λ * K, (Ω j ∩ Φ j ⁻¹' U) ∩ Φ j ⁻¹' t,
      inter_mem_nhdsWithin _ ((hΦc j).continuous.continuousAt.preimage_mem_nhds ht), ?_⟩
    exact hft.comp (hK.mono fun w hw => hw.1.1) fun w hw => hw.2
  choose G O E hOo hGc hGanti hEm hEsub hEdisj hEeq hEcov using
    fun j => LCIP n Q (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) (hΩ'o j) (hloc j)
  refine ⟨fun m => G m.unpair.1 m.unpair.2, fun m => O m.unpair.1 m.unpair.2,
    fun m => hOo _ _, fun m => hGc _ _, fun m => hGanti _ _, ?_⟩
  have hR : (μHE[n] : Measure (Eucl P)) ({x | ¬ ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
      (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp htri.orients).le) zero_le
  apply hcover_null Φ Ω (fun j => Ω j ∩ Φ j ⁻¹' U)
    (fun j => inter_subset_left) (fun j w hw hwM => ⟨hw, htri.subset hwM⟩) hΦlip hcover
  intro j
  have hCCR := CCR P Q n U M θ ξ f L (Φ j) (Ω j ∩ Φ j ⁻¹' U) hU htri hf hderiv (hΩ'o j) (hΦc j)
    (hΦanti' j)
  have hZa := le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp hCCR).le) zero_le
  obtain ⟨c, hc, hanti⟩ := hΦanti' j
  have hZb := hnull (Φ j) (Ω j ∩ Φ j ⁻¹' U) c hc hanti _ hR
  have hZc := ae_iff.mp (hEcov j)
  refine measure_mono_null ?_ (measure_union_null (measure_union_null hZa hZb) hZc)
  rintro w ⟨hw, hxM, hng⟩
  obtain ⟨hΞ, hngood⟩ := not_imp.mp hng
  by_cases ha : HasWeightedApproximateTangentSpaceAt n M θ (Φ j w)
      (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
      HasFDerivAt (f ∘ Φ j) ((L (Φ j w)).comp (fderiv ℝ (Φ j) w)) w
  swap
  · exact Or.inl (Or.inl ⟨ha, hw, hxM⟩)
  by_cases hb : ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ (Φ j w) (Submodule.span ℝ (range τ)) ∧
      (ξ (Φ j w) = simpleNVector τ ∨ ξ (Φ j w) = -simpleNVector τ)
  swap
  · exact Or.inl (Or.inr ⟨hw, hb, hxM⟩)
  refine Or.inr ?_
  show ¬ _
  intro hc'
  apply hngood
  obtain ⟨τ, hτ, htan, hξ⟩ := hb
  obtain ⟨htanΦ, hfd⟩ := ha
  have huniq : LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap = Submodule.span ℝ (range τ) :=
    htanΦ.unique (htri.pos _ hxM).ne' htan
  obtain ⟨hli, σ, hσ, hσspan, hσeq⟩ := hio P Q n τ (L (Φ j w)) (ξ (Φ j w)) hτ hξ hΞ
  obtain ⟨hinj, hrange⟩ := hlinalg (fderiv ℝ (Φ j) w) (L (Φ j w)) τ huniq hli
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hc' hw ⟨_, hfd, hinj⟩)
  obtain ⟨hueq, hufd⟩ := hEeq j k w hk
  have hDeq : fderiv ℝ (G j k) w = (L (Φ j w)).comp (fderiv ℝ (Φ j) w) := hufd.unique hfd
  refine ⟨Nat.pair j k, w, ?_, ?_, σ, hσ, ?_, hσeq⟩
  · simp only [Nat.unpair_pair]; exact (hEsub j k hk).1
  · simp only [Nat.unpair_pair]; exact hueq.symm
  · simp only [Nat.unpair_pair]; rw [hDeq, hrange, hσspan]

/-- Image `n`-vector density of the push-forward (fibre sums over `M₊ = M ∩ {Ξ ≠ 0}`).  The
counting function `N(y) = Σ'_{x ∈ M₊, f x = y} θ x` is locally integrable on `V` by (AF) and
(LF).  On `Y = {y ∈ V : N(y) ≠ 0, N(y) ≠ ∞}` every fibre is finite, and
`Ψ(y) = Σ_{x ∈ M₊, f x = y} (θ x * ‖Ξ x‖⁻¹) • Ξ x` is locally integrable, is a.e. an integer
combination of unit simple `n`-vectors on chart tangent planes (by (CH), off the null image of
the exceptional set), and represents `S` (via the signed fibre sum
`Submission.lpf_pi_signed_fibre_sum`). -/
theorem Submission.lpf_pi_image_density :
    ∀ (P Q n : ℕ) (V : Set (Eucl Q)) (M : Set (Eucl P)) (θ : Eucl P → ℝ)
      (Ξ : Eucl P → NVector (Eucl Q) n) (f : Eucl P → Eucl Q) (G : ℕ → Eucl n → Eucl Q)
      (O : ℕ → Set (Eucl n)) (S : GeometricCurrentOn V n),
      IsOpen V → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M, 0 < θ x) →
      (∀ x ∈ M, ∃ k : ℕ, θ x = k) → AEMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) →
      AEStronglyMeasurable Ξ ((μHE[n] : Measure (Eucl P)).restrict M) → ContinuousOn f M →
      MapsTo f M V →
      (∀ Z ⊆ M, (μHE[n] : Measure (Eucl P)) Z = 0 → (μHE[n] : Measure (Eucl Q)) (f '' Z) = 0) →
      (∀ (A : Set (Eucl P)) (h : Eucl P → ℝ≥0∞), A ⊆ M →
        NullMeasurableSet A (μHE[n] : Measure (Eucl P)) →
        AEMeasurable h ((μHE[n] : Measure (Eucl P)).restrict A) →
        AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x)
          (μHE[n] : Measure (Eucl Q)) ∧
        ∫⁻ x in A, h x * ‖Ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) =
          ∫⁻ y, ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x ∂(μHE[n] : Measure (Eucl Q))) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
        ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) < ∞) →
      (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), Ξ x ≠ 0 →
        ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧
          Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧
          (Ξ x = ‖Ξ x‖ • simpleNVector σ ∨ Ξ x = -(‖Ξ x‖ • simpleNVector σ))) →
      (∀ ω : TestFormOn V n, S ω =
        ∫ x in M, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x))
          ∂(μHE[n] : Measure (Eucl P))) →
      ∃ (Y : Set (Eucl Q)) (Ψ : Eucl Q → NVector (Eucl Q) n), Y ⊆ V ∧
        NullMeasurableSet Y (μHE[n] : Measure (Eucl Q)) ∧
        (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → (μHE[n] : Measure (Eucl Q)) (Y ∩ K) < ∞) ∧
        AEStronglyMeasurable Ψ ((μHE[n] : Measure (Eucl Q)).restrict Y) ∧
        (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
          IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) (μHE[n] : Measure (Eucl Q))) ∧
        (∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict Y),
          ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ) (w : Fin m → Eucl n)
            (σ : Fin m → Fin n → Eucl Q),
            (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧
              Submodule.span ℝ (range (σ i)) =
                LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧
            Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)) ∧
        ∀ ω : TestFormOn V n, S ω =
          ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂(μHE[n] : Measure (Eucl Q)) := by
  intro P Q n V M θ Ξ f G O S hV hM hθpos hθnat hθm hΞm hfc hfV hnull hAF hLF hCH hS
  classical
  generalize hμdef : (μHE[n] : Measure (Eucl P)) = μ at *
  generalize hνdef : (μHE[n] : Measure (Eucl Q)) = ν at *
  have hCA : ContinuousAdd (NVector (Eucl Q) n) :=
    ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl Q) n)).toContinuousAdd.continuous_add⟩
  -- Step 1: positive part
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθnat x hx
    have h0 := hθpos x hx
    rw [hk] at h0 ⊢
    have hk0 : 0 < k := by exact_mod_cast h0
    exact_mod_cast hk0
  obtain ⟨Mp, hMp⟩ : ∃ Mp : Set (Eucl P), Mp = {x | x ∈ M ∧ Ξ x ≠ 0} := ⟨_, rfl⟩
  have hMp_mem : ∀ x, x ∈ Mp ↔ x ∈ M ∧ Ξ x ≠ 0 := by intro x; rw [hMp]; rfl
  have hMpM : Mp ⊆ M := fun x hx => ((hMp_mem x).1 hx).1
  obtain ⟨M₀, hM₀M, hM₀m, hM₀ae⟩ := hM.exists_measurable_subset_ae_eq
  have hrestr : μ.restrict M₀ = μ.restrict M := Measure.restrict_congr_set hM₀ae
  have hnΞ : AEStronglyMeasurable (fun x => ‖Ξ x‖) (μ.restrict M₀) := by
    rw [hrestr]
    exact (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΞm
  have hMpnm : NullMeasurableSet Mp μ := by
    obtain ⟨φ, hφm, hφeq⟩ : ∃ φ : Eucl P → ℝ, Measurable φ ∧
        (fun x => ‖Ξ x‖) =ᵐ[μ.restrict M₀] φ :=
      ⟨hnΞ.mk _, hnΞ.stronglyMeasurable_mk.measurable, hnΞ.ae_eq_mk⟩
    have h1 : ∀ᵐ x ∂μ, x ∈ M₀ → ‖Ξ x‖ = φ x :=
      (ae_restrict_iff' hM₀m).1 hφeq
    have h2 : ∀ᵐ x ∂μ, x ∈ M₀ ↔ x ∈ M := eventuallyEqSet_iff.1 hM₀ae
    have hmeas : MeasurableSet (M₀ ∩ {x | φ x ≠ 0}) :=
      hM₀m.inter (hφm (measurableSet_singleton 0).compl)
    refine hmeas.nullMeasurableSet.congr (eventuallyEqSet_iff.2 ?_)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hMp_mem]
    constructor
    · rintro ⟨hxM₀, hφx⟩
      refine ⟨hx2.1 hxM₀, ?_⟩
      intro hΞx
      apply hφx
      rw [← hx1 hxM₀, hΞx]
      exact ContinuousLinearMap.opNorm_zero
    · rintro ⟨hxM, hΞx⟩
      have hxM₀ : x ∈ M₀ := hx2.2 hxM
      refine ⟨hxM₀, ?_⟩
      show φ x ≠ 0
      rw [← hx1 hxM₀]
      exact fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
  have hAFp : ∀ h : Eucl P → ℝ≥0∞, AEMeasurable h (μ.restrict Mp) →
      AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, h x) ν ∧
      ∫⁻ x in Mp, h x * ‖Ξ x‖ₑ ∂μ = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, h x ∂ν :=
    fun h hh => hAF Mp h hMpM hMpnm hh
  -- Step 2: counting function
  obtain ⟨N, hN⟩ : ∃ N : Eucl Q → ℝ≥0∞,
      N = fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := ⟨_, rfl⟩
  have hθmp : AEMeasurable (fun x => ENNReal.ofReal (θ x)) (μ.restrict Mp) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hθm).mono_set hMpM
  have hNm : AEMeasurable N ν := by rw [hN]; exact (hAFp _ hθmp).1
  -- Step 3: closed-set argument and local finiteness
  have hclosed : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      ∃ C : Set (Eucl P), IsClosed C ∧ (∀ x ∈ M, (x ∈ C ↔ f x ∈ K)) ∧
        ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ < ∞ := by
    intro K hK hKV
    obtain ⟨C, hCc, hCeq⟩ := (continuousOn_iff_isClosed.mp hfc) K hK.isClosed
    refine ⟨C, hCc, ?_, ?_⟩
    · intro x hx
      constructor
      · intro hxC
        have : x ∈ C ∩ M := ⟨hxC, hx⟩
        rw [← hCeq] at this
        exact this.1
      · intro hfx
        have : x ∈ f ⁻¹' K ∩ M := ⟨hfx, hx⟩
        rw [hCeq] at this
        exact this.1
    · calc ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ
          ≤ ∫⁻ x in M, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ :=
            lintegral_mono_set hMpM
        _ = ∫⁻ x in C ∩ M, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂μ := by
            rw [lintegral_indicator hCc.measurableSet, Measure.restrict_restrict hCc.measurableSet]
        _ = ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂μ := by
            rw [← hCeq, Set.inter_comm]
        _ < ∞ := hLF K hK hKV
  have hfib_ind : ∀ (K : Set (Eucl Q)) (C : Set (Eucl P)), (∀ x ∈ M, (x ∈ C ↔ f x ∈ K)) →
      ∀ (u : Eucl P → ℝ≥0∞) (y : Eucl Q),
        ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, C.indicator u x =
          K.indicator (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, u x) y := by
    intro K C hC u y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      refine tsum_congr fun x => ?_
      have hxC : (x : Eucl P) ∈ C := (hC x (hMpM x.2.1)).2 (by rw [x.2.2]; exact hy)
      rw [Set.indicator_of_mem hxC]
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, C.indicator u x = 0 := by
        intro x
        have hxC : (x : Eucl P) ∉ C := fun h => hy (by rw [← x.2.2]; exact (hC x (hMpM x.2.1)).1 h)
        rw [Set.indicator_of_notMem hxC]
      simp only [this, tsum_zero]
  have hNK : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∫⁻ y, K.indicator N y ∂ν < ∞ := by
    intro K hK hKV
    obtain ⟨C, hCc, hCK, hCfin⟩ := hclosed K hK hKV
    have hh : AEMeasurable (C.indicator (fun x => ENNReal.ofReal (θ x))) (μ.restrict Mp) :=
      hθmp.indicator hCc.measurableSet
    have key := (hAFp _ hh).2
    calc ∫⁻ y, K.indicator N y ∂ν
        = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y},
            C.indicator (fun x => ENNReal.ofReal (θ x)) x ∂ν := by
          refine lintegral_congr fun y => ?_
          rw [hfib_ind K C hCK, hN]
      _ = ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x)) x * ‖Ξ x‖ₑ ∂μ := key.symm
      _ = ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ := by
          refine lintegral_congr fun x => ?_
          by_cases hx : x ∈ C <;> simp [hx]
      _ < ∞ := hCfin
  -- Step 4/5: fibre facts
  have hNy : ∀ y, N y = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := by
    intro y; rw [hN]
  have hfin : ∀ y, N y ≠ ∞ → Finite {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    apply hy
    rw [hNy, ← top_le_iff]
    calc (∞ : ℝ≥0∞) = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, (1 : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hθ1 x (hMpM x.2.1))
  have hempty : ∀ y, N y = 0 → IsEmpty {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    rw [hNy, ENNReal.tsum_eq_zero] at hy
    refine ⟨fun x => ?_⟩
    have h1 := hy x
    rw [ENNReal.ofReal_eq_zero] at h1
    linarith [hθ1 x (hMpM x.2.1)]
  have hNge1 : ∀ y, N y ≠ 0 → 1 ≤ N y := by
    intro y hy
    rw [hNy] at hy ⊢
    obtain ⟨x, hx⟩ : ∃ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (ENNReal.tsum_eq_zero.2 h)
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (θ x) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hθ1 x (hMpM x.2.1))
      _ ≤ ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) :=
          ENNReal.le_tsum (f := fun x : {x : Eucl P // x ∈ Mp ∧ f x = y} => ENNReal.ofReal (θ x)) x
  have hnotV : ∀ y, y ∉ V → IsEmpty {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    refine ⟨fun x => hy ?_⟩
    rw [← x.2.2]
    exact hfV (hMpM x.2.1)
  -- Step 5: the set Y
  obtain ⟨Y, hY⟩ : ∃ Y : Set (Eucl Q), Y = {y | y ∈ V ∧ N y ≠ 0 ∧ N y ≠ ∞} := ⟨_, rfl⟩
  have hY_mem : ∀ y, y ∈ Y ↔ y ∈ V ∧ N y ≠ 0 ∧ N y ≠ ∞ := by intro y; rw [hY]; rfl
  have hYV : Y ⊆ V := fun y hy => ((hY_mem y).1 hy).1
  have hYnm : NullMeasurableSet Y ν := by
    have h1 : NullMeasurableSet (N ⁻¹' {0}ᶜ) ν :=
      hNm.nullMeasurable (measurableSet_singleton 0).compl
    have h2 : NullMeasurableSet (N ⁻¹' {∞}ᶜ) ν :=
      hNm.nullMeasurable (measurableSet_singleton ∞).compl
    have : Y = V ∩ (N ⁻¹' {0}ᶜ ∩ N ⁻¹' {∞}ᶜ) := by
      ext y; rw [hY_mem]; simp
    rw [this]
    exact hV.measurableSet.nullMeasurableSet.inter (h1.inter h2)
  have hYK : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ν (Y ∩ K) < ∞ := by
    intro K hK hKV
    have hsub : Y ∩ K ⊆ {y | 1 ≤ K.indicator N y} := by
      rintro y ⟨hyY, hyK⟩
      rw [Set.mem_ofPred_eq, Set.indicator_of_mem hyK]
      exact hNge1 y ((hY_mem y).1 hyY).2.1
    have hmk := mul_meas_ge_le_lintegral₀ (hNm.indicator hK.measurableSet) 1
    rw [one_mul] at hmk
    exact lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt hmk (hNK K hK hKV))
  -- Step 6: the density
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : Eucl P → NVector (Eucl Q) n,
      ϑ = fun x => (θ x * ‖Ξ x‖⁻¹) • Ξ x := ⟨_, rfl⟩
  have hϑx : ∀ x, ϑ x = (θ x * ‖Ξ x‖⁻¹) • Ξ x := fun x => by rw [hϑ]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Eucl Q → NVector (Eucl Q) n,
      Ψ = fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := ⟨_, rfl⟩
  have hΨy : ∀ y, Ψ y = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := fun y => by rw [hΨ]
  have hnormΞ : AEStronglyMeasurable (fun x => ‖Ξ x‖) (μ.restrict M) :=
    (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΞm
  have hϑm : AEStronglyMeasurable ϑ (μ.restrict Mp) := by
    rw [hϑ]
    have h1 : AEStronglyMeasurable (fun x => θ x * ‖Ξ x‖⁻¹) (μ.restrict M) :=
      (hθm.mul hnormΞ.aemeasurable.inv).aestronglyMeasurable
    exact (h1.smul hΞm).mono_set hMpM
  have hgβ : ∀ β : Covector (Eucl Q) n,
      AEStronglyMeasurable (fun x => ϑ x β) (μ.restrict Mp) :=
    fun β => (continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hϑm
  -- Step 7: measurability of Ψ on Y
  have hΨβ : ∀ β : Covector (Eucl Q) n, AEMeasurable (fun y => Ψ y β) (ν.restrict Y) := by
    intro β
    have hp := (hAFp (fun x => ENNReal.ofReal (ϑ x β))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hgβ β).aemeasurable)).1
    have hm := (hAFp (fun x => ENNReal.ofReal (-ϑ x β))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hgβ β).aemeasurable.neg)).1
    refine ((hp.ennreal_toReal.sub hm.ennreal_toReal).mono_measure
      Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem₀ hYnm] with y hy
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hy).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    simp only [Pi.sub_apply]
    rw [hΨy, tsum_fintype, tsum_fintype, tsum_fintype,
      ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top),
      ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top), ← Finset.sum_sub_distrib,
      sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    exact max_zero_sub_eq_self _
  have := Submission.lpf_pi_covector_finiteDimensional Q n
  obtain ⟨D, b, bs, hexp⟩ : ∃ (D : ℕ) (b : Fin D → Covector (Eucl Q) n)
      (bs : Fin D → NVector (Eucl Q) n), ∀ ζ : NVector (Eucl Q) n, ζ = ∑ i, ζ (b i) • bs i := by
    let bb := Module.finBasis ℝ (Covector (Eucl Q) n)
    refine ⟨_, bb, fun i => LinearMap.toContinuousLinearMap (bb.coord i), fun ζ => ?_⟩
    ext α
    have hα : α = ∑ i, bb.repr α i • bb i := (bb.sum_repr α).symm
    calc ζ α = ζ (∑ i, bb.repr α i • bb i) := by rw [← hα]
      _ = ∑ i, bb.repr α i * ζ (bb i) := by simp only [map_sum, map_smul, smul_eq_mul]
      _ = (∑ i, ζ (bb i) • LinearMap.toContinuousLinearMap (bb.coord i)) α := by
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
  have hΨm : AEStronglyMeasurable Ψ (ν.restrict Y) := by
    have h1 : AEStronglyMeasurable (fun y => ∑ i, Ψ y (b i) • bs i) (ν.restrict Y) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (hΨβ (b i)).aestronglyMeasurable.smul_const (bs i)
    exact h1.congr (Eventually.of_forall fun y => (hexp (Ψ y)).symm)
  -- Step 8: integrability
  have hϑnorm : ∀ x ∈ Mp, ‖ϑ x‖ ≤ θ x := by
    intro x hx
    obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
    have hpos : 0 < ‖Ξ x‖ := lt_of_le_of_ne (norm_nonneg (Ξ x))
      (Ne.symm fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h))
    rw [hϑx]
    calc ‖(θ x * ‖Ξ x‖⁻¹) • Ξ x‖ ≤ ‖θ x * ‖Ξ x‖⁻¹‖ * ‖Ξ x‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ = θ x := by
          rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hθpos x hxM) (inv_pos.2 hpos)),
            inv_mul_cancel_right₀ hpos.ne']
  have hΨnorm : ∀ y ∈ Y, ENNReal.ofReal ‖Ψ y‖ ≤ N y := by
    intro y hy
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hy).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    rw [hΨy, hNy, tsum_fintype, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg (fun (x : {x : Eucl P // x ∈ Mp ∧ f x = y}) _ =>
        zero_le_one.trans (hθ1 x (hMpM x.2.1)))]
    refine ENNReal.ofReal_le_ofReal ?_
    refine ContinuousLinearMap.opNorm_le_bound _
      (Finset.sum_nonneg fun x _ => zero_le_one.trans (hθ1 x (hMpM x.2.1))) fun α => ?_
    rw [sum_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hϑnorm x x.2.1) (norm_nonneg α))
  have hint : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) ν := by
    intro K hK hKV
    refine ⟨((@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΨm).mono_set
      Set.inter_subset_left, ?_⟩
    show ∫⁻ y in Y ∩ K, ‖‖Ψ y‖‖ₑ ∂ν < ∞
    calc ∫⁻ y in Y ∩ K, ‖‖Ψ y‖‖ₑ ∂ν ≤ ∫⁻ y in Y ∩ K, K.indicator N y ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ (hYnm.inter hK.measurableSet.nullMeasurableSet)]
            with y hy
          rw [Real.enorm_eq_ofReal (norm_nonneg (Ψ y)), Set.indicator_of_mem hy.2]
          exact hΨnorm y hy.1
      _ ≤ ∫⁻ y, K.indicator N y ∂ν := setLIntegral_le_lintegral _ _
      _ < ∞ := hNK K hK hKV
  -- Step 9: chart family
  have hCH' := (ae_restrict_iff'₀ hM).1 hCH
  obtain ⟨Gd, hGd_ae, hGd⟩ := hCH'.exists_mem
  have hGdc : μ Gdᶜ = 0 := mem_ae_iff.1 hGd_ae
  have hBnull : μ (Gdᶜ ∩ M) = 0 := measure_mono_null Set.inter_subset_left hGdc
  have hE : ν (f '' (Gdᶜ ∩ M)) = 0 := hnull _ Set.inter_subset_right hBnull
  have hchart : ∀ᵐ y ∂(ν.restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ)
      (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q),
      (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧
        Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧
      Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i) := by
    have hE' : ∀ᵐ y ∂ν, y ∉ f '' (Gdᶜ ∩ M) := measure_eq_zero_iff_ae_notMem.1 hE
    filter_upwards [ae_restrict_mem₀ hYnm, ae_restrict_of_ae hE'] with y hyY hyE
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hyY).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    have hdata : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ∃ k, ∃ w ∈ O k, G k w = y ∧
        ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧
          Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧
          ∃ a : ℤ, ϑ x = (a : ℝ) • simpleNVector σ := by
      intro x
      obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 x.2.1
      have hxGd : (x : Eucl P) ∈ Gd := by
        by_contra hc
        exact hyE ⟨x, ⟨hc, hxM⟩, x.2.2⟩
      obtain ⟨k, w, hw, hGw, σ, hσ, hspan, hsign⟩ := hGd x hxGd hxM hΞx
      obtain ⟨j, hj⟩ := hθnat x hxM
      refine ⟨k, w, hw, hGw.trans x.2.2, σ, hσ, hspan, ?_⟩
      have hpos : ‖Ξ x‖ ≠ 0 := fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
      rcases hsign with h | h
      · refine ⟨j, ?_⟩
        calc ϑ x = (θ x * ‖Ξ x‖⁻¹) • Ξ x := hϑx x
          _ = (θ x * ‖Ξ x‖⁻¹) • (‖Ξ x‖ • simpleNVector σ) := by rw [← h]
          _ = (θ x * ‖Ξ x‖⁻¹ * ‖Ξ x‖) • simpleNVector σ := smul_smul _ _ _
          _ = ((j : ℤ) : ℝ) • simpleNVector σ := by
              rw [inv_mul_cancel_right₀ hpos, hj, Int.cast_natCast]
      · refine ⟨-(j : ℤ), ?_⟩
        have hα : ∀ α : Covector (Eucl Q) n, Ξ x α = -(‖Ξ x‖ * α σ) := fun α =>
          congrArg (fun z : NVector (Eucl Q) n => z α) h
        rw [hϑx]
        ext α
        show (θ x * ‖Ξ x‖⁻¹) * Ξ x α = ((-(j : ℤ) : ℤ) : ℝ) * α σ
        rw [hα α, hj]
        have hr : ‖Ξ x‖⁻¹ * ‖Ξ x‖ = 1 := inv_mul_cancel₀ hpos
        calc (j : ℝ) * ‖Ξ x‖⁻¹ * -(‖Ξ x‖ * α σ) = -((j : ℝ) * (‖Ξ x‖⁻¹ * ‖Ξ x‖) * α σ) := by
              ring
          _ = ((-(j : ℤ) : ℤ) : ℝ) * α σ := by rw [hr]; push_cast; ring
    choose k w hw hGw σ hσ hspan a ha using hdata
    let e := Fintype.equivFin {x : Eucl P // x ∈ Mp ∧ f x = y}
    refine ⟨Fintype.card {x : Eucl P // x ∈ Mp ∧ f x = y}, fun i => a (e.symm i),
      fun i => k (e.symm i), fun i => w (e.symm i), fun i => σ (e.symm i),
      fun i => ⟨hw _, hGw _, hσ _, hspan _⟩, ?_⟩
    calc Ψ y = ∑ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := by rw [hΨy, tsum_fintype]
      _ = ∑ i, ϑ (e.symm i) := (e.symm.sum_comp (fun x => ϑ x)).symm
      _ = ∑ i, (a (e.symm i) : ℝ) • simpleNVector (σ (e.symm i)) :=
          Finset.sum_congr rfl fun i _ => ha (e.symm i)
  -- Step 10: representation
  have hrep : ∀ ω : TestFormOn V n,
      S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂ν := by
    intro ω
    obtain ⟨⟨hωs, hωc⟩, hωV⟩ := ω.2
    obtain ⟨Cω, hCω⟩ := hωc.exists_bound_of_continuous hωs.continuous
    have hCω0 : 0 ≤ Cω := (norm_nonneg _).trans (hCω 0)
    obtain ⟨Cl, hCl_closed, hCl_iff, hCl_fin⟩ := hclosed _ hωc.isCompact hωV
    obtain ⟨g, hg⟩ : ∃ g : Eucl P → ℝ,
        g = fun x => ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x)) := ⟨_, rfl⟩
    have hgx : ∀ x, g x = ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x)) := fun x => by rw [hg]
    -- (a)
    have ha : S ω = ∫ x in Mp, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂μ := by
      rw [hS ω]
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hM hMpM
        (Eventually.of_forall fun x hx => ?_)
      have : Ξ x = 0 := by
        by_contra hne
        exact hx.2 ((hMp_mem x).2 ⟨hx.1, hne⟩)
      rw [this, zero_apply, mul_zero]
    -- (b)
    have hb : ∫ x in Mp, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂μ =
        ∫ x in Mp, g x * (‖Ξ x‖ₑ).toReal ∂μ := by
      refine setIntegral_congr_fun₀ hMpnm fun x hx => ?_
      obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
      have hpos : ‖Ξ x‖ ≠ 0 := fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
      rw [hgx, hϑx, toReal_enorm, smul_apply, smul_eq_mul]
      field_simp
    have hωf : AEStronglyMeasurable (fun x => (ω : DifferentialForm (Eucl Q) n) (f x))
        (μ.restrict Mp) := by
      have h0 : AEStronglyMeasurable (fun x => (ω : DifferentialForm (Eucl Q) n) (f x))
          (μ.restrict M₀) :=
        (hωs.continuous.comp_continuousOn (hfc.mono hM₀M)).aestronglyMeasurable hM₀m
      rw [hrestr] at h0
      exact h0.mono_set hMpM
    have hgm : AEStronglyMeasurable g (μ.restrict Mp) := by
      rw [hg]
      exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hϑm.prodMk hωf)
    have hgfin : ∫⁻ x in Mp, ‖g x‖ₑ * ‖Ξ x‖ₑ ∂μ < ∞ := by
      calc ∫⁻ x in Mp, ‖g x‖ₑ * ‖Ξ x‖ₑ ∂μ
          ≤ ∫⁻ x in Mp, ENNReal.ofReal Cω *
              Cl.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem₀ hMpnm] with x hx
            obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
            by_cases hxC : x ∈ Cl
            · rw [Set.indicator_of_mem hxC]
              have hgle : ‖g x‖ₑ ≤ ENNReal.ofReal Cω * ENNReal.ofReal (θ x) := by
                rw [← ENNReal.ofReal_mul hCω0, hgx, Real.enorm_eq_ofReal_abs]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [← Real.norm_eq_abs]
                calc ‖ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x))‖
                    ≤ ‖ϑ x‖ * ‖(ω : DifferentialForm (Eucl Q) n) (f x)‖ :=
                      ContinuousLinearMap.le_opNorm _ _
                  _ ≤ θ x * Cω := mul_le_mul (hϑnorm x hx) (hCω _) (norm_nonneg _)
                      (zero_le_one.trans (hθ1 x hxM))
                  _ = Cω * θ x := mul_comm _ _
              calc ‖g x‖ₑ * ‖Ξ x‖ₑ ≤ (ENNReal.ofReal Cω * ENNReal.ofReal (θ x)) * ‖Ξ x‖ₑ := by
                    gcongr
                _ = ENNReal.ofReal Cω * (ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) := mul_assoc _ _ _
            · have hfx : f x ∉ tsupport (ω : DifferentialForm (Eucl Q) n) :=
                fun h => hxC ((hCl_iff x hxM).2 h)
              have : g x = 0 := by rw [hgx, image_eq_zero_of_notMem_tsupport hfx, map_zero]
              rw [this, enorm_zero, zero_mul]
              exact zero_le
        _ = ENNReal.ofReal Cω *
              ∫⁻ x in Mp, Cl.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCl_fin
    have hJm : AEMeasurable (fun x => ‖Ξ x‖ₑ) (μ.restrict Mp) := by
      have h0 := (hnormΞ.aemeasurable.ennreal_ofReal).mono_set hMpM
      exact h0.congr (Eventually.of_forall fun x => ofReal_norm (Ξ x))
    obtain ⟨-, -, heq⟩ := Submission.lpf_pi_signed_fibre_sum (Eucl P) (Eucl Q) μ ν f Mp
      (fun x => ‖Ξ x‖ₑ) hJm hAFp g hgm hgfin
    -- (d)
    have hNfin : ∀ᵐ y ∂ν, y ∈ tsupport (ω : DifferentialForm (Eucl Q) n) → N y < ∞ := by
      have h1 := ae_lt_top' (hNm.indicator hωc.isCompact.measurableSet)
        (hNK _ hωc.isCompact hωV).ne
      filter_upwards [h1] with y hy hyK
      rwa [Set.indicator_of_mem hyK] at hy
    have hd : (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, g x) =ᵐ[ν]
        Y.indicator (fun y => Ψ y ((ω : DifferentialForm (Eucl Q) n) y)) := by
      filter_upwards [hNfin] with y hy
      by_cases hyY : y ∈ Y
      · rw [Set.indicator_of_mem hyY]
        have hyN : N y ≠ ∞ := ((hY_mem y).1 hyY).2.2
        have := hfin y hyN
        have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
        rw [tsum_fintype, hΨy, tsum_fintype, sum_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hgx, x.2.2]
      · rw [Set.indicator_of_notMem hyY]
        by_cases hyV : y ∈ V
        · by_cases hN0 : N y = 0
          · have := hempty y hN0
            exact tsum_empty
          · have hNinf : N y = ∞ := by
              by_contra h
              exact hyY ((hY_mem y).2 ⟨hyV, hN0, h⟩)
            have hyK : y ∉ tsupport (ω : DifferentialForm (Eucl Q) n) :=
              fun hyK => (hy hyK).ne hNinf
            have : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, g x = 0 := by
              intro x
              rw [hgx, x.2.2, image_eq_zero_of_notMem_tsupport hyK, map_zero]
            simp only [this, tsum_zero]
        · have := hnotV y hyV
          exact tsum_empty
    rw [ha, hb]
    refine heq.trans ?_
    rw [integral_congr_ae hd, integral_indicator₀ hYnm]
  exact ⟨Y, Ψ, hYV, hYnm, hYK, hΨm, hint, hchart, hrep⟩
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
/-- Countable Lipschitz cover (Lindelöf): if `f` is locally Lipschitz on an arbitrary `U ⊆ ℝ^P`,
then countably many open sets `O i` cover `U` and `f` is `K i`-Lipschitz on each `O i ∩ U`. -/
theorem Submission.lpf_lli_countable_lipschitz_cover : ∀ (P Q : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q), LocallyLipschitzOn U f → ∃ (O : ℕ → Set (Eucl P)) (K : ℕ → ℝ≥0), (∀ i, IsOpen (O i)) ∧ U ⊆ ⋃ i, O i ∧ ∀ i, LipschitzOnWith (K i) f (O i ∩ U) := by
  intro P Q U f hf
  -- Step 1: each `x ∈ U` has an open `o x ∋ x` with `f` `k x`-Lipschitz on `o x ∩ U`.
  have hloc : ∀ x ∈ U, ∃ (o : Set (Eucl P)) (k : ℝ≥0),
      IsOpen o ∧ x ∈ o ∧ LipschitzOnWith k f (o ∩ U) := by
    intro x hx
    obtain ⟨k, t, ht, hft⟩ := hf hx
    obtain ⟨o, ho, hxo, hot⟩ := mem_nhdsWithin.1 ht
    exact ⟨o, k, ho, hxo, hft.mono hot⟩
  choose! o k ho hxo hfo using hloc
  -- Step 2: `ℝ^P` is hereditarily Lindelöf, so countably many `o x` (`x ∈ T ⊆ U`) cover `U`.
  obtain ⟨T, hTc, hTU, hUT⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_nhds_subcover o
    fun x hx => (ho x hx).mem_nhds (hxo x hx)
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- Step 3: `T = ∅` forces `U = ∅`; take empty pieces.
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, fun x hx => ?_, fun _ => ?_⟩
    · simpa using hUT hx
    · simp
  · -- Step 4: enumerate `T = range g` and take `O i = o (g i)`, `K i = k (g i)`.
    obtain ⟨g, rfl⟩ := hTc.exists_eq_range hTne
    refine ⟨fun i => o (g i), fun i => k (g i), fun i => ho _ (hTU _ (mem_range_self i)),
      fun x hx => ?_, fun i => hfo _ (hTU _ (mem_range_self i))⟩
    -- Step 5: the pieces cover `U`.
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.1 (hUT hx)
    exact mem_iUnion.2 ⟨i, hxy⟩
/-- Compact inner approximation: a `μ`-null-measurable `A ⊆ ℝ^P` with `μ ⌞ A` σ-finite is,
up to a `μ`-null set, the union of countably many compact subsets of `A`. -/
theorem Submission.lpf_lli_inner_compact_approx : ∀ (P : ℕ) (μ : Measure (Eucl P)) (A : Set (Eucl P)), NullMeasurableSet A μ → SigmaFinite (μ.restrict A) → ∃ C : ℕ → Set (Eucl P), (∀ k, IsCompact (C k)) ∧ (∀ k, C k ⊆ A) ∧ μ (A \ ⋃ k, C k) = 0 := by
  intro P μ A hA hσ
  -- Step 1: a Borel set `A' ⊆ A` with `μ (A \ A') = 0`.
  obtain ⟨A', hA'A, hA'm, hA'ae⟩ := hA.exists_measurable_subset_ae_eq
  have hAA' : μ (A \ A') = 0 := (ae_eq_set.1 hA'ae).2
  -- Step 2: the Borel pieces `B m = A' ∩ S m`, `S = spanningSets (μ ⌞ A)`, have finite measure.
  set S := spanningSets (μ.restrict A) with hS
  set B : ℕ → Set (Eucl P) := fun m => A' ∩ S m
  have hBA : ∀ m, B m ⊆ A := fun m => inter_subset_left.trans hA'A
  have hBm : ∀ m, MeasurableSet (B m) := fun m => hA'm.inter (measurableSet_spanningSets _ m)
  have hBfin : ∀ m, μ (B m) ≠ ∞ := by
    intro m
    have h : μ.restrict A (B m) = μ (B m) := by
      rw [Measure.restrict_apply (hBm m), inter_eq_left.2 (hBA m)]
    rw [← h]
    exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ m)).ne
  -- Step 3: the finite measure `μ ⌞ B m` on `ℝ^P` is regular, so there are compact
  -- `K m j ⊆ B m` with `μ (B m \ K m j) < (j + 1)⁻¹`.
  have hK : ∀ m j : ℕ, ∃ K, K ⊆ B m ∧ IsCompact K ∧ μ (B m \ K) < ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro m j
    have : IsFiniteMeasure (μ.restrict (B m)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hBfin m).lt_top⟩
    have : (μ.restrict (B m)).Regular :=
      Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    obtain ⟨K, hKB, hKc, hKlt⟩ := (hBm m).exists_isCompact_sdiff_lt (μ := μ.restrict (B m))
      (measure_ne_top _ _) (ε := ((j : ℝ≥0∞) + 1)⁻¹) (by simp)
    refine ⟨K, hKB, hKc, ?_⟩
    rwa [Measure.restrict_apply ((hBm m).diff hKc.measurableSet),
      inter_eq_left.2 sdiff_subset] at hKlt
  choose K hKB hKc hKlt using hK
  -- Step 4: `μ (B m \ ⋃ j, K m j) < (j + 1)⁻¹` for every `j`, hence it vanishes.
  have hnull : ∀ m, μ (B m \ ⋃ j, K m j) = 0 := by
    intro m
    by_contra h
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
    have h1 : μ (B m \ ⋃ j, K m j) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      (measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ n))).trans_lt (hKlt m n)
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact lt_irrefl _ ((h1.trans_le h2).trans hn)
  -- Steps 5 and 6: re-index `K m j` along `Nat.unpair`; the rest of `A` lies in the null set
  -- `(A \ A') ∪ ⋃ m, (B m \ ⋃ j, K m j)`.
  refine ⟨fun k => K (Nat.unpair k).1 (Nat.unpair k).2, fun k => hKc _ _,
    fun k => (hKB _ _).trans (hBA _), measure_mono_null ?_
      (measure_union_null hAA' (measure_iUnion_null hnull))⟩
  rintro x ⟨hxA, hxC⟩
  by_cases hx : x ∈ A'
  · have hxS : x ∈ ⋃ m, S m := by rw [hS, iUnion_spanningSets]; exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxS
    refine Or.inr (mem_iUnion.2 ⟨m, ⟨hx, hm⟩, fun hxK => hxC ?_⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.1 hxK
    exact mem_iUnion.2 ⟨Nat.pair m j, by simpa only [Nat.unpair_pair] using hj⟩
  · exact Or.inl ⟨hxA, hx⟩

/-- Locally Lipschitz images (step (P3) of Simon Ch. 6, Lemma 3.9; cf. Ch. 2, Theorem 1.8(i)).
If `f` is locally Lipschitz on `U ⊆ ℝ^P`, then `f` maps `Hⁿ`-null subsets of `U` to `Hⁿ`-null
sets, and `Hⁿ`-null-measurable `A ⊆ U` with `Hⁿ ⌞ A` σ-finite to `Hⁿ`-null-measurable sets. -/
theorem Submission.lpf_locally_lipschitz_image : ∀ (P Q n : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q), LocallyLipschitzOn U f → (∀ Z ⊆ U, (μHE[n] : Measure (Eucl P)) Z = 0 → (μHE[n] : Measure (Eucl Q)) (f '' Z) = 0) ∧ ∀ A ⊆ U, NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → SigmaFinite ((μHE[n] : Measure (Eucl P)).restrict A) → NullMeasurableSet (f '' A) (μHE[n] : Measure (Eucl Q)) := by
  intro P Q n U f hf
  -- Step 1: open sets `O i` covering `U`, with `f` `K i`-Lipschitz on `O i ∩ U`.
  obtain ⟨O, K, -, hUO, hK⟩ := Submission.lpf_lli_countable_lipschitz_cover P Q U f hf
  -- Step 2, part (i): `Hⁿ(f(Z ∩ O i)) ≤ (K i)ⁿ Hⁿ(Z ∩ O i) = 0` and `f(Z) ⊆ ⋃ i, f(Z ∩ O i)`.
  have hnull : ∀ Z ⊆ U, (μHE[n] : Measure (Eucl P)) Z = 0 →
      (μHE[n] : Measure (Eucl Q)) (f '' Z) = 0 := by
    intro Z hZU hZ
    have hcover : f '' Z ⊆ ⋃ i, f '' (Z ∩ O i) := by
      rintro _ ⟨x, hxZ, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hUO (hZU hxZ))
      exact mem_iUnion.2 ⟨i, x, ⟨hxZ, hi⟩, rfl⟩
    refine measure_mono_null hcover (measure_iUnion_null fun i => nonpos_iff_eq_zero.1 ?_)
    calc (μHE[n] : Measure (Eucl Q)) (f '' (Z ∩ O i))
        ≤ (K i : ℝ≥0∞) ^ n * (μHE[n] : Measure (Eucl P)) (Z ∩ O i) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            ((hK i).mono fun x hx => ⟨hx.2, hZU hx.1⟩)
      _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
  refine ⟨hnull, fun A hAU hA hσ => ?_⟩
  -- Step 3: compact `C k ⊆ A` with `Hⁿ(A \ ⋃ k, C k) = 0`.
  obtain ⟨C, hCc, hCA, hAC⟩ := Submission.lpf_lli_inner_compact_approx P _ A hA hσ
  -- Step 4: each `f(C k)` is compact (`f` is continuous on `U ⊇ C k`), hence Borel, and
  -- `f(A \ ⋃ k, C k)` is `Hⁿ`-null by part (i).
  have hB : MeasurableSet (⋃ k, f '' C k) := MeasurableSet.iUnion fun k =>
    ((hCc k).image_of_continuousOn (hf.continuousOn.mono ((hCA k).trans hAU))).isClosed
      |>.measurableSet
  have hsplit : f '' A = (⋃ k, f '' C k) ∪ f '' (A \ ⋃ k, C k) := by
    rw [← image_iUnion, ← image_union, union_sdiff_cancel (iUnion_subset hCA)]
  rw [hsplit]
  exact hB.nullMeasurableSet.union (.of_null (hnull _ (sdiff_subset.trans hAU) hAC))
/-- Simon Ch. 1, Theorem 1.17 (Lusin), in the form used in the proof of Ch. 2, Theorem 1.5
(p. 44), "which applies to sets of infinite measure for `Lⁿ`": if `S ⊆ ℝⁿ` is Borel and
`f : ℝⁿ → (ℝⁿ)*` is Borel measurable, then for every `ε > 0` there is a closed `C ⊆ S` with
`Lⁿ(S ∖ C) < ε` and `f|C` continuous. -/
theorem Submission.lpf_c1r_lusin_closed :
    ∀ (n : ℕ) (S : Set (Eucl n)) (f : Eucl n → (Eucl n →L[ℝ] ℝ)), MeasurableSet S →
      Measurable f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Eucl n), IsClosed C ∧ C ⊆ S ∧
        (volume : Measure (Eucl n)) (S \ C) < ε ∧ ContinuousOn f C := by
  intro n S f hS hf ε hε
  -- Closed inner approximation of Borel sets of any measure: on the closed annuli
  -- `K j = {j ≤ |x| ≤ j + 1}`, which are bounded and locally finite and cover `ℝⁿ`, choose
  -- closed `F j ⊆ A ∩ K j` with `Lⁿ((A ∩ K j) ∖ F j) < η j`, `∑ η j < δ`; `⋃ j, F j` is closed.
  have hreg : ∀ A : Set (Eucl n), MeasurableSet A → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ A, IsClosed F ∧ (volume : Measure (Eucl n)) (A \ F) < δ := by
    intro A hA δ hδ
    obtain ⟨η, hη0, hηδ⟩ := ENNReal.exists_pos_sum_of_countable hδ ℕ
    set K : ℕ → Set (Eucl n) := fun j => (fun x : Eucl n => ‖x‖) ⁻¹' Icc (j : ℝ) (j + 1)
    have hKc : ∀ j, IsClosed (K j) := fun j => isClosed_Icc.preimage continuous_norm
    have hKb : ∀ j, K j ⊆ closedBall 0 (j + 1) := by
      intro j x hx
      rw [mem_closedBall, dist_zero_right]
      exact hx.2
    have hKcov : ∀ x : Eucl n, x ∈ K ⌊‖x‖⌋₊ := fun x =>
      ⟨Nat.floor_le (norm_nonneg x), (Nat.lt_floor_add_one _).le⟩
    -- `B₁(x)` meets `K j` only if `j ≤ |y| < |x| + 1` for some `y`.
    have hKlf : LocallyFinite K := by
      intro x
      refine ⟨ball x 1, ball_mem_nhds x one_pos, (Set.finite_lt_nat (⌊‖x‖⌋₊ + 2)).subset ?_⟩
      rintro j ⟨y, hyK, hyx⟩
      have h1 : (j : ℝ) ≤ ‖y‖ := hyK.1
      have h2 : ‖y‖ < ‖x‖ + 1 := by
        have hd : ‖y - x‖ < 1 := by rw [← dist_eq_norm]; exact mem_ball.1 hyx
        have := norm_le_norm_add_norm_sub' y x
        linarith [norm_sub_rev y x]
      have h3 : ‖x‖ < ⌊‖x‖⌋₊ + 1 := Nat.lt_floor_add_one _
      have h4 : (j : ℝ) < ((⌊‖x‖⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h4
    have hfin : ∀ j, (volume : Measure (Eucl n)) (A ∩ K j) ≠ ⊤ := fun j =>
      ((measure_mono (inter_subset_right.trans (hKb j))).trans_lt measure_closedBall_lt_top).ne
    choose F hFA hFc hFlt using fun j =>
      (hA.inter (hKc j).measurableSet).exists_isClosed_sdiff_lt (hfin j)
        (ENNReal.coe_ne_zero.2 (hη0 j).ne')
    refine ⟨⋃ j, F j, iUnion_subset fun j => (hFA j).trans inter_subset_left,
      (hKlf.subset fun j => (hFA j).trans inter_subset_right).isClosed_iUnion hFc, ?_⟩
    calc (volume : Measure (Eucl n)) (A \ ⋃ j, F j)
        ≤ volume (⋃ j, (A ∩ K j) \ F j) := by
          refine measure_mono fun x hx => mem_iUnion.2 ⟨⌊‖x‖⌋₊, ⟨hx.1, hKcov x⟩, fun hxF => ?_⟩
          exact hx.2 (mem_iUnion.2 ⟨_, hxF⟩)
      _ ≤ ∑' j, volume ((A ∩ K j) \ F j) := measure_iUnion_le _
      _ ≤ ∑' j, (η j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => (hFlt j).le
      _ < δ := hηδ
  -- Lusin's theorem through a countable basis `(b k)` of the second countable space `(ℝⁿ)*`:
  -- closed `F k ⊆ S ∩ f⁻¹(b k)` and `G k ⊆ S ∖ f⁻¹(b k)` with defects `< η k`, `∑ η k < ε / 2`,
  -- and `C = ⋂ k, (F k ∪ G k)`.
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (Eucl n →L[ℝ] ℝ)
  have hbo : ∀ k, IsOpen (b k) := fun k => hb.isOpen (mem_range_self k)
  obtain ⟨η, hη0, hηε⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε.ne').ne' ℕ
  have hη : ∀ k, ((η k : ℝ≥0) : ℝ≥0∞) ≠ 0 := fun k => ENNReal.coe_ne_zero.2 (hη0 k).ne'
  choose F hFE hFc hFlt using fun k =>
    hreg _ (hS.inter (hf (hbo k).measurableSet)) (η k) (hη k)
  choose G hGE hGc hGlt using fun k =>
    hreg _ (hS.diff (hf (hbo k).measurableSet)) (η k) (hη k)
  refine ⟨⋂ k, (F k ∪ G k), isClosed_iInter fun k => (hFc k).union (hGc k), ?_, ?_, ?_⟩
  · exact (iInter_subset _ 0).trans
      (union_subset ((hFE 0).trans inter_subset_left) ((hGE 0).trans Set.sdiff_subset))
  -- `S ∖ C ⊆ ⋃ k, ((S ∩ f⁻¹(b k)) ∖ F k ∪ (S ∖ f⁻¹(b k)) ∖ G k)`.
  · calc (volume : Measure (Eucl n)) (S \ ⋂ k, (F k ∪ G k))
        ≤ volume (⋃ k, ((S ∩ f ⁻¹' b k) \ F k ∪ (S \ f ⁻¹' b k) \ G k)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨k, hk⟩ : ∃ k, x ∉ F k ∪ G k := by
            by_contra! h
            exact hx.2 (mem_iInter.2 h)
          refine mem_iUnion.2 ⟨k, ?_⟩
          by_cases hxb : f x ∈ b k
          · exact Or.inl ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inl h)⟩
          · exact Or.inr ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inr h)⟩
      _ ≤ ∑' k, volume ((S ∩ f ⁻¹' b k) \ F k ∪ (S \ f ⁻¹' b k) \ G k) := measure_iUnion_le _
      _ ≤ ∑' k, ((η k : ℝ≥0∞) + η k) := ENNReal.tsum_le_tsum fun k =>
          (measure_union_le _ _).trans (add_le_add (hFlt k).le (hGlt k).le)
      _ = ∑' k, (η k : ℝ≥0∞) + ∑' k, (η k : ℝ≥0∞) := ENNReal.tsum_add
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hηε hηε
      _ = ε := ENNReal.add_halves ε
  -- `f⁻¹(b k) ∩ C = (G k)ᶜ ∩ C` is relatively open in `C` for every basic open set `b k`.
  · rw [hb.continuousOn_iff]
    rintro t ⟨k, rfl⟩
    refine ⟨(G k)ᶜ, (hGc k).isOpen_compl, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hxb, hxC⟩
      exact ⟨fun hxG => ((hGE k) hxG).2 hxb, hxC⟩
    · rintro ⟨hxG, hxC⟩
      refine ⟨?_, hxC⟩
      rcases mem_iInter.1 hxC k with hxF | hxG'
      · exact ((hFE k) hxF).2
      · exact absurd hxG' hxG
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
/-- Whitney's `C¹` extension theorem (Simon Ch. 2, Theorem 1.6), with derivatives as continuous
linear maps: if `A ⊆ ℝⁿ` is closed and `f`, `τ` are continuous on `A` with the compact-uniform
Taylor condition, then some `C¹` function `h` agrees with `f` on `A` and has derivative `τ a` at
every `a ∈ A`.  Standard construction (Evans–Gariepy §6.5): Whitney radius
`r = min(1, dist(·, A)) / 100`, a Vitali family of disjoint balls `B(c, r c)` whose fourfold
enlargements cover `ℝⁿ ∖ A`, uniformly bounded overlap, rescaled bumps normalized to a partition
of unity `w_c` with `∑ ‖Dw_c(x)‖ ≤ M / r x`, and `h = ∑ w_c P_{q c}` off `A`, where
`P_b(y) = f b + τ b (y - b)` and `q c ∈ A` is a nearest point.  The steps follow the pinned
SimonGMT proof `Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney` (whose
module is not imported here), inlined. -/
theorem Submission.lpf_c1r_whitney_extension :
    ∀ (n : ℕ) (A : Set (Eucl n)) (f : Eucl n → ℝ) (τ : Eucl n → (Eucl n →L[ℝ] ℝ)),
      IsClosed A → ContinuousOn f A → ContinuousOn τ A →
      (∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧
        ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - τ x (y - x)‖ ≤ δ * ‖y - x‖) →
      ∃ h : Eucl n → ℝ, ContDiff ℝ 1 h ∧ ∀ a ∈ A, h a = f a ∧ HasFDerivAt h (τ a) a := by
  intro n A f τ hA _hf hτ hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, fun a ha => absurd ha (notMem_empty a)⟩
  -- Step 1: local uniform Taylor estimate near each point of `A`.
  have hloc : ∀ a ∈ A, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖τ b - τ a‖ ≤ ε) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖f c - f b - τ b (c - b)‖ ≤ ε * ‖c - b‖ := by
    intro a ha ε hε
    obtain ⟨ρ, hρ, hρrem⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left ε hε
    obtain ⟨η, hη, hD⟩ := Metric.continuousWithinAt_iff.mp (hτ a ha) ε hε
    have hδ1 : min 1 (min η (ρ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η (ρ / 3)) ≤ η := (min_le_right _ _).trans (min_le_left _ _)
    have hδρ : min 1 (min η (ρ / 3)) ≤ ρ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η (ρ / 3)), lt_min one_pos (lt_min hη (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      have h1 := hD hb (hba.trans_le hδη)
      rw [dist_eq_norm] at h1
      exact h1.le
    · intro b hb hba c hc hca
      refine hρrem b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc ?_
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- Affine jets `P b y = f b + τ b (y - b)`.
  obtain ⟨P, hPdef⟩ : ∃ P : Eucl n → Eucl n → ℝ, ∀ b y, P b y = f b + τ b (y - b) :=
    ⟨fun b y => f b + τ b (y - b), fun _ _ => rfl⟩
  have P_sub : ∀ a b y, ‖P b y - P a y‖ ≤
      ‖f b - f a - τ a (b - a)‖ + ‖τ b - τ a‖ * ‖y - b‖ := by
    intro a b y
    have hid : P b y - P a y = (f b - f a - τ a (b - a)) + (τ b - τ a) (y - b) := by
      have hy : y - a = (y - b) + (b - a) := by abel
      simp only [hPdef, hy, map_add, sub_apply]
      ring
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((τ b - τ a).le_opNorm (y - b)))
  have P_deriv : ∀ b y, HasFDerivAt (P b) (τ b) y := by
    intro b y
    have e : P b = fun y => f b + (τ b y - τ b b) := by
      funext y
      rw [hPdef, map_sub]
    rw [e]
    exact ((τ b).hasFDerivAt.sub_const (τ b b)).const_add (f b)
  have P_cd : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    have e : P b = fun y => f b + τ b (y - b) := funext (hPdef b)
    rw [e]
    exact contDiff_const.add ((τ b).contDiff.comp (contDiff_id.sub contDiff_const))
  -- Step 2: the Whitney radius `r x = min 1 (dist x A) / 100`.
  obtain ⟨r, hr⟩ : ∃ r : Eucl n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨fun x => min 1 (infDist x A) / 100, fun _ => rfl⟩
  have r_nonneg : ∀ x, 0 ≤ r x := by
    intro x
    rw [hr]
    exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have r_le : ∀ x, r x ≤ 1 / 100 := by
    intro x
    rw [hr]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have r_le_inf : ∀ x, 100 * r x ≤ infDist x A := by
    intro x
    rw [hr]
    linarith [min_le_right (1 : ℝ) (infDist x A)]
  have r_pos : ∀ x, x ∉ A → 0 < r x := by
    intro x hx
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have r_le_add : ∀ x y, r x ≤ r y + dist x y / 100 := by
    intro x y
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [hr, hr]
    linarith
  have r_near : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := r_le_add x c
    have h₂ := r_le_add c x
    rw [dist_comm c x] at h₂
    have hx := r_nonneg x
    have hc := r_nonneg c
    exact ⟨by linarith, by linarith, by linarith⟩
  have r_scale : ∀ x, infDist x A ≤ 1 → infDist x A = 100 * r x := by
    intro x hx
    rw [hr, min_eq_right hx]
    ring
  have notMem_of_near : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA
    have hi := infDist_le_dist_of_mem (x := x) hyA
    rw [dist_comm x y] at hi
    linarith [r_le_inf x, r_nonneg x]
  -- Step 3: Vitali selection of disjoint Whitney balls covering `Aᶜ` fourfold.
  obtain ⟨Z, hZA, hZd, hZc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    Aᶜ (fun x : Eucl n => x) r (1 / 100) (fun x _ => r_le x) 4 (by norm_num)
  have Z_cov : ∀ x, x ∉ A → ∃ c ∈ Z, dist x c < 4 * r c := by
    intro x hx
    obtain ⟨c, hcZ, hxc⟩ := hZc x hx
    exact ⟨c, hcZ, hxc (mem_ball_self (r_pos x hx))⟩
  have Z_sep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      rw [mem_ball, dist_comm]
      exact lt_of_not_ge hlt
    have hdd : d ∈ ball d (r d) := mem_ball_self (r_pos d (hZA hd))
    exact Set.disjoint_left.mp (hZd hc hd hcd) hdc hdd
  -- Step 4: bounded overlap, via a uniform packing bound in `closedBall 0 21`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Eucl n), s ⊆ closedBall 0 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Eucl n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hsep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Eucl n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Function.Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Eucl n) ≠ (y : Eucl n) := fun h => hxy' (Subtype.ext h)
      have hd := hsep x.property y.property hne'
      have htri := dist_triangle (x : Eucl n) (c x : Eucl n) (y : Eucl n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Eucl n) (c x : Eucl n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  have hover : ∀ x, x ∉ A →
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
        {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := r_pos x hx
    let sc : Eucl n → Eucl n := fun c => (r x)⁻¹ • (c - x)
    have hsc : Function.Injective sc := by
      intro c d hcd
      have h := congrArg (fun z : Eucl n => r x • z) hcd
      simpa [sc, smul_smul, hrx.ne'] using h
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖sc c‖ ≤ 21 := by
      intro c hc
      have hd := (r_near x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      dsimp [sc]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep : (sc '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun h => hcd (congrArg sc h)
      have hdist := Z_sep c hc.1 d hd.1 hcd'
      have hrad := (r_near x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        rw [← dist_eq_norm]
        exact hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      dsimp [sc]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : sc '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Eucl n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      exact hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep
    exact ⟨hfin.of_finite_image hsc.injOn, by rwa [Set.ncard_image_of_injective _ hsc] at hcard⟩
  -- The finite sets `S x` of centres near `x`.
  have hSex : ∀ x : Eucl n, ∃ s : Finset Z, x ∉ A →
      (∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun h => absurd hx h⟩
    · obtain ⟨hT, hTN⟩ := hover x hx
      have hU : {c : Z | dist x c ≤ r x + 10 * r c}.Finite :=
        (hT.preimage Subtype.val_injective.injOn).subset (fun c hc => ⟨c.2, hc⟩)
      refine ⟨hU.toFinset, fun _ => ⟨fun c => by simp, ?_⟩⟩
      rw [← Set.ncard_eq_toFinset_card _ hU,
        ← Set.ncard_image_of_injective _ Subtype.val_injective]
      refine le_trans (Set.ncard_le_ncard ?_ hT) hTN
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
  choose S hS using hSex
  -- Step 5: rescaled bumps `bp c y = b0 ((y - c) / r c)`, with `b0 = 1` on `B̄(0, 4)` and
  -- `b0 = 0` off `B(0, 8)`.
  obtain ⟨b0, hb0in, hb0out⟩ : ∃ b0 : ContDiffBump (0 : Eucl n), b0.rIn = 4 ∧ b0.rOut = 8 :=
    ⟨⟨4, 8, by norm_num, by norm_num⟩, rfl, rfl⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b0.hasCompactSupport
    (b0.contDiff (n := 1)) (by simp)
  obtain ⟨bp, hbp⟩ : ∃ bp : Z → Eucl n → ℝ, ∀ c y, bp c y = b0 ((r c)⁻¹ • (y - c)) :=
    ⟨fun c y => b0 ((r c)⁻¹ • (y - c)), fun _ _ => rfl⟩
  have bp_cd : ∀ c, ContDiff ℝ 1 (bp c) := by
    intro c
    have e : bp c = fun y => b0 ((r c)⁻¹ • (y - c)) := funext (hbp c)
    rw [e]
    exact (b0.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).const_smul _)
  have bp_nonneg : ∀ c y, 0 ≤ bp c y := by
    intro c y
    rw [hbp]
    exact b0.nonneg
  have bp_le_one : ∀ c y, bp c y ≤ 1 := by
    intro c y
    rw [hbp]
    exact b0.le_one
  have bp_one : ∀ (c : Z) (y : Eucl n), dist y c ≤ 4 * r c → bp c y = 1 := by
    intro c y hy
    have hc : 0 < r c := r_pos c (hZA c.2)
    rw [hbp]
    apply b0.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le),
      hb0in]
    rw [dist_eq_norm] at hy
    calc (r c)⁻¹ * ‖y - c‖ ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have bp_zero : ∀ (c : Z) (y : Eucl n), 8 * r c ≤ dist y c → bp c y = 0 := by
    intro c y hy
    have hc : 0 < r c := r_pos c (hZA c.2)
    rw [hbp]
    apply Function.notMem_support.mp
    rw [b0.support_eq, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hc.le), hb0out, not_lt]
    rw [dist_eq_norm] at hy
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * ‖y - c‖ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, bp_der⟩ : ∃ B : ℝ, 0 < B ∧
      ∀ (c : Z) (y : Eucl n), ‖fderiv ℝ (bp c) y‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c y => ?_⟩
    have hc : 0 < r c := r_pos c (hZA c.2)
    let ρ : ℝ≥0 := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Eucl n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (bp c) := by
      have e : bp c = b0 ∘ (fun y : Eucl n => (r c)⁻¹ • (y - c)) := funext (hbp c)
      rw [e]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := y)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (bp c) y‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- Step 6: the partition of unity `w c = bp c / sm`, `sm = ∑ᶠ c, bp c`, on `Aᶜ`.
  have bp_far : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c : Z, c ∉ S x → bp c y = 0 := by
    intro x hx y hy c hc
    apply bp_zero c y
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun h => hc (((hS x hx).1 c).mpr h)
    have ht := dist_triangle x y (c : Eucl n)
    rw [dist_comm x y] at ht
    have := r_nonneg c
    linarith
  obtain ⟨sm, hsm⟩ : ∃ sm : Eucl n → ℝ, ∀ y, sm y = ∑ᶠ c : Z, bp c y :=
    ⟨fun y => ∑ᶠ c : Z, bp c y, fun _ => rfl⟩
  have sm_eq : ∀ x, x ∉ A → ∀ y, dist y x < r x → sm y = ∑ c ∈ S x, bp c y := by
    intro x hx y hy
    rw [hsm]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra h
    exact hc (bp_far x hx y hy c h)
  have sm_ge : ∀ x, x ∉ A → 1 ≤ sm x := by
    intro x hx
    have hrx := r_pos x hx
    rw [sm_eq x hx x (by rw [dist_self]; exact hrx)]
    obtain ⟨c, hcZ, hxc⟩ := Z_cov x hx
    have hi : (⟨c, hcZ⟩ : Z) ∈ S x := by
      rw [(hS x hx).1]
      have := r_nonneg c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = bp ⟨c, hcZ⟩ x := (bp_one ⟨c, hcZ⟩ x hxc.le).symm
      _ ≤ ∑ c ∈ S x, bp c x :=
          Finset.single_le_sum (f := fun c : Z => bp c x) (fun c _ => bp_nonneg c x) hi
  have sm_cd : ∀ x, x ∉ A → ContDiffAt ℝ 1 sm x := by
    intro x hx
    have hs : ContDiff ℝ 1 (fun y => ∑ c ∈ S x, bp c y) := ContDiff.sum (fun c _ => bp_cd c)
    apply hs.contDiffAt.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
    exact sm_eq x hx y hy
  have sm_fderiv : ∀ x, x ∉ A → fderiv ℝ sm x = ∑ c ∈ S x, fderiv ℝ (bp c) x := by
    intro x hx
    have heq : sm =ᶠ[𝓝 x] (fun y => ∑ c ∈ S x, bp c y) := by
      filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
      exact sm_eq x hx y hy
    rw [heq.fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (bp_cd c).differentiable one_ne_zero x)
  obtain ⟨w, hw⟩ : ∃ w : Z → Eucl n → ℝ, ∀ c y, w c y = bp c y / sm y :=
    ⟨fun c y => bp c y / sm y, fun _ _ => rfl⟩
  have w_cd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    have e : w c = bp c / sm := funext (hw c)
    rw [e]
    exact (bp_cd c).contDiffAt.div (sm_cd x hx) (ne_of_gt (lt_of_lt_of_le one_pos (sm_ge x hx)))
  have w_nonneg : ∀ c x, x ∉ A → 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (bp_nonneg c x) (zero_le_one.trans (sm_ge x hx))
  have w_zero : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c : Z, c ∉ S x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, bp_far x hx y hy c hc, zero_div]
  have w_sum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ S x, w c y = 1 := by
    intro x hx y hy
    have hyA := notMem_of_near x hx y hy
    simp only [hw, ← Finset.sum_div, ← sm_eq x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (sm_ge y hyA)))
  have w_dsum : ∀ x, x ∉ A → ∑ c ∈ S x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ S x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
      exact w_sum x hx y hy
    have hh := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh
    rw [fderiv_fun_sum (fun c _ => (w_cd c x hx).differentiableAt one_ne_zero)] at hh
    exact hh
  -- Step 7: `‖D w_c‖ ≤ ‖D bp_c‖ + ‖D sm‖` and the summed bound `M / r x`.
  have w_der : ∀ c x, x ∉ A →
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (bp c) x‖ + ‖fderiv ℝ sm x‖ := by
    intro c x hx
    have hS1 : 1 ≤ sm x := sm_ge x hx
    have hSpos : 0 < sm x := lt_of_lt_of_le one_pos hS1
    have hSi : (sm x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1
    have hSi2 : (sm x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ sm x ^ 2 by nlinarith)
    have hb := ((bp_cd c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((sm_cd x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x) + (sm x)⁻¹ • fderiv ℝ (bp c) x := by
      have e : w c = fun y => bp c y * ((fun t : ℝ => t⁻¹) ∘ sm) y := by
        funext y
        rw [hw, div_eq_mul_inv]
        rfl
      rw [e]
      exact hprod.fderiv
    rw [hder]
    have hb0 := bp_nonneg c x
    have hb1 := bp_le_one c x
    calc ‖bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x) + (sm x)⁻¹ • fderiv ℝ (bp c) x‖
        ≤ ‖bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x)‖ + ‖(sm x)⁻¹ • fderiv ℝ (bp c) x‖ :=
          norm_add_le _ _
      _ = bp c x * ((sm x ^ 2)⁻¹ * ‖fderiv ℝ sm x‖) + (sm x)⁻¹ * ‖fderiv ℝ (bp c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (sm x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (bp c) x‖ + ‖fderiv ℝ sm x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (bp c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ sm x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (sm x))) (norm_nonneg (fderiv ℝ sm x)))
          linarith
  obtain ⟨M, hM, w_dbound⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x, x ∉ A →
      ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := r_pos x hx
    have hT : 0 ≤ 2 * B / r x := by positivity
    have hb' : ∀ c ∈ S x, ‖fderiv ℝ (bp c) x‖ ≤ 2 * B / r x := by
      intro c hc
      have hlow := (r_near x c (((hS x hx).1 c).mp hc)).1
      refine (bp_der c x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = 2 * B / r x := by ring
    have hcard : ((S x).card : ℝ) ≤ N := by exact_mod_cast (hS x hx).2
    have hsum : ‖fderiv ℝ sm x‖ ≤ (N : ℝ) * (2 * B / r x) := by
      rw [sm_fderiv x hx]
      calc ‖∑ c ∈ S x, fderiv ℝ (bp c) x‖ ≤ ∑ c ∈ S x, ‖fderiv ℝ (bp c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ S x, 2 * B / r x := Finset.sum_le_sum hb'
        _ = ((S x).card : ℝ) * (2 * B / r x) := by simp
        _ ≤ (N : ℝ) * (2 * B / r x) := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ S x, ‖fderiv ℝ (w c) x‖ ≤ 2 * B / r x + (N : ℝ) * (2 * B / r x) :=
      fun c hc => (w_der c x hx).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖
        ≤ ∑ _c ∈ S x, (2 * B / r x + (N : ℝ) * (2 * B / r x)) := Finset.sum_le_sum hw'
      _ = ((S x).card : ℝ) * (2 * B / r x + (N : ℝ) * (2 * B / r x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * B / r x + (N : ℝ) * (2 * B / r x)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * (2 * B / r x) := by
          nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by ring
  -- Step 8: nearest-point anchors.
  choose q hqA hqd using fun x => hA.exists_infDist_eq_dist hne x
  have q_le : ∀ x a, a ∈ A → dist x (q x) ≤ dist x a := by
    intro x a ha
    rw [← hqd]
    exact infDist_le_dist_of_mem ha
  have q_pt : ∀ x a, a ∈ A → dist (q x) a ≤ 2 * dist x a := by
    intro x a ha
    have h1 := dist_triangle (q x) x a
    rw [dist_comm (q x) x] at h1
    linarith [q_le x a ha]
  have anchor1 : ∀ x, x ∉ A → ∀ c ∈ S x, dist x (q c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hc' := ((hS x hx).1 c).mp hc
    have hd := (r_near x c hc').2.2
    have hr' := r_le_inf x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Eucl n)) (y := x)
    have ht := dist_triangle x (c : Eucl n) (q c)
    rw [dist_comm (c : Eucl n) x] at hi
    rw [← hqd (c : Eucl n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have anchor2 : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ S x, dist (q c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := anchor1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (q c) x a
    rw [dist_comm (q c) x] at ht
    linarith
  -- Convex combinations of vectors of norm `≤ b` have norm `≤ b`.
  have convex_le : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Finset Z)
      (u : Z → ℝ) (v : Z → F) (b : ℝ), (∀ i ∈ s, 0 ≤ u i) → ∑ i ∈ s, u i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, u i • v i‖ ≤ b := by
    intro F _ _ s u v b hu hs hv
    calc ‖∑ i ∈ s, u i • v i‖ ≤ ∑ i ∈ s, ‖u i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, u i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (hu i hi)]
      _ ≤ ∑ i ∈ s, u i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (hu i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- Step 9: the extension.
  obtain ⟨g, hg⟩ : ∃ g : Eucl n → ℝ,
      ∀ y, g y = if y ∈ A then f y else ∑ᶠ c : Z, w c y * P (q c) y :=
    ⟨fun y => if y ∈ A then f y else ∑ᶠ c : Z, w c y * P (q c) y, fun _ => rfl⟩
  have g_on : ∀ a ∈ A, g a = f a := by
    intro a ha
    rw [hg, ite_eq_left ha]
  have g_near : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ S x, w c y * P (q c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (notMem_of_near x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (q c) y = 0
    rw [w_zero x hx y hy c hc', zero_mul]
  have g_ev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] (fun y => ∑ c ∈ S x, w c y * P (q c) y) := by
    intro x hx
    filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
    exact g_near x hx y hy
  have g_cd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ S x, w c y * P (q c) y) x :=
      ContDiffAt.sum (fun c _ => (w_cd c x hx).mul (P_cd _).contDiffAt)
    exact hs.congr_of_eventuallyEq (g_ev x hx)
  have g_fderiv : ∀ x, x ∉ A → fderiv ℝ g x =
      ∑ c ∈ S x, (w c x • τ (q c) + P (q c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(g_ev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((w_cd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (P_deriv _ x)
  have g_sub : ∀ a x, x ∉ A → g x - P a x = ∑ c ∈ S x, w c x * (P (q c) x - P a x) := by
    intro a x hx
    have hx' : dist x x < r x := by
      rw [dist_self]
      exact r_pos x hx
    rw [g_near x hx x hx']
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, w_sum x hx x hx', one_mul]
  -- Step 10: `g` has derivative `τ a` at every `a ∈ A`.
  have g_deriv : ∀ a ∈ A, HasFDerivAt g (τ a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, _hδ1, hD, hR⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by
      rw [dist_self]
      exact hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [g_on a ha]
    by_cases hxA : x ∈ A
    · rw [g_on x hxA]
      have hr' := hR a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hid : g x - f a - τ a (x - a) = g x - P a x := by
        rw [hPdef a x]
        ring
      rw [hid, g_sub a x hxA]
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact r_pos x hxA
      have key := convex_le ℝ (S x) (fun c => w c x) (fun c => P (q c) x - P a x) (ε * ‖x - a‖)
        (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') ?_
      · simpa only [smul_eq_mul] using key
      intro c hc
      have hbA : q c ∈ A := hqA c
      have hba : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
      have hxb : dist x (q c) ≤ 2 * dist x a :=
        (anchor1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (q c) a < δ := by linarith
      have hDb := hD (q c) hbA hbaδ
      have hr' := hR a ha haa (q c) hbA hbaδ
      have hba' : ‖q c - a‖ ≤ 3 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hba
      have hxb' : ‖x - q c‖ ≤ 2 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hxb
      calc ‖P (q c) x - P a x‖
          ≤ ‖f (q c) - f a - τ a (q c - a)‖ + ‖τ (q c) - τ a‖ * ‖x - q c‖ := P_sub a (q c) x
        _ ≤ (ε / 5) * ‖q c - a‖ + (ε / 5) * ‖x - q c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  have g_fderiv_on : ∀ a ∈ A, fderiv ℝ g a = τ a := fun a ha => (g_deriv a ha).fderiv
  -- Step 11: `Dg` is continuous at every `a ∈ A`.
  have g_cont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    have hK : (0 : ℝ) < 1 + 700 * M := by positivity
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by
      rw [hηdef]
      field_simp
    have hηε : η ≤ ε / 2 := by nlinarith
    obtain ⟨δ, hδ, hδ1, hD, hR⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [g_fderiv_on a ha, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [g_fderiv_on x hxA]
      exact (hD x hxA (by linarith)).trans hηε
    · have hrx := r_pos x hxA
      have hbA : q x ∈ A := hqA x
      have hba : dist (q x) a ≤ 2 * dist x a := q_pt x a ha
      have hbaδ : dist (q x) a < δ := by linarith
      have hDb := hD (q x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := r_scale x hdx
      have hD' : ∀ c ∈ S x, ‖τ (q c) - τ a‖ ≤ η := by
        intro c hc
        apply hD _ (hqA c)
        have hi := anchor2 x hxA a ha c hc
        linarith
      have hP' : ∀ c ∈ S x, ‖P (q c) x - P (q x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA : q c ∈ A := hqA c
        have hda : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
        have hdaδ : dist (q c) a < δ := by linarith
        have hxd : dist x (q c) ≤ 2 * infDist x A := anchor1 x hxA c hc
        have hxb : dist x (q x) = infDist x A := (hqd x).symm
        have hdb : dist (q c) (q x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (q c) x (q x)
          rw [dist_comm (q c) x, hxb] at ht
          linarith
        have hDd : ‖τ (q c) - τ (q x)‖ ≤ 2 * η := by
          calc ‖τ (q c) - τ (q x)‖ = ‖(τ (q c) - τ a) - (τ (q x) - τ a)‖ := by
                congr 1
                abel
            _ ≤ ‖τ (q c) - τ a‖ + ‖τ (q x) - τ a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hR (q x) hbA hbaδ (q c) hdA hdaδ
        have hdb' : ‖q c - q x‖ ≤ 3 * infDist x A := by
          rw [← dist_eq_norm]
          exact hdb
        have hxd' : ‖x - q c‖ ≤ 2 * infDist x A := by
          rw [← dist_eq_norm]
          exact hxd
        calc ‖P (q c) x - P (q x) x‖
            ≤ ‖f (q c) - f (q x) - τ (q x) (q c - q x)‖ + ‖τ (q c) - τ (q x)‖ * ‖x - q c‖ :=
              P_sub (q x) (q c) x
          _ ≤ η * ‖q c - q x‖ + (2 * η) * ‖x - q c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by
              rw [hscale]
              ring
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact hrx
      have hdecomp : fderiv ℝ g x - τ a =
          (∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x := by
        rw [g_fderiv x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, w_sum x hxA x hx', w_dsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hdecomp]
      calc ‖(∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ S x, w c x • (τ (q c) - τ a)‖ +
            ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact convex_le _ (S x) (fun c => w c x) (fun c => τ (q c) - τ a) η
                (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') hD'
            · calc ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ S x, ‖(P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_sum_le _ _
                _ ≤ ∑ c ∈ S x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (w_dbound x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by
            field_simp
        _ = ε / 2 := heq
  -- Step 12: conclusion.
  refine ⟨g, ?_, fun a ha => ⟨g_on a ha, g_deriv a ha⟩⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (g_deriv x hx).differentiableAt
    · exact (g_cd x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact g_cont x hx
    · exact (g_cd x hx).continuousAt_fderiv one_ne_zero

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42), in the form established by its
printed proof (p. 44): a Lipschitz `g : ℝⁿ → ℝ` agrees with a `C¹` function `h` on a closed set `A`
with `Lⁿ(ℝⁿ ∖ A) < ε`, and `g` is differentiable on `A` with `Dg = Dh` there.  Rademacher gives a
Borel set `D` of full measure where `g` is differentiable; Lusin gives a closed `C ⊆ D` with `Dg|C`
continuous; the `η_k` step gives a closed `A ⊆ C` satisfying Whitney's condition (‡) (Thm 1.6);
Whitney's extension theorem then gives `h`. -/
theorem Submission.lpf_c1_approximation_real :
    ∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧ (volume : Measure (Eucl n)) Aᶜ < ε ∧
        ContDiff ℝ 1 h ∧ ∀ x ∈ A, g x = h x ∧ HasFDerivAt g (fderiv ℝ h x) x := by
  intro n g K hg ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Rademacher: `g` is differentiable on the Borel set `D`, and `Lⁿ(ℝⁿ ∖ D) = 0`.
  set D : Set (Eucl n) := {x | DifferentiableAt ℝ g x}
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  have hDc : (volume : Measure (Eucl n)) Dᶜ = 0 := ae_iff.1 hg.ae_differentiableAt
  -- Lusin: a closed `C ⊆ D` with `Lⁿ(D ∖ C) < ε / 2` on which `Dg` is continuous.
  obtain ⟨C, hCc, hCD, hDC, hgC⟩ := Submission.lpf_c1r_lusin_closed n D (fderiv ℝ g) hDm
    (measurable_fderiv ℝ g) (ε / 2) hε2
  -- The `η_k` step: a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε / 2` satisfying Whitney's (‡) for
  -- `(g, Dg)`.
  obtain ⟨A, hAc, hAC, hCA, hrem⟩ := Submission.lpf_c1r_uniform_remainder n g K hg C hCc
    (fun x hx => hCD hx) hgC (ε / 2) hε2
  -- Whitney: a `C¹` function `h` with `h = g` and `Dh = Dg` on `A`.
  obtain ⟨h, hh, hhA⟩ := Submission.lpf_c1r_whitney_extension n A g (fderiv ℝ g) hAc
    hg.continuous.continuousOn (hgC.mono hAC) hrem
  refine ⟨A, h, hAc, ?_, hh, fun x hx => ?_⟩
  · -- `ℝⁿ ∖ A ⊆ (ℝⁿ ∖ D) ∪ (D ∖ C) ∪ (C ∖ A)`, so `Lⁿ(ℝⁿ ∖ A) < 0 + ε / 2 + ε / 2 = ε`.
    have hsub : Aᶜ ⊆ Dᶜ ∪ (D \ C) ∪ (C \ A) := by
      intro x hxA
      by_cases hxD : x ∈ D
      · by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        · exact Or.inl (Or.inr ⟨hxD, hxC⟩)
      · exact Or.inl (Or.inl hxD)
    calc (volume : Measure (Eucl n)) Aᶜ ≤ volume (Dᶜ ∪ (D \ C) ∪ (C \ A)) := measure_mono hsub
      _ ≤ volume Dᶜ + volume (D \ C) + volume (C \ A) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = volume (D \ C) + volume (C \ A) := by rw [hDc, zero_add]
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hDC hCA
      _ = ε := ENNReal.add_halves ε
  · -- `Dh(x) = Dg(x)` by uniqueness of the derivative, and `g` is differentiable at `x ∈ A ⊆ D`.
    obtain ⟨hhx, hDhx⟩ := hhA x hx
    rw [hDhx.fderiv]
    exact ⟨hhx.symm, DifferentiableAt.hasFDerivAt (hCD (hAC hx))⟩

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) for `ℝ^Q`-valued maps, applied
componentwise as in the proof of Ch. 6, Lemma 3.9 (p. 148): a Lipschitz `u : ℝⁿ → ℝ^Q` agrees
with a `C¹` map `G`, and has Fréchet derivative `DG(x)`, at every `x` of a closed set `A` with
`Lⁿ(ℝⁿ ∖ A) < ε`. -/
theorem Submission.lpf_c1_approximation_eucl :
    ∀ (n Q : ℕ) (u : Eucl n → Eucl Q) (K : ℝ≥0), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (G : Eucl n → Eucl Q), IsClosed A ∧
        (volume : Measure (Eucl n)) Aᶜ < ε ∧ ContDiff ℝ 1 G ∧
        ∀ x ∈ A, u x = G x ∧ HasFDerivAt u (fderiv ℝ G x) x := by
  intro n Q u K hu ε hε
  -- Split `ε`: `δ > 0` with `Q δ < ε`.
  obtain ⟨δ, hδ, hδQ⟩ := ENNReal.exists_pos_mul_lt (ENNReal.natCast_ne_top Q) hε.ne'
  -- The scalar theorem for each component `u_l = π_l ∘ u`, which is `‖π_l‖ K`-Lipschitz: a closed
  -- `A_l` with `Lⁿ(ℝⁿ ∖ A_l) < δ` and a `C¹` `h_l` with `u_l = h_l`, `Du_l = Dh_l` on `A_l`.
  have hcomp : ∀ l : Fin Q, ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧
      (volume : Measure (Eucl n)) Aᶜ < δ ∧ ContDiff ℝ 1 h ∧
      ∀ x ∈ A, u x l = h x ∧ HasFDerivAt (fun y => u y l) (fderiv ℝ h x) x := fun l =>
    Submission.lpf_c1_approximation_real n (fun y => u y l) _
      ((EuclideanSpace.proj (𝕜 := ℝ) l).lipschitzWith.comp hu) δ hδ
  choose A h hA hAδ hh hAh using hcomp
  -- Every `y ∈ ℝ^Q` is `∑_l y_l e_l`, `e_l = EuclideanSpace.single l 1`.
  have hsum : ∀ y : Eucl Q, ∑ l, y l • EuclideanSpace.single l (1 : ℝ) = y := fun y => by
    have hy := (EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr y
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hy
    exact hy
  -- `A = ⋂_l A_l` and `G = ∑_l h_l e_l`.
  refine ⟨⋂ l, A l, fun x => ∑ l, h l x • EuclideanSpace.single l (1 : ℝ), isClosed_iInter hA,
    ?_, ContDiff.sum fun l _ => (hh l).smul_const _, ?_⟩
  · -- `Lⁿ(ℝⁿ ∖ A) ≤ ∑_l Lⁿ(ℝⁿ ∖ A_l) ≤ Q δ < ε`.
    rw [compl_iInter]
    calc (volume : Measure (Eucl n)) (⋃ l, (A l)ᶜ)
        ≤ ∑ l, (volume : Measure (Eucl n)) (A l)ᶜ := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _l : Fin Q, δ := Finset.sum_le_sum fun l _ => (hAδ l).le
      _ = δ * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ < ε := hδQ
  · intro x hx
    rw [mem_iInter] at hx
    -- `G` and `u = ∑_l u_l e_l` both have derivative `Λ = ∑_l (Dh_l(x)).smulRight e_l` at `x`.
    have hG : HasFDerivAt (fun y => ∑ l, h l y • EuclideanSpace.single l (1 : ℝ))
        (∑ l, (fderiv ℝ (h l) x).smulRight (EuclideanSpace.single l (1 : ℝ))) x :=
      HasFDerivAt.fun_sum fun l _ =>
        ((hh l).differentiable one_ne_zero x).hasFDerivAt.smul_const _
    have hu' : HasFDerivAt (fun y => ∑ l, u y l • EuclideanSpace.single l (1 : ℝ))
        (∑ l, (fderiv ℝ (h l) x).smulRight (EuclideanSpace.single l (1 : ℝ))) x :=
      HasFDerivAt.fun_sum fun l _ => (hAh l x (hx l)).2.smul_const _
    rw [show (fun y => ∑ l, u y l • EuclideanSpace.single l (1 : ℝ)) = u from
      funext fun y => hsum (u y)] at hu'
    refine ⟨?_, ?_⟩
    · rw [← hsum (u x)]
      exact Finset.sum_congr rfl fun l _ => by rw [(hAh l x (hx l)).1]
    · rw [hG.fderiv]
      exact hu'
/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9 (p. 148): the
inverse-function-theorem estimate.  If `G : ℝⁿ → ℝ^Q` is `C¹` and `DG(w)` is injective, then
`c |z − z'| ≤ |G z − G z'|` for all `z, z'` in some ball `B_r(w)`, with `c > 0`. -/
theorem Submission.lpf_c1_local_antilipschitz :
    ∀ (n Q : ℕ) (G : Eucl n → Eucl Q) (w : Eucl n), ContDiff ℝ 1 G →
      Function.Injective (fderiv ℝ G w) →
      ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ ball w r, ∀ z' ∈ ball w r,
        c * ‖z - z'‖ ≤ ‖G z - G z'‖ := by
  intro n Q G w hG hinj
  set A : Eucl n →L[ℝ] Eucl Q := fderiv ℝ G w
  -- `A` is injective on the finite-dimensional `ℝⁿ`, hence antilipschitz: `|v| ≤ K |A v|`,
  -- i.e. `|A v| ≥ m |v|` with `m = K⁻¹ > 0`.
  obtain ⟨K, hKpos, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q)).mp hinj
  have hK0 : (0 : ℝ) < K := hKpos
  have hm : ∀ v : Eucl n, (K : ℝ)⁻¹ * ‖v‖ ≤ ‖A v‖ := by
    intro v
    rw [inv_mul_le_iff₀ hK0]
    exact ZeroHomClass.bound_of_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q) hK v
  -- `c = m / 2`.  `A` is the strict derivative of `G` at `w`, so `G` approximates `A` with
  -- constant `c` on a neighbourhood of `w`, which contains a ball `B_r(w)`.
  set c : ℝ≥0 := K⁻¹ / 2 with hc
  have hc0 : 0 < c := by
    rw [hc]
    exact div_pos (inv_pos.mpr hKpos) two_pos
  have hcK : (c : ℝ) = (K : ℝ)⁻¹ / 2 := by
    rw [hc, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_two]
  have hstrict : HasStrictFDerivAt G A w := hG.hasStrictFDerivAt one_ne_zero
  obtain ⟨s, hs, happrox⟩ := hstrict.approximates_deriv_on_nhds (c := c) (Or.inr hc0)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r, hr, c, hc0, fun z hz z' hz' => ?_⟩
  -- On `B_r(w)`, `|G z − G z' − A (z − z')| ≤ c |z − z'|`; with the triangle inequality,
  -- `m |z − z'| ≤ |A (z − z')| ≤ |G z − G z'| + c |z − z'|`, and `m − c = c`.
  have h1 : ‖G z - G z' - A (z - z')‖ ≤ c * ‖z - z'‖ := happrox z (hrs hz) z' (hrs hz')
  have h2 := hm (z - z')
  have h3 : ‖A (z - z')‖ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := by
    calc ‖A (z - z')‖ = ‖(G z - G z') - (G z - G z' - A (z - z'))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := norm_sub_le _ _
  rw [hcK] at h1 ⊢
  linarith
/-- Countable localization of a locally Lipschitz map: open sets `B m ⊆ Ω` covering `Ω` and
globally Lipschitz maps `v m` agreeing with `u` on `B m` (Lindelöf, then Lipschitz extension). -/
theorem Submission.lpf_lipschitz_localization :
    ∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u →
      ∃ (B : ℕ → Set (Eucl n)) (v : ℕ → Eucl n → Eucl Q), (∀ m, IsOpen (B m)) ∧
        (∀ m, B m ⊆ Ω) ∧ Ω ⊆ ⋃ m, B m ∧ (∀ m, ∃ K : ℝ≥0, LipschitzWith K (v m)) ∧
        ∀ m, EqOn u (v m) (B m) := by
  intro n Q Ω u hΩ hu
  -- Each `w ∈ Ω` has an open neighbourhood `V w ⊆ Ω` on which `u` is Lipschitz.
  have hV : ∀ w : Ω, ∃ V : Set (Eucl n), IsOpen V ∧ V ⊆ Ω ∧ (w : Eucl n) ∈ V ∧
      ∃ K : ℝ≥0, LipschitzOnWith K u V := by
    rintro ⟨w, hw⟩
    obtain ⟨K, t, ht, hK⟩ := hu hw
    obtain ⟨o, ho, hwo, hot⟩ := mem_nhdsWithin.1 ht
    exact ⟨o ∩ Ω, ho.inter hΩ, inter_subset_right, ⟨hwo, hw⟩, K, hK.mono hot⟩
  choose V hVo hVΩ hwV hVK using hV
  -- Lindelöf: countably many `V w` already cover `Ω`.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hΩT : Ω ⊆ ⋃ w ∈ T, V w := fun x hx => hTU ▸ mem_iUnion.2 ⟨⟨x, hx⟩, hwV _⟩
  -- Extend `u` from each `V w` to a globally Lipschitz map `g w`.
  have hext : ∀ w : Ω, ∃ g : Eucl n → Eucl Q, (∃ K : ℝ≥0, LipschitzWith K g) ∧
      EqOn u g (V w) := fun w => by
    obtain ⟨K, hK⟩ := hVK w
    obtain ⟨g, hg, hug⟩ := hK.extend_finite_dimension
    exact ⟨g, ⟨_, hg⟩, hug⟩
  choose g hg hug using hext
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- `T = ∅` forces `Ω = ∅`: take empty sets and the zero map.
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, fun _ => empty_subset _, ?_,
      fun _ => ⟨0, LipschitzWith.const 0⟩, fun _ => eqOn_empty _ _⟩
    simpa [hT] using hΩT
  · -- Enumerate the nonempty countable `T` as `range f`.
    obtain ⟨f, rfl⟩ := hTc.exists_eq_range hT
    refine ⟨fun m => V (f m), fun m => g (f m), fun m => hVo _, fun m => hVΩ _, ?_,
      fun m => hg _, fun m => hug _⟩
    rwa [biUnion_range] at hΩT

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) combined with the
inverse-function-theorem estimate of Ch. 3, Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9
(p. 148).  A map `u : ℝⁿ → ℝ^Q` that is locally Lipschitz on an open `Ω` agrees, together with its
derivative, with `C¹` maps `G_k` on pairwise disjoint Borel sets `E_k ⊆ O_k ∩ Ω`, where `G_k` is
antilipschitz on the open set `O_k`; and `Lⁿ`-a.e. point of `Ω` at which `u` has an injective
derivative lies in `⋃_k E_k`. -/
theorem Submission.lpf_lipschitz_c1_immersion_pieces :
    ∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u →
      ∃ (G : ℕ → Eucl n → Eucl Q) (O E : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧
        (∀ k, ContDiff ℝ 1 (G k)) ∧
        (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧
        (∀ k, MeasurableSet (E k)) ∧ (∀ k, E k ⊆ O k ∩ Ω) ∧
        Pairwise (Function.onFun Disjoint E) ∧
        (∀ k, ∀ w ∈ E k, u w = G k w ∧ HasFDerivAt u (fderiv ℝ (G k) w) w) ∧
        ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω →
          (∃ D : Eucl n →L[ℝ] Eucl Q, HasFDerivAt u D w ∧ Function.Injective D) →
            w ∈ ⋃ k, E k := by
  intro n Q Ω u hΩ hu
  -- Open sets `B m ⊆ Ω` covering `Ω`, and Lipschitz maps `v m` with `u = v m` on `B m`.
  obtain ⟨B, v, hBo, hBΩ, hΩB, hv, huv⟩ := Submission.lpf_lipschitz_localization n Q Ω u hΩ hu
  choose K hK using hv
  -- C¹ approximation of `v m` with `ε = 1 / i`: closed sets `A m i` with `Lⁿ(ℝⁿ ∖ A m i) < 1 / i`
  -- and `C¹` maps `G m i` with `v m = G m i` and `D(v m) = D(G m i)` on `A m i`.
  have happrox : ∀ m i : ℕ, ∃ (A : Set (Eucl n)) (G : Eucl n → Eucl Q), IsClosed A ∧
      (volume : Measure (Eucl n)) Aᶜ < (i : ℝ≥0∞)⁻¹ ∧ ContDiff ℝ 1 G ∧
      ∀ x ∈ A, v m x = G x ∧ HasFDerivAt (v m) (fderiv ℝ G x) x := fun m i =>
    Submission.lpf_c1_approximation_eucl n Q (v m) (K m) (hK m) _
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
  choose A G hAc hA hG hAG using happrox
  -- On `B m ∩ A m i`, `u = G m i` and `Du = D(G m i)`, because `u = v m` on the open set `B m`.
  have huG : ∀ m i, ∀ w ∈ B m ∩ A m i, u w = G m i w ∧ HasFDerivAt u (fderiv ℝ (G m i) w) w := by
    rintro m i w ⟨hwB, hwA⟩
    exact ⟨(huv m hwB).trans (hAG m i w hwA).1, (hAG m i w hwA).2.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem ((hBo m).mem_nhds hwB) (huv m))⟩
  -- A sequence `b j` of open sets forming a basis of the topology of `ℝⁿ`.
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (Eucl n)
  -- Index `k ↔ (m, i, j)`.  The triple is *good* when `b j ⊆ B m` and `G m i` is antilipschitz on
  -- `b j`; then `O k := b j`, otherwise `O k := ∅`.  `E' k := O k ∩ B m ∩ A m i`, and
  -- `E := disjointed E'`.
  classical
  let good : ℕ × ℕ × ℕ → Prop := fun t => b t.2.2 ⊆ B t.1 ∧
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ b t.2.2, ∀ w' ∈ b t.2.2, c * ‖w - w'‖ ≤ ‖G t.1 t.2.1 w - G t.1 t.2.1 w'‖
  let idx : ℕ → ℕ × ℕ × ℕ := fun k => ((Nat.unpair k).1, Nat.unpair (Nat.unpair k).2)
  let O : ℕ → Set (Eucl n) := fun k => if good (idx k) then b (idx k).2.2 else ∅
  let E' : ℕ → Set (Eucl n) := fun k => O k ∩ (B (idx k).1 ∩ A (idx k).1 (idx k).2.1)
  have hOo : ∀ k, IsOpen (O k) := by
    intro k
    by_cases h : good (idx k)
    · simp only [O, ite_eq_left h]
      exact hb.isOpen ⟨_, rfl⟩
    · simp only [O, ite_eq_right h]
      exact isOpen_empty
  have hE' : ∀ k, MeasurableSet (E' k) := fun k =>
    (hOo k).measurableSet.inter ((hBo _).measurableSet.inter (hAc _ _).measurableSet)
  refine ⟨fun k => G (idx k).1 (idx k).2.1, O, disjointed E', hOo, fun k => hG _ _, ?_,
    MeasurableSet.disjointed hE', ?_, disjoint_disjointed E', ?_, ?_⟩
  · -- `G k` is antilipschitz on `O k` (vacuously if `O k = ∅`).
    intro k
    by_cases h : good (idx k)
    · simp only [O, ite_eq_left h]
      exact h.2
    · simp only [O, ite_eq_right h]
      exact ⟨1, one_pos, fun w hw => absurd hw (notMem_empty w)⟩
  · -- `E k ⊆ E' k ⊆ O k ∩ B m ⊆ O k ∩ Ω`.
    intro k w hw
    have hw' : w ∈ E' k := disjointed_subset E' k hw
    exact ⟨hw'.1, hBΩ _ hw'.2.1⟩
  · intro k w hw
    have hw' : w ∈ E' k := disjointed_subset E' k hw
    exact huG _ _ w hw'.2
  · -- For each `m`, the points outside every `A m i` form a null set, as `Lⁿ(ℝⁿ ∖ A m i) < 1 / i`.
    have hnull : ∀ m, (volume : Measure (Eucl n)) (⋂ i, (A m i)ᶜ) = 0 := by
      intro m
      by_contra h
      obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt h
      exact lt_asymm hi ((measure_mono (iInter_subset _ i)).trans_lt (hA m i))
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_iUnion_null hnull)]
      with w hwN hwΩ hDw
    obtain ⟨D, hD, hDinj⟩ := hDw
    obtain ⟨m, hwm⟩ := mem_iUnion.1 (hΩB hwΩ)
    obtain ⟨i, hwi⟩ : ∃ i, w ∈ A m i := by
      by_contra h
      exact hwN (mem_iUnion.2 ⟨m, mem_iInter.2 fun i => mem_compl (not_exists.1 h i)⟩)
    -- `D = D(G m i)(w)` by uniqueness of the derivative, so `D(G m i)(w)` is injective.
    have hDG : D = fderiv ℝ (G m i) w := hD.unique (huG m i w ⟨hwm, hwi⟩).2
    rw [hDG] at hDinj
    -- `G m i` is antilipschitz on a ball `B_r(w)`, hence on a basis set `b j` with
    -- `w ∈ b j ⊆ B_r(w) ∩ B m`; so `(m, i, j)` is good and `w ∈ E' k` for `k ↔ (m, i, j)`.
    obtain ⟨r, hr, c, hc, hcr⟩ :=
      Submission.lpf_c1_local_antilipschitz n Q (G m i) w (hG m i) hDinj
    obtain ⟨_, ⟨j, rfl⟩, hwj, hjs⟩ := hb.exists_subset_of_mem_open
      (show w ∈ ball w r ∩ B m from ⟨mem_ball_self hr, hwm⟩) (isOpen_ball.inter (hBo m))
    have hk : idx (Nat.pair m (Nat.pair i j)) = (m, i, j) := by
      simp only [idx, Nat.unpair_pair]
    have hgood : good (m, i, j) :=
      ⟨fun z hz => (hjs hz).2, c, hc, fun z hz z' hz' => hcr z (hjs hz).1 z' (hjs hz').1⟩
    rw [iUnion_disjointed]
    refine mem_iUnion.2 ⟨Nat.pair m (Nat.pair i j), ?_⟩
    simp only [E', O, hk, ite_eq_left hgood]
    exact ⟨hwj, hwm, hwi⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
