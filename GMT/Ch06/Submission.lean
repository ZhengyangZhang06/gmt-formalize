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
/-- The coordinate wedge covectors are dual to the increasing basis tuples: the `J`-th coordinate
of `∑_I c_I dx^I` is `c_J`, i.e. `dx^I(e_{J(0)}, …, e_{J(k-1)}) = δ_{IJ}`. -/
theorem Submission.smr_ci_coord_sum_smul_wedge :
    ∀ (P k : ℕ) (c : SimonMultiIndex k P → ℝ) (J : SimonMultiIndex k P),
      euclideanCovectorCoordinate (∑ I : SimonMultiIndex k P,
        c I • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)) : Covector (Eucl P) k) J = c J := by
  intro P k c J
  classical
  -- Kronecker property: `dx^I (e_J) = δ_{IJ}`.
  have hK : ∀ I : SimonMultiIndex k P, wedgeCovectors k (fun j => EuclideanSpace.proj (I j))
      (fun j => EuclideanSpace.single (J j) (1 : ℝ)) = if I = J then 1 else 0 := by
    intro I
    rw [wedgeCovectors_apply_det]
    split_ifs with hIJ
    · -- the matrix `[δ_{I i, I j}]` is the identity
      subst hIJ
      convert Matrix.det_one (n := Fin k) (R := ℝ)
      ext i j
      simp [Matrix.one_apply, PiLp.single_apply, I.injective.eq_iff]
    · -- some `I i` is not among the `J j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra! h
        apply hIJ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range I ⊆ Set.range J := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range J)
        rw [Set.ncard_range_of_injective J.injective, Set.ncard_range_of_injective I.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  -- Evaluation at `e_J` is linear, so only the term `I = J` survives.
  rw [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
/-- A `k`-covector on `ℝ^P` whose coordinates `α(e_{I(0)}, …, e_{I(k-1)})` vanish for every
increasing multi-index `I` is zero. -/
theorem Submission.smr_ci_covector_eq_zero_of_coord :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k),
      (∀ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I = 0) → α = 0 := by
  intro P k α hα
  classical
  -- By extensionality on the standard basis it suffices to treat injective index tuples `v`.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.toAlternatingMap_zero,
    AlternatingMap.zero_apply]
  -- Sorting `v` gives an increasing multi-index `I` with `e_I = e_v ∘ σ`, `σ := Tuple.sort v`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  have h := hα (OrderEmbedding.ofStrictMono _ hsm)
  have heq : (fun j => EuclideanSpace.single (OrderEmbedding.ofStrictMono _ hsm j) (1 : ℝ)) =
      (fun i => EuclideanSpace.single (v i) (1 : ℝ)) ∘ Tuple.sort v := rfl
  -- `α(e_I) = sign σ • α(e_v)`, and the sign is a unit.
  rw [euclideanCovectorCoordinate, heq, ← ContinuousAlternatingMap.coe_toAlternatingMap α,
    AlternatingMap.map_perm] at h
  exact (smul_eq_zero_iff_eq _).mp h
/-- The Euclidean coefficient norm of a `k`-covector on `ℝ^P` is the `ℓ²`-norm of its coordinates
`α(e_{I(0)}, …, e_{I(k-1)})` over the increasing multi-indices `I : Fin k ↪o Fin P`. -/
theorem Submission.smr_ci_norm_eq_sqrt_sum_coord_sq :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k), covectorEuclideanNorm α =
      Real.sqrt (∑ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I ^ 2) := by
  intro P k α
  unfold covectorEuclideanNorm
  congr 1
  -- Drop the tuples that are not strictly increasing; their terms vanish.
  rw [← Finset.sum_filter]
  -- Reindex the strictly increasing tuples by the order embeddings, `I ↦ ⇑I`.
  symm
  refine Finset.sum_bij' (fun I _ => ⇑I)
    (fun f hf => OrderEmbedding.ofStrictMono f (Finset.mem_filter.1 hf).2)
    (fun I _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, I.strictMono⟩)
    (fun _ _ => Finset.mem_univ _) (fun I _ => ?_) (fun f _ => ?_) (fun I _ => ?_)
  · exact RelEmbedding.ext fun _ => rfl
  · exact OrderEmbedding.coe_ofStrictMono _
  · -- Matching summands: `basisFun i = EuclideanSpace.single i 1`.
    simp only [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]

/-- Simon (6.1.2)–(6.1.5): listing the coefficients `α(e_{I(0)}, …, e_{I(k-1)})` over the
increasing multi-indices `I` is a linear isomorphism `J` of the `k`-covectors on `ℝ^P` onto `ℝ^N`
with `|α| = ‖J α‖` for the Euclidean coefficient norm `|α| = covectorEuclideanNorm α`. -/
theorem Submission.smr_covector_coord_isometry :
    ∀ (P k : ℕ), ∃ (N : ℕ) (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖ := by
  intro P k
  -- Enumerate the increasing multi-indices `I : Fin k ↪o Fin P` by `Fin N`.
  let σ : Fin (Fintype.card (SimonMultiIndex k P)) ≃ SimonMultiIndex k P :=
    (Fintype.equivFin (SimonMultiIndex k P)).symm
  -- The coordinate map `J α = (α(e_{σ n}))_n`, linear because evaluation is.
  obtain ⟨J, hJ⟩ : ∃ J : Covector (Eucl P) k →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (SimonMultiIndex k P))),
      ∀ α n, J α n = euclideanCovectorCoordinate α (σ n) :=
    ⟨{ toFun := fun α => WithLp.toLp 2 fun n => euclideanCovectorCoordinate α (σ n)
       map_add' := fun α β => by
         ext n
         simp [euclideanCovectorCoordinate]
       map_smul' := fun c α => by
         ext n
         simp [euclideanCovectorCoordinate] }, fun _ _ => rfl⟩
  have hbij : Function.Bijective J := by
    refine ⟨(injective_iff_map_eq_zero J).2 fun α hα => ?_, fun y => ?_⟩
    · -- injective: a covector whose coordinates all vanish is zero
      refine Submission.smr_ci_covector_eq_zero_of_coord P k α fun I => ?_
      rw [← σ.apply_symm_apply I, ← hJ, hα, PiLp.zero_apply]
    · -- surjective: `∑_I y_{σ⁻¹ I} dx^I` has coordinates `y`
      refine ⟨∑ I : SimonMultiIndex k P,
        y (σ.symm I) • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)), ?_⟩
      ext n
      rw [hJ, Submission.smr_ci_coord_sum_smul_wedge, σ.symm_apply_apply]
  refine ⟨_, LinearEquiv.ofBijective J hbij, fun α => ?_⟩
  -- Both norms are square roots of the same sum of squares, reindexed along `σ`.
  rw [Submission.smr_ci_norm_eq_sqrt_sum_coord_sq, LinearEquiv.ofBijective_apply,
    EuclideanSpace.norm_eq, ← σ.sum_comp]
  simp only [hJ, Real.norm_eq_abs, sq_abs]
/-- **Mollification step of Simon Ch. 6, 2.7–2.9 (pp. 136–137).**  A continuous compactly
supported `k`-form `φ` with `tsupport φ ⊆ V`, `V` open, is a uniform limit, in the Euclidean
coefficient norm, of test forms supported in `V`.  As `|α| ≤ √M ‖α‖` (`M = #(Fin k → Fin P)`,
`‖α‖` the operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ φ)`:
`ψ ⋆ φ` is the convolution of `φ` with a normalized smooth bump `ψ` supported in a ball whose
radius is a uniform-continuity modulus of `φ`, and `χ` is a smooth cutoff with values in `[0, 1]`,
equal to `1` exactly on `tsupport φ`, whose support `V'` has compact closure in `V`. -/
theorem Submission.smr_exists_testForm_uniform_approx : ∀ (P k : ℕ) (U V : Set (Eucl P)) (φ : Eucl P → Covector (Eucl P) k), IsOpen V → V ⊆ U → Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧ ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ ε := by
  intro P k U V φ hV hVU hφ hφc hφV ε hε
  -- Step 1: `|α| ≤ C ‖α‖` with `C = √M`, since every coefficient satisfies
  -- `|α(e_I)| ≤ ‖α‖ ∏ ‖e_{I j}‖ = ‖α‖`.
  set C : ℝ := Real.sqrt (Fintype.card (Fin k → Fin P)) with hC_def
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hcmp : ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hC_def, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin k → Fin P,
          (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
        ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg α)] using h)
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  have hC1 : 0 < C + 1 := by linarith
  set ε' : ℝ := ε / (C + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε hC1
  -- Step 2: an open `V'` with `tsupport φ ⊆ V'` and `closure V' ⊆ V` compact.
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ :=
    exists_open_between_and_isCompact_closure hφc.isCompact hV hφV
  -- Step 3: a smooth cutoff `χ : ℝ^P → [0, 1]` with `support χ = V'` and `χ = 1` exactly on
  -- `tsupport φ`.
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV'o (isClosed_tsupport φ) hKV'
  -- Step 4: mollification.  `φ` is uniformly continuous with modulus `δ` at accuracy `ε'`; `ψ` is
  -- a smooth bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `g = ψ ⋆ φ` is smooth and
  -- `dist (g x) (φ x) ≤ ε'`.
  obtain ⟨δ, hδ, hφδ⟩ :=
    Metric.uniformContinuous_iff.mp (hφc.uniformContinuous_of_continuous hφ) ε' hε'
  obtain ⟨b, hbs, hbc, hbd, hbr, hb0⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
  have hbnn : ∀ y, 0 ≤ b y := fun y => (hbr (mem_range_self y)).1
  have hbint : 0 < ∫ y, b y :=
    hbd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc (fun y => hbnn y)
      (hb0.symm ▸ one_ne_zero : b 0 ≠ 0)
  set ψ : Eucl P → ℝ := fun y => (∫ z, b z)⁻¹ * b y with hψ_def
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hbd
  have hψc : HasCompactSupport ψ := hbc.mul_left
  have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hbint.le) (hbnn y)
  have hψs : Function.support ψ ⊆ ball 0 δ :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport b).trans hbs)
  have hψ1 : ∫ y, ψ y = 1 := by
    rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hbint.ne']
  obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → Covector (Eucl P) k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (φ x) ≤ ε' :=
    ⟨convolution ψ φ (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      hψc.contDiff_convolution_left _ hψd hφ.locallyIntegrable,
      fun x => dist_convolution_le hε'.le hψs hψnn hψ1 hφ.aestronglyMeasurable
        fun y hy => (hφδ (mem_ball.mp hy)).le⟩
  -- Step 5: `η = χ • g` is a test form with `tsupport η ⊆ closure V' ⊆ V ⊆ U`.
  have hη_supp : tsupport (fun x => χ x • g x) ⊆ closure V' := by
    refine (tsupport_smul_subset_left χ g).trans ?_
    rw [tsupport, hχs]
  have hη_cpt : HasCompactSupport (fun x => χ x • g x) :=
    hV'c.of_isClosed_subset (isClosed_tsupport _) hη_supp
  refine ⟨⟨fun x => χ x • g x, ⟨⟨hχ.smul hg, hη_cpt⟩, hη_supp.trans (hV'V.trans hVU)⟩⟩,
    hη_supp.trans hV'V, fun x => ?_⟩
  -- Step 6: `‖φ x - η x‖ ≤ ε'` (on `tsupport φ`, `η = g`; off it, `φ = 0` and `0 ≤ χ ≤ 1`),
  -- hence `|φ x - η x| ≤ C ε' ≤ ε`.
  have hle : ‖φ x - χ x • g x‖ ≤ ε' := by
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε' := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  calc covectorEuclideanNorm (φ x - χ x • g x) ≤ C * ‖φ x - χ x • g x‖ := hcmp _
    _ ≤ C * ε' := mul_le_mul_of_nonneg_left hle hC
    _ ≤ ε := by
      rw [hε'_def, mul_div_assoc', div_le_iff₀ hC1]
      nlinarith

/-- Continuous extension of a current of locally finite mass (Simon Ch. 6, 2.7, pp. 136–137,
steps P1–P2): there is `L` on continuous forms with `L = X` on test forms, additive and
homogeneous on continuous compactly supported forms in `U`, and with `|L φ|` bounded on each
compact `K ⊆ U` for `|φ| ≤ 1` (Euclidean coefficient norm).  `L φ` is the limit of `X (ζ j)`
along any sequence of test forms `ζ j`, supported in a common `V ⊂⊂ U`, converging to `φ`
uniformly; the limit exists and is unique by the mass estimate `|X ω| ≤ M_V(X) · sup |ω|`. -/
theorem Submission.smr_exists_continuous_extension :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) →
      ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ,
        (∀ ω : TestFormOn U k, L (ω : DifferentialForm (Eucl P) k) = X ω) ∧
        (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          L (φ + ψ) = L φ + L ψ) ∧
        (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → L (c • φ) = c * L φ) ∧
        ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
          ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → tsupport φ ⊆ K →
            (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → |L φ| ≤ B := by
  intro P k U hU X hX
  -- Step 0: the Euclidean coefficient norm is a norm, via the isometry `J` onto `ℝ^N`.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have hle : ∀ α β : Covector (Eucl P) k,
      covectorEuclideanNorm β ≤ covectorEuclideanNorm α + covectorEuclideanNorm (α - β) := by
    intro α β
    simp only [hJ, map_sub]
    exact norm_le_norm_add_norm_sub _ _
  have htri : ∀ α β γ : Covector (Eucl P) k, covectorEuclideanNorm (β - γ) ≤
      covectorEuclideanNorm (α - β) + covectorEuclideanNorm (α - γ) := by
    intro α β γ
    simp only [hJ, map_sub]
    calc ‖J β - J γ‖ ≤ ‖J β - J α‖ + ‖J α - J γ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖J α - J β‖ + ‖J α - J γ‖ := by rw [norm_sub_rev (J β)]
  have hadd : ∀ α β γ δ : Covector (Eucl P) k, covectorEuclideanNorm (α + β - (γ + δ)) ≤
      covectorEuclideanNorm (α - γ) + covectorEuclideanNorm (β - δ) := by
    intro α β γ δ
    rw [add_sub_add_comm]
    simp only [hJ, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hJ, hJ, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 1: compact subsets of `U` lie in some `V ⊂⊂ U`, and `⊂⊂ U` is closed under unions.
  have hnbhd : ∀ K, IsCompact K → K ⊆ U → ∃ V, CompactlyContainedOpen V U ∧ K ⊆ V := by
    intro K hK hKU
    obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨V, ⟨hVo, hVc, hVU⟩, hKV⟩
  have hunion : ∀ V₁ V₂, CompactlyContainedOpen V₁ U → CompactlyContainedOpen V₂ U →
      CompactlyContainedOpen (V₁ ∪ V₂) U := by
    rintro V₁ V₂ ⟨h₁o, h₁c, h₁U⟩ ⟨h₂o, h₂c, h₂U⟩
    refine ⟨h₁o.union h₂o, ?_, ?_⟩ <;> rw [closure_union]
    · exact h₁c.union h₂c
    · exact union_subset h₁U h₂U
  -- Step 2 (P1): `|X ω| ≤ M_V · C` for `ω` supported in `V ⊂⊂ U` with `|ω| ≤ C`.
  have hmass : ∀ V, CompactlyContainedOpen V U → ∀ (ω : TestFormOn U k) (C : ℝ),
      tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ C) →
      |X ω| ≤ (X.massOn V).toReal * C := by
    intro V hV ω C hωV hC
    -- For `s > C`, both `±s⁻¹ ω` are admissible for `M_V(X)`, hence `|X ω| ≤ M_V · s`.
    have key : ∀ s, C < s → |X ω| ≤ (X.massOn V).toReal * s := by
      intro s hs
      have hs0 : 0 < s := ((covectorEuclideanNorm_nonneg _).trans (hC 0)).trans_lt hs
      have hb : ∀ t : ℝ, |t| = s⁻¹ → t * X ω ≤ (X.massOn V).toReal := by
        intro t ht
        have hadm : t • ω ∈ massAdmissibleOn U k V := by
          refine ⟨(tsupport_smul_subset_right (fun _ => t) _).trans hωV, fun x => ?_⟩
          change covectorEuclideanNorm (t • (ω : DifferentialForm (Eucl P) k) x) ≤ 1
          rw [hsmul, ht, inv_mul_le_iff₀ hs0, mul_one]
          exact (hC x).trans hs.le
        have h := (X.le_massOn hadm).trans (ENNReal.ofReal_toReal (hX V hV).ne).ge
        rwa [ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, map_smul, smul_eq_mul] at h
      have h₁ := hb s⁻¹ (abs_of_pos (inv_pos.2 hs0))
      have h₂ := hb (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs0)])
      rw [inv_mul_le_iff₀ hs0, mul_comm] at h₁
      rw [neg_mul_comm, inv_mul_le_iff₀ hs0, mul_comm] at h₂
      exact abs_le.2 ⟨by linarith, h₁⟩
    -- Let `s ↓ C` along `s = C + 1 / (n + 1)`.
    have hlim : Tendsto (fun n : ℕ => (X.massOn V).toReal * (C + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 ((X.massOn V).toReal * C)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add C).const_mul
        (X.massOn V).toReal
    exact ge_of_tendsto' hlim fun n => key _ (lt_add_of_pos_right C Nat.one_div_pos_of_nat)
  -- Test forms supported in `V₁, V₂ ⊂⊂ U` and uniformly close to the same `φ` have close values.
  have hclose : ∀ (φ : Eucl P → Covector (Eucl P) k) V₁ V₂, CompactlyContainedOpen V₁ U →
      CompactlyContainedOpen V₂ U → ∀ (η ζ : TestFormOn U k) (a b : ℝ),
      tsupport (η : DifferentialForm (Eucl P) k) ⊆ V₁ →
      tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ V₂ →
      (∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ a) →
      (∀ x, covectorEuclideanNorm (φ x - (ζ : DifferentialForm (Eucl P) k) x) ≤ b) →
      |X η - X ζ| ≤ (X.massOn (V₁ ∪ V₂)).toReal * (a + b) := by
    intro φ V₁ V₂ hV₁ hV₂ η ζ a b hη hζ ha hb
    rw [← map_sub X.toCurrent η ζ]
    refine hmass _ (hunion V₁ V₂ hV₁ hV₂) (η - ζ) (a + b) ?_ fun x =>
      (htri (φ x) ((η : DifferentialForm (Eucl P) k) x)
        ((ζ : DifferentialForm (Eucl P) k) x)).trans (add_le_add (ha x) (hb x))
    exact (closure_mono (Function.support_sub _ _)).trans
      (closure_union.subset.trans (union_subset_union hη hζ))
  -- Step 4: approximations supported in a common `V ⊂⊂ U` give Cauchy sequences `X (ζ j)`.
  have hconv : ∀ (φ : Eucl P → Covector (Eucl P) k) V, CompactlyContainedOpen V U →
      ∀ (ζ : ℕ → TestFormOn U k) (d : ℕ → ℝ),
      (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) → Tendsto d atTop (𝓝 0) →
      (∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ d j) →
      ∃ r, Tendsto (fun j => X (ζ j)) atTop (𝓝 r) := by
    intro φ V hV ζ d hζV hd hζ
    have hMd : Tendsto (fun j => (X.massOn (V ∪ V)).toReal * d j) atTop (𝓝 0) := by
      simpa using hd.const_mul (X.massOn (V ∪ V)).toReal
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hMd).2 (ε / 2) (half_pos hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    calc |X (ζ n) - X (ζ N)| ≤ (X.massOn (V ∪ V)).toReal * (d n + d N) :=
          hclose φ V V hV hV (ζ n) (ζ N) (d n) (d N) (hζV n) (hζV N) (hζ n) (hζ N)
      _ = (X.massOn (V ∪ V)).toReal * d n + (X.massOn (V ∪ V)).toReal * d N := mul_add _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hN n hn) (hN N le_rfl)
      _ = ε := add_halves ε
  -- `IsLim φ r`: test forms `ζ j`, supported in a common `V ⊂⊂ U`, converge uniformly to `φ`
  -- (errors `d j → 0`) and `X (ζ j) → r`.
  let IsLim : (Eucl P → Covector (Eucl P) k) → ℝ → Prop := fun φ r =>
    ∃ V, CompactlyContainedOpen V U ∧ ∃ (ζ : ℕ → TestFormOn U k) (d : ℕ → ℝ),
      (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) ∧ Tendsto d atTop (𝓝 0) ∧
      (∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ d j) ∧
      Tendsto (fun j => X (ζ j)) atTop (𝓝 r)
  -- Step 5: the limit does not depend on the approximation.
  have huniq : ∀ φ r s, IsLim φ r → IsLim φ s → r = s := by
    rintro φ r s ⟨V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩ ⟨V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩
    have h0 : Tendsto (fun j => X (ζ₁ j) - X (ζ₂ j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans
        (hclose φ V₁ V₂ hV₁ hV₂ (ζ₁ j) (ζ₂ j) (d₁ j) (d₂ j) (hs₁ j) (hs₂ j) (ha₁ j)
          (ha₂ j))) ?_
      simpa using (hd₁.add hd₂).const_mul (X.massOn (V₁ ∪ V₂)).toReal
    exact sub_eq_zero.1 (tendsto_nhds_unique (hl₁.sub hl₂) h0)
  -- Definition of `L`: the common limit of the approximations (arbitrary if there are none).
  obtain ⟨L, hL⟩ : ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ, ∀ φ r, IsLim φ r → L φ = r :=
    ⟨fun φ => Classical.epsilon (IsLim φ), fun φ r hr =>
      huniq φ _ _ (Classical.epsilon_spec ⟨r, hr⟩) hr⟩
  -- Step 3: uniform approximants `|φ - ζ j| ≤ 1 / (j + 1)` supported in `V`.
  have happ : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
      ∀ V, CompactlyContainedOpen V U → tsupport φ ⊆ V →
      ∃ ζ : ℕ → TestFormOn U k, (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) ∧
        ∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤
          1 / ((j : ℝ) + 1) := by
    intro φ hφ hφc V hV hφV
    choose ζ hζV hζ using fun j : ℕ =>
      Submission.smr_exists_testForm_uniform_approx P k U V φ hV.1
        (subset_closure.trans hV.2.2) hφ hφc hφV (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨ζ, hζV, hζ⟩
  -- Every `φ ∈ CF(U)` has an approximation, hence a limit.
  have hexists : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∃ r, IsLim φ r := by
    intro φ hφ hφc hφU
    obtain ⟨V, hV, hφV⟩ := hnbhd _ hφc hφU
    obtain ⟨ζ, hζV, hζ⟩ := happ φ hφ hφc V hV hφV
    obtain ⟨r, hr⟩ := hconv φ V hV ζ _ hζV tendsto_one_div_add_atTop_nhds_zero_nat hζ
    exact ⟨r, V, hV, ζ, _, hζV, tendsto_one_div_add_atTop_nhds_zero_nat, hζ, hr⟩
  refine ⟨L, fun ω => ?_, fun φ ψ hφ hφc hφU hψ hψc hψU => ?_,
    fun c φ hφ hφc hφU => ?_, fun K hK hKU => ?_⟩
  · -- (1) The constant approximation `ζ j = ω`.
    obtain ⟨V, hV, hωV⟩ := hnbhd _ ω.2.1.2 ω.2.2
    exact hL _ _ ⟨V, hV, fun _ => ω, fun _ => 0, fun _ => hωV, tendsto_const_nhds,
      fun _ x => by simp, tendsto_const_nhds⟩
  · -- (2) The sum of approximations of `φ` and `ψ`.
    obtain ⟨r₁, V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩ := hexists φ hφ hφc hφU
    obtain ⟨r₂, V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩ := hexists ψ hψ hψc hψU
    rw [hL φ r₁ ⟨V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩,
      hL ψ r₂ ⟨V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩]
    refine hL _ _ ⟨V₁ ∪ V₂, hunion V₁ V₂ hV₁ hV₂, fun j => ζ₁ j + ζ₂ j,
      fun j => d₁ j + d₂ j, fun j => ?_, by simpa using hd₁.add hd₂, fun j x => ?_, ?_⟩
    · exact (tsupport_add (ζ₁ j : DifferentialForm (Eucl P) k) (ζ₂ j)).trans
        (union_subset_union (hs₁ j) (hs₂ j))
    · exact (hadd (φ x) (ψ x) ((ζ₁ j : DifferentialForm (Eucl P) k) x)
        ((ζ₂ j : DifferentialForm (Eucl P) k) x)).trans (add_le_add (ha₁ j x) (ha₂ j x))
    · simpa only [map_add] using hl₁.add hl₂
  · -- (3) The scalar multiple of an approximation of `φ`.
    obtain ⟨r, V, hV, ζ, d, hs, hd, ha, hl⟩ := hexists φ hφ hφc hφU
    rw [hL φ r ⟨V, hV, ζ, d, hs, hd, ha, hl⟩]
    refine hL _ _ ⟨V, hV, fun j => c • ζ j, fun j => |c| * d j,
      fun j => (tsupport_smul_subset_right (fun _ => c) _).trans (hs j),
      by simpa using hd.const_mul |c|, fun j x => ?_, ?_⟩
    · have e : (c • φ) x - ((c • ζ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x =
          c • (φ x - (ζ j : DifferentialForm (Eucl P) k) x) := (smul_sub c _ _).symm
      rw [e, hsmul]
      exact mul_le_mul_of_nonneg_left (ha j x) (abs_nonneg c)
    · simpa only [map_smul, smul_eq_mul] using hl.const_mul c
  · -- (4) `|L φ| ≤ 2 M_V` for `|φ| ≤ 1` supported in `K ⊆ V ⊂⊂ U`.
    obtain ⟨V, hV, hKV⟩ := hnbhd K hK hKU
    refine ⟨(X.massOn V).toReal * 2, fun φ hφ hφK hφ1 => ?_⟩
    have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hφK
    obtain ⟨ζ, hζV, hζ⟩ := happ φ hφ hφc V hV (hφK.trans hKV)
    obtain ⟨r, hr⟩ := hconv φ V hV ζ _ hζV tendsto_one_div_add_atTop_nhds_zero_nat hζ
    rw [hL φ r ⟨V, hV, ζ, _, hζV, tendsto_one_div_add_atTop_nhds_zero_nat, hζ, hr⟩]
    refine le_of_tendsto' hr.abs fun j => hmass V hV (ζ j) 2 (hζV j) fun x => ?_
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    calc covectorEuclideanNorm ((ζ j : DifferentialForm (Eucl P) k) x)
        ≤ covectorEuclideanNorm (φ x) +
            covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) := hle _ _
      _ ≤ 1 + 1 := add_le_add (hφ1 x) ((hζ j x).trans h1)
      _ = 2 := one_add_one_eq_two
/-- Extension by zero from `↥U` to `ℝ^P` transfers a locally bounded functional `L` on
`CF_N(U)` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`, with `L f = L' (f ∘ ι)`
for every `f ∈ CF_N(U)`. -/
theorem Submission.smr_rb_transfer_functional :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ,
      (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        L (f + g) = L f + L g) →
      (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → L (c • f) = c * L f) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K →
          (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) →
      ∃ L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ,
        (∀ K : Set ↥U, IsCompact K → ∃ B : ℝ,
          ∀ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)),
            (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L' g ≤ B) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U →
          ∃ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)),
            (∀ y : ↥U, g y = f ↑y) ∧ L f = L' g := by
  intro P N U hU L hadd hsmul hbd
  -- The zero extension `E g = Function.extend Subtype.val g 0` of `g ∈ C_c(↥U, ℝ^N)`.
  set E : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →
      Eucl P → EuclideanSpace ℝ (Fin N) := fun g => Function.extend Subtype.val (⇑g) 0
  have hEval : ∀ g x (hx : x ∈ U), E g x = g ⟨x, hx⟩ := fun g x hx =>
    Subtype.val_injective.extend_apply (⇑g) 0 ⟨x, hx⟩
  have hEout : ∀ g x, x ∉ U → E g x = 0 := fun g x hx =>
    Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)
  -- `E g ∈ CF_N(U)`, with `tsupport (E g) ⊆ ι(tsupport g)`; continuity uses that `U` is open.
  have hEsupp : ∀ g, tsupport (E g) ⊆ Subtype.val '' tsupport g := fun g =>
    g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val
  have hEU : ∀ g, tsupport (E g) ⊆ U := fun g =>
    (hEsupp g).trans (Subtype.coe_image_subset _ _)
  have hEcpt : ∀ g, HasCompactSupport (E g) := fun g =>
    g.hasCompactSupport.extend_zero continuous_subtype_val
  have hEcont : ∀ g, Continuous (E g) := fun g =>
    HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport
  -- The extension is linear.
  have hEadd : ∀ g h, E (g + h) = E g + E h := by
    intro g h; funext x
    by_cases hx : x ∈ U
    · simp only [Pi.add_apply, hEval _ x hx, CompactlySupportedContinuousMap.add_apply]
    · simp only [Pi.add_apply, hEout _ x hx, add_zero]
  have hEsmul : ∀ (c : ℝ) g, E (c • g) = c • E g := by
    intro c g; funext x
    by_cases hx : x ∈ U
    · simp only [Pi.smul_apply, hEval _ x hx, CompactlySupportedContinuousMap.smul_apply]
    · simp only [Pi.smul_apply, hEout _ x hx, smul_zero]
  -- `L' g = L (E g)` is linear by the additivity and homogeneity of `L` on `CF_N(U)`.
  let L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ :=
    { toFun := fun g => L (E g)
      map_add' := fun g h => by
        show L (E (g + h)) = L (E g) + L (E h)
        rw [hEadd]
        exact hadd _ _ (hEcont g) (hEcpt g) (hEU g) (hEcont h) (hEcpt h) (hEU h)
      map_smul' := fun c g => by
        show L (E (c • g)) = c * L (E g)
        rw [hEsmul]
        exact hsmul c _ (hEcont g) (hEcpt g) (hEU g) }
  refine ⟨L', fun K hK => ?_, fun f hf hfc hfU => ?_⟩
  · -- The bound for the compact set `ι(K) ⊆ U` serves for `L'` on `K`.
    obtain ⟨B, hB⟩ := hbd (Subtype.val '' K) (hK.image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)
    refine ⟨B, fun g hg hgK => hB (E g) (hEcont g) ((hEsupp g).trans (image_mono hgK)) fun x => ?_⟩
    by_cases hx : x ∈ U
    · rw [hEval g x hx]; exact hg _
    · rw [hEout g x hx, norm_zero]; exact zero_le_one
  · -- `g = f ∘ ι` vanishes off the compact set `ι⁻¹(tsupport f)`, and `E g = f`.
    have hcpt : HasCompactSupport (f ∘ Subtype.val : ↥U → EuclideanSpace ℝ (Fin N)) := by
      refine HasCompactSupport.intro (K := Subtype.val ⁻¹' tsupport f) ?_ fun y hy => ?_
      · exact (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (hfU.trans Subtype.range_coe.symm.subset)).2 hfc
      · exact image_eq_zero_of_notMem_tsupport (f := f) hy
    let g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) :=
      ⟨⟨f ∘ Subtype.val, hf.comp continuous_subtype_val⟩, hcpt⟩
    refine ⟨g, fun y => rfl, ?_⟩
    show L f = L (E g)
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hEval g x hx]; rfl
    · rw [hEout g x hx]
      exact image_eq_zero_of_notMem_tsupport fun h => hx (hfU h)
/-- Riesz representation (Simon Ch. 1, 4.14) with Borel data on a σ-compact locally compact
Hausdorff space: a locally bounded functional on `C_c(Y, ℝ^N)` is `g ↦ ∫ ⟨g, ν⟩ dm` for a
measure `m` finite on compacts and a Borel field `ν` with `‖ν‖ ≤ 1`, `‖ν‖ = 1` `m`-a.e. -/
theorem Submission.smr_rb_borel_riesz_sigma_compact : ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (N : ℕ) (L : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ), (∀ K : Set Y, IsCompact K → ∃ B : ℝ, ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L g ≤ B) → ∃ (m : Measure Y) (ν : Y → EuclideanSpace ℝ (Fin N)), (∀ K : Set Y, IsCompact K → m K < ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ ≤ 1) ∧ (∀ᵐ y ∂m, ‖ν y‖ = 1) ∧ ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), L g = ∫ y, inner ℝ (g y) (ν y) ∂m := by
  intro Y _ _ _ _ _ _ N L hL
  -- Step 1: a functional on `C_c(Y, ℝ)` bounded above on each order interval `[0, f]` is
  -- dominated on nonnegative functions by a positive functional (its positive part).
  have key : ∀ ℓ : CompactlySupportedContinuousMap Y ℝ →ₗ[ℝ] ℝ,
      (∀ f : CompactlySupportedContinuousMap Y ℝ≥0, ∃ B : ℝ,
        ∀ φ : CompactlySupportedContinuousMap Y ℝ≥0, φ ≤ f → ℓ φ.toReal ≤ B) →
      ∃ Λ : CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ,
        ∀ f : CompactlySupportedContinuousMap Y ℝ, 0 ≤ f → ℓ f ≤ Λ f := by
    intro ℓ hB
    -- `S f = sup {ℓ φ : φ ≤ f}`, the positive part of `ℓ` on nonnegative functions
    let S : CompactlySupportedContinuousMap Y ℝ≥0 → ℝ := fun f =>
      sSup ((fun φ : CompactlySupportedContinuousMap Y ℝ≥0 => ℓ φ.toReal) '' Set.Iic f)
    have hzero : (0 : CompactlySupportedContinuousMap Y ℝ≥0).toReal = 0 := by ext; simp
    have hle : ∀ f φ, φ ≤ f → ℓ φ.toReal ≤ S f := by
      intro f φ hφ
      obtain ⟨B, hB⟩ := hB f
      exact le_csSup ⟨B, by rintro _ ⟨ψ, hψ, rfl⟩; exact hB ψ hψ⟩ ⟨φ, hφ, rfl⟩
    have hsup : ∀ f c, (∀ φ, φ ≤ f → ℓ φ.toReal ≤ c) → S f ≤ c := by
      intro f c h
      exact csSup_le ⟨_, 0, fun y => zero_le, rfl⟩ (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ)
    have hS0 : ∀ f, 0 ≤ S f := fun f => by
      simpa [hzero] using hle f 0 (fun y => zero_le)
    have hadd : ∀ f g, S (f + g) = S f + S g := by
      intro f g
      refine le_antisymm (hsup _ _ fun φ hφ => ?_) ?_
      · obtain ⟨φ₂, hφ₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le
          (inf_le_left : φ ⊓ f ≤ φ)
        have h2 : φ₂ ≤ g := by
          intro y
          have e := DFunLike.congr_fun hφ₂ y
          have hy := hφ y
          simp only [CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.inf_apply] at e hy
          rcases le_total (φ y) (f y) with h | h
          · rw [inf_eq_left.2 h] at e
            have : φ₂ y = 0 := by simpa using e
            rw [this]; exact zero_le
          · rw [inf_eq_right.2 h] at e
            rw [← e] at hy
            exact le_of_add_le_add_left hy
        calc ℓ φ.toReal = ℓ (φ ⊓ f).toReal + ℓ φ₂.toReal := by
              rw [← map_add, ← CompactlySupportedContinuousMap.toReal_add, hφ₂]
          _ ≤ S f + S g := add_le_add (hle _ _ inf_le_right) (hle _ _ h2)
      · have h1 : ∀ φ, φ ≤ f → ℓ φ.toReal + S g ≤ S (f + g) := by
          intro φ hφ
          have := hsup g (S (f + g) - ℓ φ.toReal) fun ψ hψ => by
            have := hle (f + g) (φ + ψ) fun y => add_le_add (hφ y) (hψ y)
            rw [CompactlySupportedContinuousMap.toReal_add, map_add] at this
            linarith
          linarith
        have := hsup f (S (f + g) - S g) fun φ hφ => by linarith [h1 φ hφ]
        linarith
    have hsmul_le : ∀ (c : ℝ≥0) f, S (c • f) ≤ c * S f := by
      intro c f
      rcases eq_or_ne c 0 with rfl | hc
      · refine hsup _ _ fun φ hφ => ?_
        have : φ = 0 := by
          ext y
          have := hφ y
          simp only [zero_smul, CompactlySupportedContinuousMap.zero_apply] at this
          simpa using le_antisymm this zero_le
        simp [this, hzero]
      · refine hsup _ _ fun φ hφ => ?_
        have h1 : c⁻¹ • φ ≤ f := by
          intro y
          have := hφ y
          simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul] at this ⊢
          rwa [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)]
        have h2 : c • (c⁻¹ • φ) = φ := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        calc ℓ φ.toReal = c * ℓ (c⁻¹ • φ).toReal := by
              conv_lhs => rw [← h2]
              rw [CompactlySupportedContinuousMap.toReal_smul, NNReal.smul_def, map_smul,
                smul_eq_mul]
          _ ≤ c * S f := mul_le_mul_of_nonneg_left (hle _ _ h1) c.2
    have hsmul : ∀ (c : ℝ≥0) f, S (c • f) = c * S f := by
      intro c f
      refine le_antisymm (hsmul_le c f) ?_
      rcases eq_or_ne c 0 with rfl | hc
      · rw [NNReal.coe_zero, zero_mul]; exact hS0 _
      · have := hsmul_le c⁻¹ (c • f)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        calc (c : ℝ) * S f ≤ c * (c⁻¹ * S (c • f)) := mul_le_mul_of_nonneg_left this c.2
          _ = S (c • f) := by
            rw [← mul_assoc, ← NNReal.coe_mul, mul_inv_cancel₀ hc, NNReal.coe_one, one_mul]
    let Λ₀ : CompactlySupportedContinuousMap Y ℝ≥0 →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f => Real.toNNReal (S f)
        map_add' := fun f g => by rw [hadd, Real.toNNReal_add (hS0 f) (hS0 g)]
        map_smul' := fun c f => by
          rw [hsmul, Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe, RingHom.id_apply, smul_eq_mul] }
    refine ⟨CompactlySupportedContinuousMap.toRealPositiveLinear Λ₀, fun f hf => ?_⟩
    have hf' : f.nnrealPart.toReal = f := by
      ext y
      have hfy : 0 ≤ f y := by simpa using hf y
      simp [hfy]
    rw [← hf', CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
    exact (hle _ _ le_rfl).trans (Real.le_coe_toNNReal _)
  -- Step 2: the coordinate functionals `ψ ↦ L(ψ bᵢ)` for the standard orthonormal basis `b`.
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  let mk : CompactlySupportedContinuousMap Y ℝ → EuclideanSpace ℝ (Fin N) →
      CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) := fun ψ v =>
    ψ.compLeft ⟨fun t => t • v, continuous_id.smul continuous_const⟩
  have mk_apply : ∀ ψ v y, mk ψ v y = ψ y • v := fun ψ v y =>
    CompactlySupportedContinuousMap.compLeft_apply (by simp) ψ y
  let ℓ : EuclideanSpace ℝ (Fin N) → CompactlySupportedContinuousMap Y ℝ →ₗ[ℝ] ℝ := fun v =>
    { toFun := fun ψ => L (mk ψ v)
      map_add' := fun ψ φ => by
        rw [← map_add]
        congr 1
        exact CompactlySupportedContinuousMap.ext fun y => by simp [mk_apply, add_smul]
      map_smul' := fun c ψ => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        exact CompactlySupportedContinuousMap.ext fun y => by simp [mk_apply, smul_smul] }
  have hbound : ∀ i, ∀ f : CompactlySupportedContinuousMap Y ℝ≥0, ∃ B : ℝ,
      ∀ φ : CompactlySupportedContinuousMap Y ℝ≥0, φ ≤ f → ℓ (b i) φ.toReal ≤ B := by
    intro i f
    obtain ⟨B, hB⟩ := hL (tsupport f) f.hasCompactSupport
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖f.toReal y‖ ≤ C :=
      (map_continuous f.toReal).bounded_above_of_compact_support f.toReal.hasCompactSupport
    have hc : 0 < |C| + 1 := by positivity
    refine ⟨(|C| + 1) * B, fun φ hφ => ?_⟩
    have hφf : ∀ y, (φ y : ℝ) ≤ |C| + 1 := fun y => by
      have h1 : (φ y : ℝ) ≤ f y := NNReal.coe_le_coe.2 (hφ y)
      have h2 := hC y
      rw [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs] at h2
      linarith [le_abs_self C, le_abs_self (f y : ℝ)]
    have hnorm : ∀ y, ‖mk ((|C| + 1)⁻¹ • φ.toReal) (b i) y‖ ≤ 1 := fun y => by
      rw [mk_apply, norm_smul, hb, mul_one, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      rw [inv_mul_le_iff₀ hc, mul_one]
      exact hφf y
    have hsupp : tsupport (mk ((|C| + 1)⁻¹ • φ.toReal) (b i)) ⊆ tsupport f := by
      refine closure_mono fun y hy => ?_
      rw [Function.mem_support] at hy ⊢
      contrapose! hy
      have : φ y = 0 := le_antisymm ((hφ y).trans hy.le) zero_le
      simp [mk_apply, this]
    have h := hB _ hnorm hsupp
    change ℓ (b i) ((|C| + 1)⁻¹ • φ.toReal) ≤ B at h
    rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hc] at h
    exact h
  -- Step 3: Jordan decomposition `ℓᵢ = Λᵢ - Qᵢ` and the Riesz–Markov–Kakutani measures.
  choose Λ hΛ using fun i => key (ℓ (b i)) (hbound i)
  let Q : Fin N → CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ := fun i =>
    PositiveLinearMap.mk₀ ((Λ i).toLinearMap - ℓ (b i)) fun f hf => by
      simpa using hΛ i f hf
  have hℓ : ∀ i ψ, ℓ (b i) ψ =
      ∫ y, ψ y ∂(RealRMK.rieszMeasure (Λ i)) - ∫ y, ψ y ∂(RealRMK.rieszMeasure (Q i)) := by
    intro i ψ
    rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    change _ = _ - ((Λ i) ψ - ℓ (b i) ψ)
    ring
  -- Step 4: the reference measure `μ₀ = ∑ᵢ (μ_{Λᵢ} + μ_{Qᵢ})` and Radon–Nikodym transfer.
  let μ₀ : Measure Y := ∑ i, (RealRMK.rieszMeasure (Λ i) + RealRMK.rieszMeasure (Q i))
  have hμ₀ : ∀ s, μ₀ s = ∑ i, (RealRMK.rieszMeasure (Λ i) s + RealRMK.rieszMeasure (Q i) s) := by
    intro s
    simp only [μ₀, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_add, Pi.add_apply]
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨fun K hK => by
    rw [hμ₀]
    exact ENNReal.sum_lt_top.2 fun i _ =>
      ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  have hPle : ∀ i, RealRMK.rieszMeasure (Λ i) ≤ μ₀ := fun i => Measure.le_iff'.2 fun s => by
    rw [hμ₀]
    exact le_self_add.trans (Finset.single_le_sum
      (f := fun j => RealRMK.rieszMeasure (Λ j) s + RealRMK.rieszMeasure (Q j) s)
      (fun j _ => zero_le) (Finset.mem_univ i))
  have hQle : ∀ i, RealRMK.rieszMeasure (Q i) ≤ μ₀ := fun i => Measure.le_iff'.2 fun s => by
    rw [hμ₀]
    exact le_add_self.trans (Finset.single_le_sum
      (f := fun j => RealRMK.rieszMeasure (Λ j) s + RealRMK.rieszMeasure (Q j) s)
      (fun j _ => zero_le) (Finset.mem_univ i))
  have transfer : ∀ (μ' : Measure Y) [IsFiniteMeasureOnCompacts μ'], μ' ≤ μ₀ →
      ∀ ψ : CompactlySupportedContinuousMap Y ℝ,
        Integrable (fun y => (μ'.rnDeriv μ₀ y).toReal • ψ y) μ₀ ∧
        ∫ y, ψ y ∂μ' = ∫ y, (μ'.rnDeriv μ₀ y).toReal • ψ y ∂μ₀ := by
    intro μ' _ hle ψ
    have hwd : μ₀.withDensity (μ'.rnDeriv μ₀) = μ' := by
      have h := Measure.rnDeriv_add_singularPart μ' μ₀
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        add_zero] at h
    have hint : Integrable ψ (μ₀.withDensity (μ'.rnDeriv μ₀)) := by
      rw [hwd]
      exact (map_continuous ψ).integrable_of_hasCompactSupport ψ.hasCompactSupport
    refine ⟨(integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).1 hint, ?_⟩
    calc ∫ y, ψ y ∂μ' = ∫ y, ψ y ∂(μ₀.withDensity (μ'.rnDeriv μ₀)) := by rw [hwd]
      _ = _ := integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
          (Measure.rnDeriv_lt_top _ _) _
  -- the vector density `w = ∑ᵢ (dμ_{Λᵢ}/dμ₀ - dμ_{Qᵢ}/dμ₀) bᵢ`
  let a : Fin N → Y → ℝ := fun i y => ((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal -
    ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal
  let w : Y → EuclideanSpace ℝ (Fin N) := fun y => ∑ i, a i y • b i
  have hw : Measurable w := Finset.measurable_sum _ fun i _ =>
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).smul_const _
  -- Step 5: `L g = ∫ ⟨g, w⟩ dμ₀`.
  have hrep : ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)),
      L g = ∫ y, inner ℝ (g y) (w y) ∂μ₀ := by
    intro g
    let gc : Fin N → CompactlySupportedContinuousMap Y ℝ := fun i =>
      g.compLeft ⟨fun v => inner ℝ (b i) v, continuous_const.inner continuous_id⟩
    have gc_apply : ∀ i y, gc i y = inner ℝ (b i) (g y) := fun i y =>
      CompactlySupportedContinuousMap.compLeft_apply (by simp) g y
    have hg : g = ∑ i, mk (gc i) (b i) := by
      refine CompactlySupportedContinuousMap.ext fun y => ?_
      rw [CompactlySupportedContinuousMap.sum_apply]
      simp only [mk_apply, gc_apply]
      exact (b.sum_repr' (g y)).symm
    have hP := fun i => transfer _ (hPle i) (gc i)
    have hQ := fun i => transfer _ (hQle i) (gc i)
    calc L g = ∑ i, ℓ (b i) (gc i) := by
          conv_lhs => rw [hg]
          rw [map_sum]
          rfl
      _ = ∑ i, ∫ y, (((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal • gc i y -
            ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal • gc i y) ∂μ₀ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hℓ, (hP i).2, (hQ i).2, integral_sub (hP i).1 (hQ i).1]
      _ = ∫ y, ∑ i, (((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal • gc i y -
            ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal • gc i y) ∂μ₀ :=
          (integral_finsetSum _ fun i _ => (hP i).1.sub (hQ i).1).symm
      _ = ∫ y, inner ℝ (g y) (w y) ∂μ₀ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [w, a, inner_sum, real_inner_smul_right, gc_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [real_inner_comm]
          ring
  -- Step 6: polar normalization `m = ‖w‖ μ₀`, `ν = ‖w‖⁻¹ w`.
  have hbe : ∀ i, ‖b i‖ₑ = 1 := fun i => by
    rw [← ofReal_norm, hb i, ENNReal.ofReal_one]
  refine ⟨μ₀.withDensity fun y => ‖w y‖ₑ, fun y => ‖w y‖⁻¹ • w y, fun K hK => ?_,
    hw.norm.inv.smul hw, fun y => ?_, ?_, fun g => ?_⟩
  · calc (μ₀.withDensity fun y => ‖w y‖ₑ) K = ∫⁻ y in K, ‖w y‖ₑ ∂μ₀ :=
          withDensity_apply _ hK.isClosed.measurableSet
      _ ≤ ∫⁻ y in K, ∑ i, ((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y +
            (RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y) ∂μ₀ := by
          refine lintegral_mono fun y =>
            (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [enorm_smul, hbe i, mul_one]
          refine enorm_sub_le.trans (add_le_add ?_ ?_) <;>
            rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg] <;> exact ENNReal.ofReal_toReal_le
      _ = ∑ i, (∫⁻ y in K, (RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y ∂μ₀ +
            ∫⁻ y in K, (RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y ∂μ₀) := by
          rw [lintegral_finsetSum']
          · exact Finset.sum_congr rfl fun i _ =>
              lintegral_add_left (Measure.measurable_rnDeriv _ _) _
          · exact fun i _ => ((Measure.measurable_rnDeriv _ _).add
              (Measure.measurable_rnDeriv _ _)).aemeasurable
      _ < ∞ := ENNReal.sum_lt_top.2 fun i _ => ENNReal.add_lt_top.2
          ⟨((withDensity_apply_le _ _).trans (Measure.le_iff'.1
              (Measure.withDensity_rnDeriv_le _ _) K)).trans_lt hK.measure_lt_top,
            ((withDensity_apply_le _ _).trans (Measure.le_iff'.1
              (Measure.withDensity_rnDeriv_le _ _) K)).trans_lt hK.measure_lt_top⟩
  · show ‖‖w y‖⁻¹ • w y‖ ≤ 1
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖w y‖ 0 with h | h
    · rw [h, inv_zero, zero_mul]
      exact zero_le_one
    · rw [inv_mul_cancel₀ h]
  · refine (ae_withDensity_iff hw.enorm).2 (ae_of_all _ fun y hy => ?_)
    show ‖‖w y‖⁻¹ • w y‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (enorm_ne_zero.1 hy))]
  · rw [hrep g, integral_withDensity_eq_integral_toReal_smul hw.enorm
      (ae_of_all _ fun y => enorm_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show inner ℝ (g y) (w y) = (‖w y‖ₑ).toReal • inner ℝ (g y) (‖w y‖⁻¹ • w y)
    rw [toReal_enorm, smul_eq_mul, real_inner_smul_right]
    rcases eq_or_ne ‖w y‖ 0 with h | h
    · rw [norm_eq_zero.1 h, inner_zero_right, mul_zero, mul_zero]
    · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]
/-- Push-forward of Borel representing data from the open subspace `↥U` to `ℝ^P`: `μ = m.map ι`
and the zero extension `ν` of `ν₁` represent the same integrals against every `f ∈ CF_N(U)`. -/
theorem Submission.smr_rb_pushforward_subtype :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (m : Measure ↥U) (ν₁ : ↥U → EuclideanSpace ℝ (Fin N)),
      (∀ K : Set ↥U, IsCompact K → m K < ∞) → Measurable ν₁ → (∀ y, ‖ν₁ y‖ ≤ 1) →
      (∀ᵐ y ∂m, ‖ν₁ y‖ = 1) →
      ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U → Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧
            ∫ x, inner ℝ (f x) (ν x) ∂μ = ∫ y, inner ℝ (f ↑y) (ν₁ y) ∂m := by
  intro P N U hU m ν₁ hm hν₁ hle hae
  -- `ι = Subtype.val : ↥U → ℝ^P` is a measurable embedding since `U` is open.
  have hι : MeasurableEmbedding (Subtype.val : ↥U → Eucl P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  -- The zero extension `ν = Function.extend Subtype.val ν₁ 0` of `ν₁`.
  set ν : Eucl P → EuclideanSpace ℝ (Fin N) := Function.extend Subtype.val ν₁ 0
  have hνval : ∀ y : ↥U, ν y = ν₁ y := fun y => Subtype.val_injective.extend_apply ν₁ 0 y
  have hνout : ∀ x, x ∉ U → ν x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)
  have hνm : Measurable ν := hι.measurable_extend hν₁ measurable_zero
  have hνle : ∀ x, ‖ν x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ U
    · rw [← Subtype.coe_mk x hx, hνval]; exact hle _
    · rw [hνout x hx, norm_zero]; exact zero_le_one
  -- Compact subsets of `U` have finite `m.map ι`-measure.
  have hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → m.map Subtype.val K < ∞ := by
    intro K hK hKU
    rw [hι.map_apply]
    exact hm _ ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (hKU.trans Subtype.range_coe.symm.subset)).2 hK)
  refine ⟨m.map Subtype.val, ν, hνm, ?_, hfin, hνle, ?_, fun f hf hfc hfU => ⟨?_, ?_⟩⟩
  · rw [hι.map_apply, Subtype.preimage_coe_compl, measure_empty]
  · exact hι.ae_map_iff.2 (hae.mono fun y hy => by rw [hνval]; exact hy)
  · -- `⟨f, ν⟩` is measurable, bounded, and vanishes off the compact `tsupport f ⊆ U`.
    have hFm : Measurable fun x => inner ℝ (f x) (ν x) :=
      continuous_inner.measurable.comp (hf.measurable.prodMk hνm)
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
    have hsupp : Function.support (fun x => inner ℝ (f x) (ν x)) ⊆ tsupport f := by
      intro x hx
      by_contra h
      exact hx (by simp only [image_eq_zero_of_notMem_tsupport h, inner_zero_left])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1
      (Measure.integrableOn_of_bounded (hfin _ hfc hfU).ne hFm.aestronglyMeasurable
        (M := C) (ae_of_all _ fun x => ?_))
    calc ‖inner ℝ (f x) (ν x)‖ ≤ ‖f x‖ * ‖ν x‖ := norm_inner_le_norm _ _
      _ ≤ ‖f x‖ := mul_le_of_le_one_right (norm_nonneg _) (hνle x)
      _ ≤ C := hC x
  · -- Change of variables along the measurable embedding `ι`.
    rw [hι.integral_map]
    simp only [hνval]

/-- Riesz representation (Simon Ch. 1, 4.14) for a locally bounded functional `L` on
`CF_N(U) = {f ∈ C_c(ℝ^P, ℝ^N) : tsupport f ⊆ U}`, `U ⊆ ℝ^P` open: there are a Borel measure `μ`
on `ℝ^P` living on `U`, finite on compact subsets of `U`, and a Borel field `ν` with `‖ν‖ ≤ 1`
and `‖ν‖ = 1` `μ`-a.e., such that `L f = ∫ ⟨f, ν⟩ dμ` for every `f ∈ CF_N(U)`. -/
theorem Submission.smr_riesz_borel_euclidean :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ,
      (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        L (f + g) = L f + L g) →
      (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → L (c • f) = c * L f) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K →
          (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) →
      ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U →
          Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧
            L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
  intro P N U hU L hadd hsmul hbd
  -- Transfer `L` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`.
  obtain ⟨L', hL'bd, hL'f⟩ := Submission.smr_rb_transfer_functional P N U hU L hadd hsmul hbd
  -- `↥U` is locally compact (`U` is open), hence σ-compact (second countable); it carries the
  -- subspace Borel σ-algebra.
  have : LocallyCompactSpace ↥U := hU.locallyCompactSpace
  -- Borel Riesz representation of `L'` on `↥U`.
  obtain ⟨m, ν₁, hmK, hν₁, hν₁le, hν₁ae, hrep⟩ :=
    Submission.smr_rb_borel_riesz_sigma_compact ↥U N L' hL'bd
  -- Push the data forward to `ℝ^P`, extending `ν₁` by zero.
  obtain ⟨μ, ν, hν, hμU, hμK, hνle, hνae, hpush⟩ :=
    Submission.smr_rb_pushforward_subtype P N U hU m ν₁ hmK hν₁ hν₁le hν₁ae
  refine ⟨μ, ν, hν, hμU, hμK, hνle, hνae, fun f hf hfc hfU => ?_⟩
  obtain ⟨hint, hμm⟩ := hpush f hf hfc hfU
  obtain ⟨g, hg, hLg⟩ := hL'f f hf hfc hfU
  -- `L f = L' g = ∫ ⟨g, ν₁⟩ dm = ∫ ⟨f ∘ ι, ν₁⟩ dm = ∫ ⟨f, ν⟩ dμ`.
  refine ⟨hint, ?_⟩
  rw [hLg, hrep g, hμm]
  simp only [hg]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
