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

/-- **A directional derivative of a compactly supported `C¹` function has integral `0`.**  For
`h : ℝᵏ → ℝ` of class `C¹` with compact support and `e ∈ ℝᵏ`, `∫ Dh(w)(e) dw = 0`, where
`Dh(w) = fderiv ℝ h w`.  `h` is Lipschitz, so integration by parts for Lipschitz functions against
the constant function `1` gives `∫ ∂ₑ1 · h = ∫ ∂₋ₑh · 1`.  The left side vanishes and, `h` being
differentiable, `∂₋ₑh(w) = Dh(w)(-e) = -Dh(w)(e)`, so the right side is `-∫ Dh(w)(e) dw`. -/
theorem Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero :
    ∀ (k : ℕ) (h : Eucl k → ℝ) (e : Eucl k), ContDiff ℝ 1 h → HasCompactSupport h →
      ∫ w, fderiv ℝ h w e ∂(volume : Measure (Eucl k)) = 0 := by
  intro k h e hh hcs
  -- `h` is Lipschitz; integrate by parts against the constant function `1`.
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hh one_ne_zero
  have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Eucl k)))
    (LipschitzWith.const (α := Eucl k) (1 : ℝ)) hD hcs e
  -- Both functions are differentiable, so their line derivatives are Fréchet derivatives.
  have h1 : ∀ w, lineDeriv ℝ (fun _ : Eucl k => (1 : ℝ)) w e = 0 := fun w => by
    rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
    simp
  have h2 : ∀ w, lineDeriv ℝ h w (-e) = -fderiv ℝ h w e := fun w => by
    rw [((hh.differentiable one_ne_zero) w).lineDeriv_eq_fderiv]
    simp
  simp only [h1, h2, zero_mul, integral_zero, mul_one, integral_neg] at key
  linarith
/-- **The determinant of a matrix of `C^m` functions is `C^m`.**  Let `M t s : ℝᵏ → ℝ`
(`t, s : Fin n`) be `C^m` for some `m : WithTop ℕ∞` (finite, `∞` or `ω`).  Then
`w ↦ det (M t s w)ₜₛ` is `C^m`.  By the Leibniz formula `det A = ∑_σ sign σ · ∏ᵢ A (σ i) i`, this
function is a finite sum, over the permutations `σ` of `Fin n`, of constant multiples of finite
products of entries (for `n = 0` it is the constant `1`). -/
theorem Submission.deformation_ipl_mwc_mis_det_contDiff :
    ∀ (k n : ℕ) (m : WithTop ℕ∞) (M : Fin n → Fin n → Eucl k → ℝ),
      (∀ t s, ContDiff ℝ m (M t s)) →
        ContDiff ℝ m (fun w => Matrix.det (Matrix.of fun t s : Fin n => M t s w)) := by
  intro k n m M hM
  -- Leibniz formula: `det (M t s w)ₜₛ = ∑_σ sign σ * ∏ᵢ M (σ i) i w`.
  simp only [Matrix.det_apply', Matrix.of_apply]
  -- Each summand is a constant times a finite product of `C^m` entries.
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hM _ _
/-- Signed first-row cofactors as restricted Leibniz sums: `(-1)^q` times the minor of the
`r × (r + 1)` array `N` with column `q` deleted is the sum of `sgn σ * ∏ t, N t (σ t.succ)` over
the permutations `σ` of `Fin (r + 1)` with `σ 0 = q`.  Both sides are the determinant of the
matrix with row `0` equal to `Pi.single q 1` and row `t.succ` equal to `N t`. -/
theorem Submission.deformation_ipl_mwc_pi_cofactor_leibniz : ∀ (r : ℕ) (N : Fin r → Fin (r + 1) → ℝ) (q : Fin (r + 1)), (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) = ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
  intro r N q
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := Matrix.of (Matrix.vecCons (Pi.single q 1) N)
  -- Laplace expansion along row `0`: only the column `j = q` survives.
  have h1 : A.det = (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single q]
    · have hsub : A.submatrix Fin.succ q.succAbove =
          Matrix.of fun t s : Fin r => N t (q.succAbove s) := by
        ext t s
        simp [A]
      rw [hsub]
      simp [A]
    · intro j _ hj
      simp [A, hj]
    · intro h
      exact absurd (Finset.mem_univ q) h
  -- Leibniz formula for `Aᵀ`: the row-`0` factor `Pi.single q 1 (σ 0)` selects `σ 0 = q`.
  have h2 : A.det = ∑ σ : Equiv.Perm (Fin (r + 1)),
      (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [A, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Pi.single_apply]
    split_ifs <;> ring
  rw [← h1, h2]
/-- Schwarz symmetry of mixed directional second derivatives of a `C²` function on `ℝ^k`:
`∂_v (∂_u f)(x) = ∂_u (∂_v f)(x)`. -/
theorem Submission.deformation_ipl_mwc_pi_hessian_symm :
    ∀ (k : ℕ) (f : Eucl k → ℝ), ContDiff ℝ 2 f → ∀ x u v : Eucl k,
      fderiv ℝ (fun y : Eucl k => fderiv ℝ f y u) x v =
        fderiv ℝ (fun y : Eucl k => fderiv ℝ f y v) x u := by
  intro k f hf x u v
  -- `Df` is `C¹`, hence differentiable at `x`; by Schwarz, `D²f(x)` is symmetric.
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := (h1.differentiable (by norm_num)) x
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  -- Differentiating `y ↦ Df(y) u` at `x` in direction `v` gives `D²f(x) v u`.
  rw [fderiv_clm_apply hd (differentiableAt_const u),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa using hs v u
/-- Product rule for a weighted sum of finite products: if every `g i t` is differentiable at
`w`, the derivative of `x ↦ ∑ i, a i * ∏ t, g i t x` at `w` in direction `v` is
`∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ≠ u, g i t w`. -/
theorem Submission.deformation_ipl_mwc_pi_fderiv_sum_prod : ∀ (k r : ℕ) (ι : Type) [Fintype ι] (a : ι → ℝ) (g : ι → Fin r → Eucl k → ℝ) (w v : Eucl k), (∀ i t, DifferentiableAt ℝ (g i t) w) → fderiv ℝ (fun x : Eucl k => ∑ i, a i * ∏ t, g i t x) w v = ∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ∈ Finset.univ.erase u, g i t w := by
  intro k r ι _ a g w v hg
  -- Product rule for each `∏ t, g i t`, then the constant factor `a i` and the sum over `ι`.
  have hs : HasFDerivAt (fun x => ∑ i, a i * ∏ t, g i t x)
      (∑ i, a i • ∑ u, (∏ t ∈ Finset.univ.erase u, g i t w) • fderiv ℝ (g i u) w) w :=
    HasFDerivAt.fun_sum fun i _ =>
      (HasFDerivAt.finsetProd fun t _ => (hg i t).hasFDerivAt).const_mul (a i)
  -- Evaluate the derivative at `v` termwise and commute the real factors.
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  ring
/-- Algebraic core of the Piola identity: an alternating sum over permutations against a kernel
`H u` symmetric in its two arguments vanishes, since `σ ↦ σ * swap 0 u.succ` reverses the sign,
exchanges the two arguments of `H u` and fixes every other factor. -/
theorem Submission.deformation_ipl_mwc_pi_swap_cancel : ∀ (r : ℕ) (H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ) (N : Fin r → Fin (r + 1) → ℝ), (∀ u i j, H u i j = H u j i) → ∑ σ : Equiv.Perm (Fin (r + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ u : Fin r, H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) = 0 := by
  intro r H N hH
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  -- Pair `σ` with `σ * τ`, `τ = (0 u.succ)`; the terms `T σ` and `T (σ * τ)` cancel.
  let τ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 u.succ
  have hτne : (0 : Fin (r + 1)) ≠ u.succ := (Fin.succ_ne_zero u).symm
  let T : Equiv.Perm (Fin (r + 1)) → ℝ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * (H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ))
  have hT : ∀ σ : Equiv.Perm (Fin (r + 1)), T (σ * τ) = - T σ := by
    intro σ
    have h0 : (σ * τ) 0 = σ u.succ := by simp [τ, Equiv.Perm.mul_apply]
    have h1 : (σ * τ) u.succ = σ 0 := by simp [τ, Equiv.Perm.mul_apply]
    have hprod : ∏ t ∈ Finset.univ.erase u, N t ((σ * τ) t.succ) =
        ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) := by
      refine Finset.prod_congr rfl (fun t ht => ?_)
      have htu : t ≠ u := Finset.ne_of_mem_erase ht
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero t)
        (fun h => htu (Fin.succ_injective _ h))]
    have hsign : ((Equiv.Perm.sign (σ * τ) : ℤ) : ℝ) = - ((Equiv.Perm.sign σ : ℤ) : ℝ) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hτne]
      push_cast
      ring
    simp only [T]
    rw [h0, h1, hprod, hsign, hH u (σ u.succ) (σ 0)]
    ring
  have hS : ∑ σ, T σ = - ∑ σ, T σ :=
    calc ∑ σ, T σ = ∑ σ, T (σ * τ) := (Equiv.sum_comp (Equiv.mulRight τ) T).symm
      _ = ∑ σ, - T σ := Finset.sum_congr rfl (fun σ _ => hT σ)
      _ = - ∑ σ, T σ := Finset.sum_neg_distrib _
  linarith

/-- Piola identity (step (3.2)(i) of the proof of `minor_weak_continuity`; Evans, PDE, §8.1.4(b),
Lemma 1): for `C²` functions `W_0, …, W_{r-1}` on `ℝ^k` and `b : Fin (r + 1) → Fin k`, the signed
minors `c_q = (-1)^q det (∂_{b (q.succAbove s)} W_t)_{t,s}` satisfy `∑_q ∂_{b q} c_q = 0`.
By the cofactor formula `c_q = ∑_{σ 0 = q} sgn σ ∏_t ∂_{b (σ t.succ)} W_t` and the product rule,
`∑_q ∂_{b q} c_q = ∑_σ sgn σ ∑_u H_u(σ 0, σ u.succ) ∏_{t ≠ u} ∂_{b (σ t.succ)} W_t` with
`H_u(i, j) = ∂_{b i} ∂_{b j} W_u`; this vanishes since `H_u` is symmetric (Schwarz) and
`σ ↦ σ * swap 0 u.succ` changes the sign. -/
theorem Submission.deformation_ipl_mwc_piola_identity :
    ∀ (k r : ℕ) (W : Fin r → Eucl k → ℝ) (b : Fin (r + 1) → Fin k), (∀ t, ContDiff ℝ 2 (W t)) →
      ∀ w : Eucl k, ∑ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w
          (EuclideanSpace.single (b q) 1) = 0 := by
  intro k r W b hW w
  -- `D t i x = ∂_{b i} W_t (x)`, the entries of the minors; `C¹` since `W_t` is `C²`.
  let D : Fin r → Fin (r + 1) → Eucl k → ℝ := fun t i x =>
    fderiv ℝ (W t) x (EuclideanSpace.single (b i) 1)
  have hD : ∀ t i, DifferentiableAt ℝ (D t i) w := fun t i =>
    (((hW t).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero w).clm_apply
      (differentiableAt_const _)
  -- `H u i j = ∂_{b i} ∂_{b j} W_u (w)` is symmetric in `(i, j)`.
  let H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ := fun u i j =>
    fderiv ℝ (D u j) w (EuclideanSpace.single (b i) 1)
  have hH : ∀ u i j, H u i j = H u j i := fun u i j =>
    Submission.deformation_ipl_mwc_pi_hessian_symm k (W u) (hW u) w
      (EuclideanSpace.single (b j) 1) (EuclideanSpace.single (b i) 1)
  -- Cofactor formula and product rule: `∂_{b q} c_q = ∑_{σ 0 = q} sgn σ ∂_{b q} ∏_t D t (σ t.succ)`
  have hc : ∀ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w
        (EuclideanSpace.single (b q) 1) =
      ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) *
        ∑ u : Fin r, H u q (σ u.succ) * ∏ t ∈ Finset.univ.erase u, D t (σ t.succ) w := by
    intro q
    have hcof : (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) =
        fun x => ∑ σ : Equiv.Perm (Fin (r + 1)),
          (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, D t (σ t.succ) x :=
      funext fun x => Submission.deformation_ipl_mwc_pi_cofactor_leibniz r (fun t i => D t i x) q
    rw [hcof]
    exact Submission.deformation_ipl_mwc_pi_fderiv_sum_prod k r (Equiv.Perm (Fin (r + 1)))
      (fun σ => if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0)
      (fun σ t => D t (σ t.succ)) w _ fun σ t => hD t (σ t.succ)
  -- Sum over `q`: only `q = σ 0` survives, and the sum cancels in pairs `σ, σ * swap 0 u.succ`.
  refine Eq.trans ?_
    (Submission.deformation_ipl_mwc_pi_swap_cancel r H (fun t i => D t i w) hH)
  rw [Fintype.sum_congr _ _ hc, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun σ => ?_
  rw [Finset.sum_eq_single (σ 0) (fun q _ hq => by rw [ite_eq_right (Ne.symm hq), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- Integration by parts for Jacobian minors of `C²` functions (step (3.2)(ii) of the weak
continuity of Jacobian minors behind the Lipschitz push-forward limits in the proof of the
Deformation Theorem, Simon Ch. 6, 5.1): for `C²` functions `V₀, …, V_r : ℝᵏ → ℝ`, directions
`b : Fin (r + 1) → Fin k` and `φ ∈ C¹_c(ℝᵏ)`, with
`A = (∂_{b(s)} V_t)_{t,s}` and the signed first-row cofactors
`C_q = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1})_{t,s}`, `∫ φ det A = -∑_q ∫ V₀ C_q ∂_{b(q)} φ`.
Laplace expansion along row `0` gives `det A = ∑_q ∂_{b(q)} V₀ · C_q`.  The directional derivative
`∂_{b(q)}(V₀ φ C_q)` of the compactly supported `C¹` function `V₀ φ C_q` has integral `0`, and the
product rule turns this into `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`.
Summing over `q`, the last terms cancel by the Piola identity `∑_q ∂_{b(q)} C_q = 0`. -/
theorem Submission.deformation_ipl_mwc_minor_ibp_smooth :
    ∀ (k r : ℕ) (V : Fin (r + 1) → Eucl k → ℝ) (b : Fin (r + 1) → Fin k) (φ : Eucl k → ℝ),
      (∀ t, ContDiff ℝ 2 (V t)) → ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
          fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k)) =
        -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) *
          Matrix.det (Matrix.of fun t s : Fin r =>
            fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
          fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
  intro k r V b φ hV hφ hφc
  -- `C q w = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1}(w))_{t,s}`: the signed first-row cofactors.
  obtain ⟨C, hC⟩ : ∃ C : Fin (r + 1) → Eucl k → ℝ, ∀ q w, C q w = (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1)) :=
    ⟨_, fun _ _ => rfl⟩
  have hCf : ∀ q, C q = fun w => (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1)) :=
    fun q => funext (hC q)
  -- Step 1 (Laplace expansion along row `0`): `det A = ∑_q ∂_{b(q)} V₀ · C_q`.
  have hLap : ∀ w, Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
      fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) =
      ∑ q, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * C q w := by
    intro w
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hC q w, Matrix.of_apply]
    have hsub : (Matrix.of fun t s : Fin (r + 1) =>
        fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)).submatrix Fin.succ q.succAbove =
        Matrix.of fun t s : Fin r =>
          fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1) := rfl
    rw [hsub]
    ring
  -- Step 2 (regularity): the entries `∂_i V_t` and, by the Leibniz formula, the cofactors `C_q`
  -- are `C¹`.
  have hDV : ∀ t i, ContDiff ℝ 1 fun w => fderiv ℝ (V t) w (EuclideanSpace.single i 1) :=
    fun t i => ((hV t).fderiv_right (m := 1) one_add_one_eq_two.le).clm_apply contDiff_const
  have hV0 : ContDiff ℝ 1 (V 0) := (hV 0).of_le one_le_two
  have hCd : ∀ q, ContDiff ℝ 1 (C q) := by
    intro q
    rw [hCf q]
    exact contDiff_const.mul (Submission.deformation_ipl_mwc_mis_det_contDiff k r 1
      (fun t s w => fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      fun t s => hDV t.succ _)
  -- Step 3 (supports and integrability): `φ` and `Dφ` vanish off the compact set `tsupport φ`,
  -- so every continuous integrand below with a factor `φ` or `∂_i φ` is integrable.
  have hφ0 : ∀ w, w ∉ tsupport φ → φ w = 0 := fun w hw => image_eq_zero_of_notMem_tsupport hw
  have hdφ0 : ∀ w, w ∉ tsupport φ → fderiv ℝ φ w = 0 :=
    fun w hw => fderiv_of_notMem_tsupport ℝ hw
  have hcs : ∀ g : Eucl k → ℝ, (∀ w, w ∉ tsupport φ → g w = 0) → HasCompactSupport g := by
    intro g hg0
    refine hφc.mono' fun w hw => ?_
    by_contra hw'
    exact (Function.mem_support.mp hw) (hg0 w hw')
  have hint : ∀ g : Eucl k → ℝ, Continuous g → (∀ w, w ∉ tsupport φ → g w = 0) →
      Integrable g (volume : Measure (Eucl k)) :=
    fun g hg hg0 => hg.integrable_of_hasCompactSupport (hcs g hg0)
  have hcDφ : ∀ i, Continuous fun w => fderiv ℝ φ w (EuclideanSpace.single i 1) :=
    fun i => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDC : ∀ q i, Continuous fun w => fderiv ℝ (C q) w (EuclideanSpace.single i 1) :=
    fun q i => ((hCd q).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hT1 : ∀ q, Integrable (fun w => fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) *
      φ w * C q w) (volume : Measure (Eucl k)) := fun q =>
    hint _ (((hDV 0 _).continuous.mul hφ.continuous).mul (hCd q).continuous)
      fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul]
  have hT2 : ∀ q, Integrable (fun w => V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) *
      C q w) (volume : Measure (Eucl k)) := fun q =>
    hint _ ((hV0.continuous.mul (hcDφ _)).mul (hCd q).continuous)
      fun w hw => by rw [hdφ0 w hw, zero_apply, mul_zero, zero_mul]
  have hT3 : ∀ q, Integrable (fun w => V 0 w * φ w *
      fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1)) (volume : Measure (Eucl k)) := fun q =>
    hint _ ((hV0.continuous.mul hφ.continuous).mul (hcDC q _))
      fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul]
  -- Product rule for `V₀ φ C_q` in the direction `e_{b(q)}`.
  have hprod : ∀ q w, fderiv ℝ (fun y => V 0 y * φ y * C q y) w (EuclideanSpace.single (b q) 1) =
      fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w +
        V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w +
        V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
    intro q w
    have hd : HasFDerivAt (fun y => V 0 y * φ y * C q y)
        ((V 0 w * φ w) • fderiv ℝ (C q) w +
          C q w • (V 0 w • fderiv ℝ φ w + φ w • fderiv ℝ (V 0) w)) w :=
      ((hV0.differentiable one_ne_zero w).hasFDerivAt.mul
        (hφ.differentiable one_ne_zero w).hasFDerivAt).mul
        ((hCd q).differentiable one_ne_zero w).hasFDerivAt
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- Steps 4–5 (one integration by parts for each `q`): `∫ ∂_{b(q)}(V₀ φ C_q) = 0`, so
  -- `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`.
  have hq : ∀ q, ∫ w, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w =
      -(∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
        ∫ w, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
    intro q
    have h0 := Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero k
      (fun y => V 0 y * φ y * C q y) (EuclideanSpace.single (b q) 1) ((hV0.mul hφ).mul (hCd q))
      (hcs _ fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul])
    simp only [hprod q] at h0
    have h12 : Integrable (fun w => fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w +
        V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w)
        (volume : Measure (Eucl k)) := (hT1 q).add (hT2 q)
    rw [integral_add h12 (hT3 q), integral_add (hT1 q) (hT2 q)] at h0
    linarith
  -- Step 6 (Piola identity for the rows `W_t = V_{t+1}`): `∑_q ∂_{b(q)} C_q = 0`.
  have hdivC : ∀ w, ∑ q, fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) = 0 := by
    intro w
    simp only [hCf]
    exact Submission.deformation_ipl_mwc_piola_identity k r (fun t => V t.succ) b
      (fun t => hV t.succ) w
  calc ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
          fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k))
      = ∫ w, ∑ q, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w := by
        refine integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [hLap w, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ q, ∫ w, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w :=
        integral_finsetSum _ fun q _ => hT1 q
    _ = ∑ q, (-(∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
          ∫ w, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1)) :=
        Finset.sum_congr rfl fun q _ => hq q
    _ = -(∑ q, ∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
          ∫ w, ∑ q, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
        rw [integral_finsetSum _ fun q _ => hT3 q, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    _ = -∑ q, ∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w := by
        simp only [← Finset.mul_sum, hdivC, mul_zero, integral_zero, sub_zero]
    _ = -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) *
          Matrix.det (Matrix.of fun t s : Fin r =>
            fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
          fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
        congr 1
        refine Finset.sum_congr rfl fun q _ => integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [hC q w]
        ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
