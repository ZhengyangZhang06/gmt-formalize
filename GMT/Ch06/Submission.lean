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

/-- **Diagonal selection of a weakly convergent sequence with a mass bound** (the selection in the
proof of Simon Ch. 6, Theorem 8.2, p. 176: "(8) remains valid with `T_{j'}` instead of `T`").
Let `closure W` be compact.  Suppose that for every test form `ω` supported in `W`,
`X_{k,j}(ω) → Z_k(ω)` as `j → ∞` and `Z_k(ω) → L(ω)` as `k → ∞`, and that for each `k`,
`M_W(X_{k,j}) ≤ C` for all large `j`.  Then some strictly increasing `φ` gives
`M_W(X_{k,φ(k)}) ≤ C` for every `k` and `X_{k,φ(k)}(ω) → L(ω)` for every such `ω`.  With
`C⁺ = max C 0`, the mass bound gives `|X(ω) - X(ω')| ≤ C⁺ sup |ω - ω'|`, and `Z_k`, `L` inherit
this bound in the limit.  Choose `φ(k)` with `|X_{k,φ(k)}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)` for `i ≤ k`,
where `(ωᵢ)` is a countable sup-norm-dense family.  A four-term estimate then gives convergence
for every `ω`. -/
theorem Submission.ind_diagonal_weak_limit : ∀ (P n : ℕ) (U W : Set (Eucl P)) (X : ℕ → ℕ → GeometricCurrentOn U n) (Z : ℕ → TestFormOn U n → ℝ) (L : TestFormOn U n → ℝ) (C : ℝ), IsCompact (closure W) → (∀ (k : ℕ) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun j => X k j ω) atTop (𝓝 (Z k ω))) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun k => Z k ω) atTop (𝓝 (L ω))) → (∀ k, ∀ᶠ j in atTop, (X k j).massOn W ≤ ENNReal.ofReal C) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, (X k (φ k)).massOn W ≤ ENNReal.ofReal C) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun k => X k (φ k) ω) atTop (𝓝 (L ω)) := by
  intro P n U W X Z L C hW hXZ hZL hmass
  classical
  -- Step 1 (mass estimate): if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ M`
  -- everywhere (Euclidean covector norm), then `|T(ω)| ≤ B M`.
  have hF1 : ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B M : ℝ), 0 ≤ B →
      T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ M) →
      |T ω| ≤ B * M := by
    intro T ω B M hB hM hWω hMω
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
    -- `M ≥ 0`, by evaluating the pointwise bound at `0`.
    have hM0 : 0 ≤ M := (covectorEuclideanNorm_nonneg _).trans (hMω 0)
    -- For every `c > M`, both `±c⁻¹ ω` are mass-admissible for `W`, hence `|T ω| ≤ B c`.
    have key : ∀ c, M < c → |T ω| ≤ B * c := by
      intro c hc
      have hc0 : 0 < c := hM0.trans_lt hc
      have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * T ω ≤ B := by
        intro s hs
        have hadm : s • ω ∈ massAdmissibleOn U n W := by
          refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hWω, fun x => ?_⟩
          change covectorEuclideanNorm (s • (ω : DifferentialForm (Eucl P) n) x) ≤ 1
          rw [hsmul, hs, inv_mul_le_iff₀ hc0, mul_one]
          exact (hMω x).trans hc.le
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
    -- Let `c ↓ M`: take `c = M + ε / (B + 1)`.
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hB1 : 0 < B + 1 := by linarith
    have hδ : 0 < ε / (B + 1) := div_pos hε hB1
    have hBδ : B * (ε / (B + 1)) ≤ ε := by
      calc B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hδ.le
        _ = ε := by field_simp
    have := key (M + ε / (B + 1)) (by linarith)
    calc |T ω| ≤ B * (M + ε / (B + 1)) := this
      _ = B * M + B * (ε / (B + 1)) := by ring
      _ ≤ B * M + ε := by linarith
  -- Step 2 (separability): a countable family `E` of test forms supported in `W` is dense, in the
  -- sup of the Euclidean coefficient norm, among all test forms supported in `W`.  The
  -- coefficient vector `c(α) = (α(e_{I 0}, …, e_{I (n-1)}))_I ∈ ℝ^(Fin n → Fin P)` satisfies
  -- `|α| ≤ √N ‖c(α)‖_∞`; for each accuracy `1/(m+1)` and scale `1/(j+1)`, the forms whose
  -- coefficients oscillate by less than `1/(m+1)` at scale `1/(j+1)` are approximated through
  -- their values on a finite `1/(j+1)`-net of `closure W`.
  have hdense : ∃ E : Set (TestFormOn U n), E.Countable ∧
      (∀ η ∈ E, tsupport (η : DifferentialForm (Eucl P) n) ⊆ W) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → ∀ ε : ℝ, 0 < ε →
        ∃ η ∈ E, ∀ x, covectorEuclideanNorm
          ((ω : DifferentialForm (Eucl P) n) x - (η : DifferentialForm (Eucl P) n) x) ≤ ε := by
    -- The coefficient map `c` and the estimate `|α| ≤ √N ‖c α‖_∞`.
    let c : Covector (Eucl P) n → (Fin n → Fin P) → ℝ :=
      fun α I => α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
    have hc_cont : Continuous c := continuous_pi fun I => by fun_prop
    have hc_sub : ∀ α γ, c (α - γ) = c α - c γ := fun α γ => by funext I; simp [c]
    have hc_zero : c 0 = 0 := by funext I; simp [c]
    set N : ℝ := Real.sqrt (Fintype.card (Fin n → Fin P)) with hN_def
    have hN : 0 ≤ N := Real.sqrt_nonneg _
    have hcmp : ∀ α, covectorEuclideanNorm α ≤ N * ‖c α‖ := by
      intro α
      unfold covectorEuclideanNorm
      rw [hN_def, ← Real.sqrt_sq (norm_nonneg (c α)), ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      calc ∑ I : Fin n → Fin P,
            (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
          ≤ ∑ _I : Fin n → Fin P, ‖c α‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · have h : |c α I| ≤ ‖c α‖ := by
                simpa [Real.norm_eq_abs] using norm_le_pi_norm (c α) I
              calc (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 = |c α I| ^ 2 :=
                    (sq_abs _).symm
                _ ≤ ‖c α‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
            · positivity
        _ = (Fintype.card (Fin n → Fin P) : ℝ) * ‖c α‖ ^ 2 := by simp
    -- Test forms supported in `W` vanish off `closure W`.
    let D : Set (TestFormOn U n) := {ω | tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W}
    have hzero : ∀ ω ∈ D, ∀ x ∉ closure W, (ω : DifferentialForm (Eucl P) n) x = 0 :=
      fun ω hω x hx => image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hω h))
    -- Finite `1/(j+1)`-nets of the compact set `closure W`.
    have hnet : ∀ j : ℕ, ∃ t : Finset (Eucl P),
        closure W ⊆ ⋃ y ∈ t, Metric.ball y (1 / ((j : ℝ) + 1)) := by
      intro j
      obtain ⟨t, -, ht, hcov⟩ := hW.finite_cover_balls (e := 1 / ((j : ℝ) + 1)) (by positivity)
      exact ⟨ht.toFinset, by simpa using hcov⟩
    choose net hnet using hnet
    -- Accuracy `r = 1/(m+1)` at scale `1/(j+1)`: take a countable dense subset of the coefficient
    -- values on the net and choose preimages.
    have key : ∀ m j : ℕ, ∃ E' : Set (TestFormOn U n), E'.Countable ∧ E' ⊆ D ∧
        ∀ ω ∈ D, (∀ x y, dist x y < 1 / ((j : ℝ) + 1) →
            dist (c ((ω : DifferentialForm (Eucl P) n) x)) (c ((ω : DifferentialForm (Eucl P) n) y))
              < 1 / ((m : ℝ) + 1)) →
          ∃ η ∈ E', ∀ x, ‖c ((ω : DifferentialForm (Eucl P) n) x)
            - c ((η : DifferentialForm (Eucl P) n) x)‖ ≤ 3 / ((m : ℝ) + 1) := by
      intro m j
      set r : ℝ := 1 / ((m : ℝ) + 1) with hr_def
      have hr : 0 < r := by positivity
      let Dj : Set (TestFormOn U n) := {ω | ω ∈ D ∧ ∀ x y, dist x y < 1 / ((j : ℝ) + 1) →
        dist (c ((ω : DifferentialForm (Eucl P) n) x))
          (c ((ω : DifferentialForm (Eucl P) n) y)) < r}
      let g : TestFormOn U n → (net j → (Fin n → Fin P) → ℝ) :=
        fun ω y => c ((ω : DifferentialForm (Eucl P) n) y)
      obtain ⟨S, hSA, hSc, hAS⟩ :=
        (TopologicalSpace.IsSeparable.of_separableSpace (g '' Dj)).exists_countable_dense_subset
      have hpre : ∀ s : S, ∃ ω ∈ Dj, g ω = s := fun s => hSA s.2
      choose pick hpickD hpickg using hpre
      have : Countable S := hSc.to_subtype
      refine ⟨Set.range pick, Set.countable_range pick, ?_, ?_⟩
      · rintro _ ⟨s, rfl⟩
        exact (hpickD s).1
      · intro ω hωD hωmod
        obtain ⟨s, hsS, hdist⟩ :=
          Metric.mem_closure_iff.mp (hAS ⟨ω, ⟨hωD, hωmod⟩, rfl⟩) r hr
        set η := pick ⟨s, hsS⟩ with hη_def
        have hηD : η ∈ Dj := hpickD ⟨s, hsS⟩
        have hgη : g η = s := hpickg ⟨s, hsS⟩
        refine ⟨η, ⟨⟨s, hsS⟩, rfl⟩, fun x => ?_⟩
        by_cases hx : x ∈ closure W
        · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hnet j hx)
          have h1 := hωmod x y (Metric.mem_ball.mp hxy)
          rw [← hgη] at hdist
          have h2 : dist (c ((ω : DifferentialForm (Eucl P) n) y))
              (c ((η : DifferentialForm (Eucl P) n) y)) < r :=
            (dist_le_pi_dist (g ω) (g η) ⟨y, hy⟩).trans_lt hdist
          have h3 := hηD.2 y x (by rwa [dist_comm])
          have h4 := dist_triangle4 (c ((ω : DifferentialForm (Eucl P) n) x))
            (c ((ω : DifferentialForm (Eucl P) n) y)) (c ((η : DifferentialForm (Eucl P) n) y))
            (c ((η : DifferentialForm (Eucl P) n) x))
          rw [← dist_eq_norm, show 3 / ((m : ℝ) + 1) = r + r + r by rw [hr_def]; ring]
          linarith
        · rw [hzero ω hωD x hx, hzero η hηD.1 x hx, sub_self, norm_zero]
          positivity
    choose E' hE'c hE'D hE' using key
    refine ⟨⋃ m, ⋃ j, E' m j,
      Set.countable_iUnion fun m => Set.countable_iUnion fun j => hE'c m j, ?_, ?_⟩
    · intro η hη
      obtain ⟨m, j, hη⟩ := Set.mem_iUnion₂.mp hη
      exact hE'D m j hη
    · intro ω hω ε hε
      obtain ⟨m, hm⟩ : ∃ m : ℕ, N * (3 / ((m : ℝ) + 1)) ≤ ε := by
        obtain ⟨m, hm⟩ := exists_nat_gt (3 * N / ε)
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ hε] at hm
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      -- `c ∘ ω` is continuous with compact support, hence uniformly continuous.
      have huc : UniformContinuous (c ∘ (ω : DifferentialForm (Eucl P) n)) :=
        (ω.property.1.2.comp_left hc_zero).uniformContinuous_of_continuous
          (hc_cont.comp ω.property.1.1.continuous)
      obtain ⟨δ, hδ, hδ'⟩ :=
        Metric.uniformContinuous_iff.mp huc (1 / ((m : ℝ) + 1)) (by positivity)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      obtain ⟨η, hηE, hη⟩ := hE' m j ω hω fun x y hxy => hδ' (hxy.trans hj)
      refine ⟨η, Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨j, hηE⟩⟩, fun x => ?_⟩
      calc covectorEuclideanNorm
            ((ω : DifferentialForm (Eucl P) n) x - (η : DifferentialForm (Eucl P) n) x)
          ≤ N * ‖c ((ω : DifferentialForm (Eucl P) n) x
              - (η : DifferentialForm (Eucl P) n) x)‖ := hcmp _
        _ = N * ‖c ((ω : DifferentialForm (Eucl P) n) x)
              - c ((η : DifferentialForm (Eucl P) n) x)‖ := by rw [hc_sub]
        _ ≤ N * (3 / ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hη x) hN
        _ ≤ ε := hm
  obtain ⟨E, hEc, hEW, hEdense⟩ := hdense
  -- `E` is nonempty (it approximates `0`); enumerate it as `E = {ωᵢ : i ∈ ℕ}`.
  have hEne : E.Nonempty := by
    obtain ⟨η, hη, -⟩ := hEdense 0 (by simp) 1 one_pos
    exact ⟨η, hη⟩
  obtain ⟨e, rfl⟩ := hEc.exists_eq_range hEne
  have heW : ∀ i, tsupport (e i : DifferentialForm (Eucl P) n) ⊆ W := fun i => hEW _ ⟨i, rfl⟩
  -- `C⁺ = max C 0`.
  set C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right C 0
  have hCC' : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal (le_max_left C 0)
  -- If `M_W(T) ≤ C` and `|ω - ω'| ≤ ε` everywhere, then `|T(ω) - T(ω')| = |T(ω - ω')| ≤ C⁺ ε`.
  have hdiff : ∀ (T : GeometricCurrentOn U n) (ω ω' : TestFormOn U n) (ε : ℝ),
      T.massOn W ≤ ENNReal.ofReal C → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      tsupport (ω' : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm
        ((ω : DifferentialForm (Eucl P) n) x - (ω' : DifferentialForm (Eucl P) n) x) ≤ ε) →
      |T ω - T ω'| ≤ C' * ε := by
    intro T ω ω' ε hT hω hω' hε
    have hsupp : tsupport ((ω - ω' : TestFormOn U n) : DifferentialForm (Eucl P) n) ⊆ W :=
      (tsupport_sub _ _).trans (union_subset hω hω')
    have h := hF1 T (ω - ω') C' ε hC'0 (hT.trans hCC') hsupp hε
    have hlin : T (ω - ω') = T ω - T ω' := map_sub T.toCurrent ω ω'
    rwa [hlin] at h
  -- Step 3: the limits inherit the bound, first `Z_k` (`j → ∞`), then `L` (`k → ∞`).
  have hLlip : ∀ (ω ω' : TestFormOn U n) (ε : ℝ), tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      tsupport (ω' : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm
        ((ω : DifferentialForm (Eucl P) n) x - (ω' : DifferentialForm (Eucl P) n) x) ≤ ε) →
      |L ω - L ω'| ≤ C' * ε := by
    intro ω ω' ε hω hω' hε
    have hZ : ∀ k, |Z k ω - Z k ω'| ≤ C' * ε := fun k =>
      le_of_tendsto ((hXZ k ω hω).sub (hXZ k ω' hω')).abs
        ((hmass k).mono fun j hj => hdiff (X k j) ω ω' ε hj hω hω' hε)
    exact le_of_tendsto ((hZL ω hω).sub (hZL ω' hω')).abs (Eventually.of_forall hZ)
  -- Step 4: for each `k`, the mass bound and `|X_{k,j}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)` for all `i ≤ k`
  -- hold for all large `j`; extract a strictly increasing `φ` along them.
  have hev : ∀ k, ∀ᶠ j in atTop, (X k j).massOn W ≤ ENNReal.ofReal C ∧
      ∀ i : Fin (k + 1), |X k j (e i) - Z k (e i)| < 1 / ((k : ℝ) + 1) := by
    intro k
    refine (hmass k).and (Filter.eventually_all.2 fun i => ?_)
    exact (Metric.tendsto_nhds.1 (hXZ k (e i) (heW i)) (1 / ((k : ℝ) + 1)) (by positivity)).mono
      fun j hj => by rwa [Real.dist_eq] at hj
  obtain ⟨φ, hφmono, hφ⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφmono, fun k => (hφ k).1, fun ω hω => ?_⟩
  -- Step 5: fix `δ > 0`; approximate `ω` by some `ωᵢ` within `ε`, where `C⁺ ε < δ / 4`.
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set ε : ℝ := δ / (4 * (C' + 1)) with hε_def
  have hC1 : 0 < C' + 1 := by linarith
  have hε : 0 < ε := by positivity
  have hCε : C' * ε < δ / 4 := by
    have h : (C' + 1) * ε = δ / 4 := by
      rw [hε_def]
      field_simp
    nlinarith
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hEdense ω hω ε hε
  have hL := hLlip ω (e i) ε hω (heW i) hi
  -- For large `k ≥ i`, `|X_{k,φ(k)}(ω) - L(ω)|` is at most `|X_{k,φ(k)}(ω - ωᵢ)| ≤ C⁺ε`, plus
  -- `|X_{k,φ(k)}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)`, plus `|Z_k(ωᵢ) - L(ωᵢ)|`, plus `|L(ωᵢ) - L(ω)| ≤ C⁺ε`;
  -- each of the four terms is `< δ/4`.
  filter_upwards [Filter.eventually_ge_atTop i,
    Metric.tendsto_nhds.1 (hZL (e i) (heW i)) (δ / 4) (by positivity),
    (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 (δ / 4)
      (by positivity)] with k hik hZk hk
  obtain ⟨hmk, happ⟩ := hφ k
  have h1 := hdiff (X k (φ k)) ω (e i) ε hmk hω (heW i) hi
  have h2 : |X k (φ k) (e i) - Z k (e i)| < 1 / ((k : ℝ) + 1) :=
    happ ⟨i, Nat.lt_succ_of_le hik⟩
  rw [Real.dist_eq] at hZk ⊢
  have h1' := abs_le.1 h1
  have h2' := abs_lt.1 h2
  have h3' := abs_lt.1 hZk
  have h4' := abs_le.1 hL
  rw [abs_lt]
  constructor <;> linarith

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
