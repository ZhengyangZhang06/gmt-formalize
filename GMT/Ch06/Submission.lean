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

/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), in the quantitative form
used in the proof of Ch. 6, 8.2.  For `r > 0`, the blow-up `η_{x,r}(z) = r⁻¹(z - x)` pushes
`(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so the blow-up integral of `(M, θ)` against `f` is
`(rⁿ)⁻¹ ∫ f(η_{x,r} z) 1_M θ(z) dHⁿ(z)` (`M` is `Hⁿ`-null-measurable).  If `f = 0` off
`B_R(0)` and `|f| ≤ C`, then for `R r ≤ ρ` these integrals exist and those of `(M, θ)` and
`(M', θ')` differ by at most `C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'| dHⁿ → 0`; as
`θ x = θ' x`, the two tangent-space conditions are equivalent. -/
theorem Submission.iwl_weighted_tangent_locality :
    ∀ (P n : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P),
      NullMeasurableSet M (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M' (μHE[n] : Measure (Eucl P)) → θ x = θ' x →
      (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧
        IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) →
      (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
          ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) →
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q ↔
        HasWeightedApproximateTangentSpaceAt n M' θ' x Q := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P n M M' θ θ' x hM hM' hθx ⟨ρ, hρ, hθρ, hθ'ρ⟩ hlim Q
  -- Change of variables under `η_r = blowUpMap x r`: `∫_{η_r(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η_r dHⁿ`.
  have hcov : ∀ r : ℝ, 0 < r → ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, g y ∂(μHE[n] : Measure (Eucl P)) =
        (r ^ n)⁻¹ * ∫ z in S, g (blowUpMap x r z) ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr S g
    let e : Eucl P ≃ₜ Eucl P :=
      (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
    have he : (e : Eucl P → Eucl P) = blowUpMap x r := by
      funext z
      simp [e, blowUpMap, sub_eq_add_neg]
    have hemb : MeasurableEmbedding (blowUpMap x r) := he ▸ e.measurableEmbedding
    -- `η_r` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η_r⁻¹(B) = x + r • B`.
    have hmp : MeasurePreserving (blowUpMap x r)
        (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) μHE[n] := by
      refine ⟨hemb.measurable, ?_⟩
      ext B hB
      rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
      have hpre : blowUpMap x r ⁻¹' B = (fun z => x + z) '' ((fun z => r • z) '' B) := by
        ext z
        simp only [mem_preimage, mem_image, blowUpMap]
        constructor
        · intro hz
          exact ⟨r • r⁻¹ • (z - x), ⟨r⁻¹ • (z - x), hz, rfl⟩, by
            rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
        · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
          rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
      rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
        Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
        smul_eq_mul, ← mul_assoc]
      have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
          coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
          ENNReal.ofReal_one]
      rw [hc, one_mul]
    rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- The blow-up integrals of `(M, θ)` and `(M', θ')` against `f` differ by `o(1)` as `r ↓ 0`.
  have hkey : ∀ f : CompactlySupportedContinuousMap (Eucl P) ℝ, Tendsto (fun r : ℝ =>
      (∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P))) -
        ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[n] : Measure (Eucl P)))
      (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- `f = 0` off `B_R(0)` and `|f| ≤ C`.
    obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- `f ∘ η_r` vanishes off `B̄_{R r}(x)`.
    have hvan : ∀ r : ℝ, 0 < r → ∀ z : Eucl P, z ∉ closedBall x (R * r) →
        f (blowUpMap x r z) = 0 := by
      intro r hr z hz
      apply hfR
      rw [mem_closedBall, not_le, dist_eq_norm] at hz
      rw [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div,
        le_div_iff₀ hr]
      exact hz.le
    -- For `R r ≤ ρ`, `(f ∘ η_r) · 1_S ϑ` is integrable when `ϑ` is integrable on `S ∩ B̄_ρ(x)`.
    have hint : ∀ r : ℝ, 0 < r → R * r ≤ ρ → ∀ (S : Set (Eucl P)) (ϑ : Eucl P → ℝ),
        NullMeasurableSet S (μHE[n] : Measure (Eucl P)) →
        IntegrableOn ϑ (S ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
        Integrable (fun z => f (blowUpMap x r z) * S.indicator ϑ z)
          (μHE[n] : Measure (Eucl P)) := by
      intro r hr hRr S ϑ hS hϑ
      have hcont : Continuous fun z => f (blowUpMap x r z) :=
        f.continuous.comp ((continuous_const_smul _).comp (continuous_id.sub continuous_const))
      have h1 : IntegrableOn (fun z => f (blowUpMap x r z) * ϑ z) (S ∩ closedBall x ρ)
          (μHE[n] : Measure (Eucl P)) :=
        Integrable.bdd_mul hϑ hcont.aestronglyMeasurable (ae_of_all _ fun z => hC _)
      have h2 : IntegrableOn (fun z => f (blowUpMap x r z) * ϑ z) S
          (μHE[n] : Measure (Eucl P)) := by
        refine h1.of_ae_sdiff_eq_zero hS (ae_of_all _ fun z hz => ?_)
        have hz' : z ∉ closedBall x (R * r) := fun h =>
          hz.2 ⟨hz.1, closedBall_subset_closedBall hRr h⟩
        rw [hvan r hr z hz', zero_mul]
      refine (h2.integrable_indicator₀ hS).congr (ae_of_all _ fun z => ?_)
      exact Set.indicator_mul_right S (fun z => f (blowUpMap x r z)) ϑ
    -- `∫_{η_r(S)} f(y) ϑ(x + r y) dHⁿ(y) = (rⁿ)⁻¹ ∫ f(η_r z) 1_S ϑ(z) dHⁿ(z)`.
    have hI : ∀ r : ℝ, 0 < r → ∀ (S : Set (Eucl P)) (ϑ : Eucl P → ℝ),
        NullMeasurableSet S (μHE[n] : Measure (Eucl P)) →
        ∫ y in blowUpMap x r '' S, f y * ϑ (x + r • y) ∂(μHE[n] : Measure (Eucl P)) =
          (r ^ n)⁻¹ * ∫ z, f (blowUpMap x r z) * S.indicator ϑ z
            ∂(μHE[n] : Measure (Eucl P)) := by
      intro r hr S ϑ hS
      rw [hcov r hr S]
      simp only [hinv r hr.ne']
      rw [← integral_indicator₀ hS]
      congr 2
      funext z
      exact Set.indicator_mul_right S (fun z => f (blowUpMap x r z)) ϑ
    -- The estimate `|I_{M,θ}(r) - I_{M',θ'}(r)| ≤ C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'|`.
    have hbound : ∀ r : ℝ, 0 < r → R * r ≤ ρ →
        ‖(∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P))) -
          ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ n)⁻¹) *
          ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
            ∂(μHE[n] : Measure (Eucl P))) := by
      intro r hr hRr
      rw [hI r hr M θ hM, hI r hr M' θ' hM', ← mul_sub,
        ← integral_sub (hint r hr hRr M θ hM hθρ) (hint r hr hRr M' θ' hM' hθ'ρ), enorm_mul,
        Real.enorm_of_nonneg (by positivity), mul_left_comm]
      gcongr
      calc ‖∫ z, f (blowUpMap x r z) * M.indicator θ z - f (blowUpMap x r z) * M'.indicator θ' z
              ∂(μHE[n] : Measure (Eucl P))‖ₑ
          ≤ ∫⁻ z, ‖f (blowUpMap x r z) * M.indicator θ z -
              f (blowUpMap x r z) * M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ z, (closedBall x (R * r)).indicator
              (fun z => ENNReal.ofReal C * ‖M.indicator θ z - M'.indicator θ' z‖ₑ) z
              ∂(μHE[n] : Measure (Eucl P)) := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ closedBall x (R * r)
            · rw [Set.indicator_of_mem hz, ← mul_sub, enorm_mul, ← ofReal_norm]
              gcongr
              exact hC _
            · rw [hvan r hr z hz, zero_mul, zero_mul, sub_zero, enorm_zero]
              exact zero_le
        _ = ENNReal.ofReal C * ∫⁻ z in closedBall x (R * r),
              ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
            rw [lintegral_indicator measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [tendsto_zero_iff_enorm_tendsto_zero]
    have hupper : Tendsto (fun r : ℝ => ENNReal.ofReal C * (ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
          ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hlim R hR) (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    refine hbound r hr.1 ?_
    have := hr.2
    rw [lt_div_iff₀ hR] at this
    linarith
  constructor
  · rintro ⟨hQ, hf⟩
    refine ⟨hQ, fun f => ?_⟩
    rw [← hθx]
    simpa using (hf f).sub (hkey f)
  · rintro ⟨hQ, hf⟩
    refine ⟨hQ, fun f => ?_⟩
    rw [hθx]
    simpa using (hf f).add (hkey f)

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

theorem Submission.iwl_top_dim_integrality : ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T := by
  intro m
  classical
  /- Notation: n = m + 1, E = Eucl n, e the standard frame, dx = e₁* ∧ ⋯ ∧ eₙ*. -/
  obtain ⟨e, he⟩ : ∃ e : Fin (m+1) → Eucl (m+1), e = fun i => EuclideanSpace.single i (1:ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨dx, hdx⟩ : ∃ dx : Covector (Eucl (m+1)) (m+1),
      dx = wedgeCovectors (m+1) (fun i => (EuclideanSpace.proj i : Eucl (m+1) →L[ℝ] ℝ)) :=
    ⟨_, rfl⟩
  have hvol : (μHE[m+1] : Measure (Eucl (m+1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m+1)
  have hT0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true]
  have hbe : (⇑(EuclideanSpace.basisFun (Fin (m+1)) ℝ) : Fin (m+1) → Eucl (m+1)) = e := by
    rw [he]; funext i; simp only [EuclideanSpace.basisFun_apply]
  /- Step 1: top-degree covectors. -/
  have hdxe : dx e = 1 := by
    rw [hdx, he, wedgeCovectors_apply_det]
    have : (Matrix.of fun i j => (EuclideanSpace.proj i : Eucl (m+1) →L[ℝ] ℝ)
        (EuclideanSpace.single j (1:ℝ))) = 1 := by
      ext i j
      simp only [PiLp.proj_apply, PiLp.single_apply, Matrix.of_apply, Matrix.one_apply]
    rw [this, Matrix.det_one]
  have hP1 : ∀ (α : Covector (Eucl (m+1)) (m+1)) (v : Fin (m+1) → Eucl (m+1)),
      α v = α e * dx v := by
    intro α v
    classical
    let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis
    have hbe' : (⇑b : Fin (m+1) → Eucl (m+1)) = e := by
      rw [← hbe]; exact OrthonormalBasis.coe_toBasis _
    have h1 := AlternatingMap.eq_smul_basis_det b α.toAlternatingMap
    have h2 : α v = α ⇑b * b.det v := by
      have := congrArg (fun f => f v) h1
      simpa only [AlternatingMap.coe_mk, ContinuousMultilinearMap.coe_coe, ContinuousAlternatingMap.coe_toContinuousMultilinearMap, AlternatingMap.smul_apply, smul_eq_mul] using this
    rw [h2, hbe', hdx, wedgeCovectors_apply_det, Module.Basis.det_apply]
    congr 2
  have hP1' : ∀ (w : NVector (Eucl (m+1)) (m+1)) (α : Covector (Eucl (m+1)) (m+1)),
      w α = α e * w dx := by
    intro w α
    have hα : α = α e • dx := by
      ext v
      rw [hP1 α v]
      simp only [ContinuousAlternatingMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [hα]
    rw [map_smul, smul_eq_mul]
  have hP3 : ∀ τ : Fin (m+1) → Eucl (m+1), Orthonormal ℝ τ → dx τ = 1 ∨ dx τ = -1 := by
    intro τ hτ
    rw [hdx, wedgeCovectors_apply_det]
    set A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
      Matrix.of fun i j => (EuclideanSpace.proj i : Eucl (m+1) →L[ℝ] ℝ) (τ j) with hA
    have hAA : A.transpose * A = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply, ← (orthonormal_iff_ite.mp hτ) i j]
      simp only [PiLp.proj_apply, Matrix.transpose_apply, Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial, mul_comm, A]
    have hdet : A.det * A.det = 1 := by
      have := congrArg Matrix.det hAA
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact mul_self_eq_one_iff.mp hdet
  have hP5 : ∀ (P k : ℕ) (α : Covector (Eucl P) k) (B : ℝ), 0 ≤ B →
      (∀ I : Fin k → Fin P, |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ B) →
      covectorEuclideanNorm α ≤ Real.sqrt ((P:ℝ)^k) * B := by
    intro P k α B hB h
    unfold covectorEuclideanNorm
    rw [show Real.sqrt ((P:ℝ)^k) * B = Real.sqrt ((P:ℝ)^k * B^2) by
      rw [Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg P) k), Real.sqrt_sq hB]]
    apply Real.sqrt_le_sqrt
    calc (∑ I : Fin k → Fin P, if StrictMono I then
            (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)))^2 else 0)
          ≤ ∑ _I : Fin k → Fin P, B^2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · exact sq_le_sq' (abs_le.mp (h I)).1 (abs_le.mp (h I)).2
            · exact sq_nonneg B
      _ = (P:ℝ)^k * B^2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul, Nat.cast_pow]
  have hP6 : ∀ (P k : ℕ) (α : Covector (Eucl P) k) (c : ℝ),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro P k α c
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro I _
    split_ifs <;> simp only [EuclideanSpace.basisFun_apply, ContinuousAlternatingMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_pow, mul_zero]
  have hP7 : ∀ (ψ : Eucl (m+1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ∀ (z x : Eucl (m+1)),
      exteriorDerivative (fun y => ψ y • dx.curryLeft z) x e = fderiv ℝ ψ x z := by
    intro ψ hψ z x
    have hψd : Differentiable ℝ ψ := hψ.differentiable hT0
    have hd : DifferentiableAt ℝ (fun y => ψ y • dx.curryLeft z) x := (hψd x).smul_const _
    rw [exteriorDerivative_apply hd]
    have hterm : ∀ i : Fin (m+1),
        fderiv ℝ (fun y => (ψ y • dx.curryLeft z) (Fin.removeNth i e)) x (e i)
          = fderiv ℝ ψ x (e i) * dx (Matrix.vecCons z (Fin.removeNth i e)) := by
      intro i
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
        ContinuousAlternatingMap.curryLeft_apply_apply]
      rw [fderiv_mul_const (hψd x)]
      simp only [smul_apply, smul_eq_mul, mul_comm]
    simp only [hterm]
    have hP4 : ∀ g : Eucl (m+1) →L[ℝ] ℝ,
        ∑ i : Fin (m+1), (-1 : ℤ) ^ (i : ℕ) • (g (e i) * dx (Matrix.vecCons z (Fin.removeNth i e)))
          = g z * dx e := by
      intro g
      set F := ContinuousAlternatingMap.alternatizeUncurryFin (g.smulRight dx) with hF
      have h0 : F (Matrix.vecCons z e) = 0 := by
        apply F.toAlternatingMap.map_linearDependent
        intro hli
        have := hli.fintype_card_le_finrank
        simp only [Fintype.card_fin, finrank_euclideanSpace, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this
      have hrem : ∀ i : Fin (m+1), Fin.removeNth i.succ (Matrix.vecCons z e) =
          Matrix.vecCons z (Fin.removeNth i e) := by
        intro i
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.removeNth_apply, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Fin.succAbove_ne_zero_zero, Matrix.cons_val_zero]
        · simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ, Matrix.cons_val_succ]
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ] at h0
      simp only [hrem, ContinuousLinearMap.smulRight_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.removeNth_zero, ContinuousAlternatingMap.smul_apply, Fin.val_zero,
        pow_zero, one_smul, Fin.val_succ, pow_succ] at h0
      rw [show Fin.tail (Matrix.vecCons z e) = e from Fin.tail_cons _ _] at h0
      have h1 : ∀ x : Fin (m+1),
          ((-1 : ℤ) ^ (x : ℕ) * -1) • g (e x) • dx (Matrix.vecCons z (x.removeNth e))
            = -((-1 : ℤ) ^ (x : ℕ) • (g (e x) * dx (Matrix.vecCons z (x.removeNth e)))) := by
        intro x; rw [mul_neg_one, neg_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_neg_distrib, smul_eq_mul] at h0
      linarith
    rw [hP4, hdxe, mul_one]
  have hcoef_bd : ∀ (z : Eucl (m+1)) (I : Fin m → Fin (m+1)),
      |dx.curryLeft z (fun i => EuclideanSpace.basisFun (Fin (m+1)) ℝ (I i))| ≤ ‖dx‖ * ‖z‖ := by
    intro z I
    rw [ContinuousAlternatingMap.curryLeft_apply_apply]
    refine (dx.le_opNorm _).trans (le_of_eq ?_)
    rw [Fin.prod_univ_succ]
    simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one]
  obtain ⟨κ, hκ0, hκN⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ z : Eucl (m+1),
      covectorEuclideanNorm (dx.curryLeft z) ≤ κ * ‖z‖ := by
    obtain ⟨κ₀, hκ₀, hκ₀N⟩ : ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧ ∀ z : Eucl (m+1),
        covectorEuclideanNorm (dx.curryLeft z) ≤ κ₀ * (‖dx‖ * ‖z‖) :=
      ⟨_, Real.sqrt_nonneg _, fun z => hP5 (m+1) m (dx.curryLeft z) (‖dx‖ * ‖z‖)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hcoef_bd z)⟩
    refine ⟨κ₀ * ‖dx‖ + 1, add_pos_of_nonneg_of_pos (mul_nonneg hκ₀ (norm_nonneg _)) one_pos,
      fun z => (hκ₀N z).trans ?_⟩
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg z)
  /- Test forms `a • c` and the mass bound. -/
  have hform : ∀ (U' : Set (Eucl (m+1))) (k : ℕ) (a : Eucl (m+1) → ℝ) (c : Covector (Eucl (m+1)) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U' →
      ∃ ω : TestFormOn U' k, ∀ x, (ω : DifferentialForm (Eucl (m+1)) k) x = a x • c := by
    intro U' k a c ha hac haU
    exact ⟨⟨fun x => a x • c, ⟨⟨ha.smul contDiff_const, hac.smul_right⟩,
      (tsupport_smul_subset_left _ _).trans haU⟩⟩, fun x => rfl⟩
  have hmassb : ∀ (U' : Set (Eucl (m+1))) (k : ℕ) (S : GeometricCurrentOn U' k)
      (W : Set (Eucl (m+1))) (ω : TestFormOn U' k) (C : ℝ), 0 < C →
      tsupport (ω : DifferentialForm (Eucl (m+1)) k) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m+1)) k) x) ≤ C) →
      S.massOn W ≠ ⊤ → |S ω| ≤ C * (S.massOn W).toReal := by
    intro U' k S W ω C hC hωW hωC hfin
    have hle : ∀ s : ℝ, |s| = 1 → s * S ω ≤ C * (S.massOn W).toReal := by
      intro s hs
      have hadm : ((C⁻¹ * s) • ω) ∈ massAdmissibleOn U' k W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => C⁻¹ * s) _).trans hωW, fun x => ?_⟩
        change covectorEuclideanNorm ((C⁻¹ * s) • (ω : DifferentialForm (Eucl (m+1)) k) x) ≤ 1
        rw [hP6, abs_mul, hs, mul_one, abs_of_pos (inv_pos.2 hC), inv_mul_le_iff₀ hC, mul_one]
        exact hωC x
      have h := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (S.le_massOn hadm)
      rw [map_smul, smul_eq_mul] at h
      calc s * S ω = C * (C⁻¹ * s * S ω) := by rw [mul_assoc C⁻¹, mul_inv_cancel_left₀ hC.ne']
        _ ≤ C * (S.massOn W).toReal := mul_le_mul_of_nonneg_left h hC.le
    have h1 := hle (-1) (by rw [abs_neg, abs_one])
    have h2 := hle 1 abs_one
    rw [neg_one_mul] at h1
    rw [one_mul] at h2
    exact abs_le.2 ⟨by linarith only [h1], h2⟩
  /- Step 3(i): L¹ duality against smooth test functions. -/
  have hL5 : ∀ (f : Eucl (m+1) → ℝ) (K V : Set (Eucl (m+1))) (c : ℝ), Measurable f →
    IsCompact K → IsOpen V → K ⊆ V →
    (∀ K' : Set (Eucl (m+1)), IsCompact K' → K' ⊆ V → IntegrableOn f K') →
    (∀ ψ : Eucl (m+1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∀ x, |ψ x| ≤ 1) → ∫ x, f x * ψ x ≤ c) →
    ∫⁻ x in K, ‖f x‖ₑ ≤ ENNReal.ofReal c := by
    intro f K V c hf hK hV hKV hint hdual
    obtain ⟨r, hr0, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
    have hK₁ : IsCompact (cthickening r K) := hK.cthickening
    have hfK₁ : IntegrableOn f (cthickening r K) := hint _ hK₁ hrV
    -- Claim A: disjoint compact pieces
    have claimA : ∀ C₁ C₂ : Set (Eucl (m+1)), IsCompact C₁ → IsCompact C₂ → C₁ ⊆ K → C₂ ⊆ K →
        Disjoint C₁ C₂ → (∫ x in C₁, f x) - (∫ x in C₂, f x) ≤ c := by
      intro C₁ C₂ hC₁ hC₂ hC₁K hC₂K hC12
      obtain ⟨δ, hδ0, hδ⟩ := hC12.exists_thickenings hC₁ hC₂.isClosed
      let u : ℕ → ℝ := fun k => min δ r / (k + 2)
      have hu : u = (fun k => min δ r / (k + 2) : ℕ → ℝ) := rfl
      have hu0 : ∀ k, 0 < u k := fun k => div_pos (lt_min hδ0 hr0)
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) two_pos)
      have huδ : ∀ k, u k ≤ δ := fun k => (div_le_self (lt_min hδ0 hr0).le
        (le_add_of_nonneg_of_le (Nat.cast_nonneg k) one_le_two)).trans (min_le_left _ _)
      have hur : ∀ k, u k ≤ r := fun k => (div_le_self (lt_min hδ0 hr0).le
        (le_add_of_nonneg_of_le (Nat.cast_nonneg k) one_le_two)).trans (min_le_right _ _)
      have hulim : Tendsto u atTop (𝓝 0) := by
        have : Tendsto (fun k : ℕ => ((k:ℝ) + 2)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        simpa only [u, div_eq_mul_inv, mul_zero] using this.const_mul (min δ r)
      have hg : ∀ (C : Set (Eucl (m+1))), IsClosed C → ∀ k, ∃ g : Eucl (m+1) → ℝ,
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ range g ⊆ Icc 0 1 ∧ Function.support g = thickening (u k) C ∧ ∀ x, x ∈ C ↔ g x = 1 := by
        intro C hC k
        exact exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
          isOpen_thickening hC (self_subset_thickening (hu0 k) C)
      choose g₁ hg₁s hg₁r hg₁supp hg₁1 using hg C₁ hC₁.isClosed
      choose g₂ hg₂s hg₂r hg₂supp hg₂1 using hg C₂ hC₂.isClosed
      have hdisjk : ∀ k, Disjoint (thickening (u k) C₁) (thickening (u k) C₂) := fun k =>
        hδ.mono (thickening_mono (huδ k) _) (thickening_mono (huδ k) _)
      have hrange : ∀ (g : ℕ → Eucl (m+1) → ℝ), (∀ k, range (g k) ⊆ Icc 0 1) → ∀ k x,
          0 ≤ g k x ∧ g k x ≤ 1 := fun g h k x => h k (mem_range_self x)
      let ψ : ℕ → Eucl (m+1) → ℝ := fun k x => g₁ k x - g₂ k x
      have hψ : ψ = fun k x => g₁ k x - g₂ k x := rfl
      have hsuppψ : ∀ k, Function.support (ψ k) ⊆ thickening (u k) K := by
        intro k x hx
        by_contra hxK
        have h1 : g₁ k x = 0 := by
          by_contra h; exact hxK (thickening_subset_of_subset _ hC₁K ((hg₁supp k) ▸ h))
        have h2 : g₂ k x = 0 := by
          by_contra h; exact hxK (thickening_subset_of_subset _ hC₂K ((hg₂supp k) ▸ h))
        exact hx (by simp only [h1, h2, sub_self, ψ])
      have htsuppψ : ∀ k, tsupport (ψ k) ⊆ cthickening r K := fun k =>
        (closure_mono (hsuppψ k)).trans ((closure_thickening_subset_cthickening _ _).trans
          (cthickening_mono (hur k) _))
      have hψbound : ∀ k x, |ψ k x| ≤ 1 := by
        intro k x
        have a1 := hrange g₁ hg₁r k x
        have a2 := hrange g₂ hg₂r k x
        by_cases hx1 : g₁ k x = 0
        · simp only [ψ, hx1, zero_sub, abs_neg]; rw [abs_of_nonneg a2.1]; exact a2.2
        · have hx2 : g₂ k x = 0 := by
            by_contra h
            have m1 : x ∈ thickening (u k) C₁ := (hg₁supp k) ▸ hx1
            have m2 : x ∈ thickening (u k) C₂ := (hg₂supp k) ▸ h
            exact (hdisjk k).le_bot ⟨m1, m2⟩
          simp only [ψ, hx2, sub_zero]; rw [abs_of_nonneg a1.1]; exact a1.2
      have hle : ∀ k, ∫ x, f x * ψ k x ≤ c := fun k =>
        hdual (ψ k) ((hg₁s k).sub (hg₂s k))
          (IsCompact.of_isClosed_subset hK₁ (isClosed_tsupport _) (htsuppψ k))
          ((htsuppψ k).trans hrV) (hψbound k)
      -- pointwise limit
      have hlim : ∀ x, Tendsto (fun k => f x * ψ k x) atTop
          (𝓝 (f x * (C₁.indicator 1 x - C₂.indicator 1 x))) := by
        intro x
        apply Tendsto.const_mul
        by_cases hx1 : x ∈ C₁
        · have hx2 : x ∉ C₂ := fun h => hC12.le_bot ⟨hx1, h⟩
          have : ∀ k, ψ k x = 1 := by
            intro k
            have e1 : g₁ k x = 1 := (hg₁1 k x).1 hx1
            have e2 : g₂ k x = 0 := by
              by_contra h
              have m2 : x ∈ thickening (u k) C₂ := (hg₂supp k) ▸ h
              exact (hdisjk k).le_bot ⟨self_subset_thickening (hu0 k) _ hx1, m2⟩
            simp only [e1, e2, sub_zero, ψ]
          simp only [this, indicator_of_mem hx1, indicator_of_notMem hx2]
          simp only [Pi.one_apply, sub_zero, tendsto_const_nhds_iff]
        · by_cases hx2 : x ∈ C₂
          · have : ∀ k, ψ k x = -1 := by
              intro k
              have e2 : g₂ k x = 1 := (hg₂1 k x).1 hx2
              have e1 : g₁ k x = 0 := by
                by_contra h
                have m1 : x ∈ thickening (u k) C₁ := (hg₁supp k) ▸ h
                exact (hdisjk k).le_bot ⟨m1, self_subset_thickening (hu0 k) _ hx2⟩
              simp only [e1, e2, zero_sub, ψ]
            simp only [this, indicator_of_mem hx2, indicator_of_notMem hx1]
            simp only [Pi.one_apply, zero_sub, tendsto_const_nhds_iff]
          · simp only [indicator_of_notMem hx1, indicator_of_notMem hx2, sub_zero]
            have hev : ∀ (C : Set (Eucl (m+1))) (g : ℕ → Eucl (m+1) → ℝ), IsClosed C → x ∉ C →
                (∀ k, Function.support (g k) = thickening (u k) C) → ∀ᶠ k in atTop, g k x = 0 := by
              intro C g hC hxC hgs
              obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε C := by
                rw [← hC.closure_eq, closure_eq_iInter_thickening C] at hxC
                simpa only [mem_iInter, not_forall, not_imp, exists_prop] using hxC
              filter_upwards [(tendsto_order.1 hulim).2 _ εpos] with k hk
              rw [← Function.notMem_support, hgs]
              exact fun h => hε (thickening_mono hk.le C h)
            apply tendsto_const_nhds.congr'
            filter_upwards [hev C₁ g₁ hC₁.isClosed hx1 hg₁supp, hev C₂ g₂ hC₂.isClosed hx2 hg₂supp]
              with k h1 h2
            simp only [h1, h2, sub_self, ψ]
      have hdom : Tendsto (fun k => ∫ x, f x * ψ k x) atTop
          (𝓝 (∫ x, f x * (C₁.indicator 1 x - C₂.indicator 1 x))) := by
        refine tendsto_integral_of_dominated_convergence (fun x => (cthickening r K).indicator
          (fun x => ‖f x‖) x) (fun k => ?_) ?_ (fun k => ?_) (Eventually.of_forall hlim)
        · exact hf.aestronglyMeasurable.mul
            ((hg₁s k).continuous.sub (hg₂s k).continuous).aestronglyMeasurable
        · exact (integrable_indicator_iff hK₁.measurableSet).2 hfK₁.norm
        · refine Eventually.of_forall (fun x => ?_)
          by_cases hx : x ∈ cthickening r K
          · rw [indicator_of_mem hx, norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hψbound k x)
          · have : ψ k x = 0 := by
              by_contra h
              exact hx ((subset_tsupport _).trans (htsuppψ k) h)
            simp only [this, mul_zero, norm_zero, Real.norm_eq_abs, indicator_of_notMem hx, Std.le_refl]
      have hval : ∫ x, f x * (C₁.indicator 1 x - C₂.indicator 1 x) =
          (∫ x in C₁, f x) - (∫ x in C₂, f x) := by
        have e : (fun x => f x * (C₁.indicator 1 x - C₂.indicator 1 x)) =
            fun x => C₁.indicator f x - C₂.indicator f x := by
          funext x
          by_cases h1 : x ∈ C₁ <;> by_cases h2 : x ∈ C₂ <;> simp only [h1, indicator_of_mem, Pi.one_apply, h2, sub_self, mul_zero, not_false_eq_true, indicator_of_notMem, sub_zero, mul_one, zero_sub, mul_neg]
        rw [e, integral_sub ((integrable_indicator_iff hC₁.measurableSet).2 (hint C₁ hC₁ (hC₁K.trans hKV)))
          ((integrable_indicator_iff hC₂.measurableSet).2 (hint C₂ hC₂ (hC₂K.trans hKV))),
          integral_indicator hC₁.measurableSet, integral_indicator hC₂.measurableSet]
      rw [← hval]
      exact le_of_tendsto' hdom hle
    -- inner regularity and absolute continuity
    have hfK : IntegrableOn f K := hint K hK hKV
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    let F : Eucl (m+1) → ℝ≥0∞ := K.indicator (fun x => ‖f x‖ₑ)
    have hF : F = K.indicator (fun x => ‖f x‖ₑ) := rfl
    have hFfin : ∫⁻ x, F x ≠ ⊤ := by
      rw [lintegral_indicator hK.measurableSet]
      exact hfK.hasFiniteIntegral.ne
    have hε2 : ((ε : ℝ≥0∞) / 2) ≠ 0 := by
      simpa only [ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, ENNReal.ofNat_ne_top, or_false] using hε.ne'
    obtain ⟨η, hη0, hη⟩ := exists_pos_setLIntegral_lt_of_measure_lt hFfin hε2
    let Pset := K ∩ {x | 0 ≤ f x}
    have hPset : Pset = K ∩ {x | 0 ≤ f x} := rfl
    let Nset := K ∩ {x | f x < 0}
    have hNset : Nset = K ∩ {x | f x < 0} := rfl
    have hPm : MeasurableSet Pset := hK.measurableSet.inter (measurableSet_le measurable_const hf)
    have hNm : MeasurableSet Nset := hK.measurableSet.inter (measurableSet_lt hf measurable_const)
    have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
    obtain ⟨C₁, hC₁P, hC₁, hC₁η⟩ := hPm.exists_isCompact_sdiff_lt
      (measure_ne_top_of_subset inter_subset_left hKfin) hη0.ne'
    obtain ⟨C₂, hC₂N, hC₂, hC₂η⟩ := hNm.exists_isCompact_sdiff_lt
      (measure_ne_top_of_subset inter_subset_left hKfin) hη0.ne'
    have hC₁K : C₁ ⊆ K := hC₁P.trans inter_subset_left
    have hC₂K : C₂ ⊆ K := hC₂N.trans inter_subset_left
    have hdisj : Disjoint C₁ C₂ := by
      rw [Set.disjoint_left]
      intro x h1 h2
      have a1 : 0 ≤ f x := (hC₁P h1).2
      have a2 : f x < 0 := (hC₂N h2).2
      exact absurd a1 (not_le.2 a2)
    have hA := claimA C₁ C₂ hC₁ hC₂ hC₁K hC₂K hdisj
    -- the remainders are small
    have hrem : ∀ A : Set (Eucl (m+1)), MeasurableSet A → A ⊆ K → volume A < η →
        ∫⁻ x in A, ‖f x‖ₑ < (ε : ℝ≥0∞) / 2 := by
      intro A hAm hAK hAη
      calc ∫⁻ x in A, ‖f x‖ₑ = ∫⁻ x in A, F x :=
            setLIntegral_congr_fun hAm (fun x hx => by simp only [indicator_of_mem (hAK hx), F])
        _ < (ε : ℝ≥0∞) / 2 := hη A hAη
    have r1 := hrem (Pset \ C₁) (hPm.diff hC₁.measurableSet) (sdiff_subset.trans inter_subset_left) hC₁η
    have r2 := hrem (Nset \ C₂) (hNm.diff hC₂.measurableSet) (sdiff_subset.trans inter_subset_left) hC₂η
    have e1 : ∫⁻ x in C₁, ‖f x‖ₑ = ENNReal.ofReal (∫ x in C₁, f x) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hint C₁ hC₁ (hC₁K.trans hKV))
        ((ae_restrict_iff' hC₁.measurableSet).2 (Eventually.of_forall (fun x hx => (hC₁P hx).2)))]
      exact setLIntegral_congr_fun hC₁.measurableSet (fun x hx => by
        rw [Real.enorm_of_nonneg (hC₁P hx).2])
    have e2 : ∫⁻ x in C₂, ‖f x‖ₑ = ENNReal.ofReal (-(∫ x in C₂, f x)) := by
      have hneg : IntegrableOn (fun x => -f x) C₂ := (hint C₂ hC₂ (hC₂K.trans hKV)).neg
      rw [← integral_neg, ofReal_integral_eq_lintegral_ofReal hneg
        ((ae_restrict_iff' hC₂.measurableSet).2 (Eventually.of_forall (fun x hx =>
          (neg_nonneg.2 (hC₂N hx).2.le))))]
      refine setLIntegral_congr_fun hC₂.measurableSet (fun x hx => ?_)
      rw [← enorm_neg (f x), Real.enorm_of_nonneg (neg_nonneg.2 (hC₂N hx).2.le)]
    have hKsplit : K = (C₁ ∪ (Pset \ C₁)) ∪ (C₂ ∪ (Nset \ C₂)) := by
      ext x
      constructor
      · intro hx
        by_cases h : 0 ≤ f x
        · by_cases h1 : x ∈ C₁
          · exact Or.inl (Or.inl h1)
          · exact Or.inl (Or.inr ⟨⟨hx, h⟩, h1⟩)
        · by_cases h2 : x ∈ C₂
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨⟨hx, lt_of_not_ge h⟩, h2⟩)
      · rintro ((h | h) | (h | h))
        · exact hC₁K h
        · exact h.1.1
        · exact hC₂K h
        · exact h.1.1
    have hle1 : ∫⁻ x in K, ‖f x‖ₑ ≤ ((∫⁻ x in C₁, ‖f x‖ₑ) + (∫⁻ x in Pset \ C₁, ‖f x‖ₑ)) +
        ((∫⁻ x in C₂, ‖f x‖ₑ) + (∫⁻ x in Nset \ C₂, ‖f x‖ₑ)) := by
      conv_lhs => rw [hKsplit]
      refine (lintegral_union_le (fun x => ‖f x‖ₑ) _ _).trans (add_le_add ?_ ?_)
      · exact lintegral_union_le (fun x => ‖f x‖ₑ) C₁ (Pset \ C₁)
      · exact lintegral_union_le (fun x => ‖f x‖ₑ) C₂ (Nset \ C₂)
    have hsum : ENNReal.ofReal (∫ x in C₁, f x) + ENNReal.ofReal (-(∫ x in C₂, f x)) ≤ ENNReal.ofReal c := by
      have p1 : 0 ≤ ∫ x in C₁, f x := setIntegral_nonneg hC₁.measurableSet (fun x hx => (hC₁P hx).2)
      have p2 : 0 ≤ -(∫ x in C₂, f x) :=
        neg_nonneg.2 (setIntegral_nonpos hC₂.measurableSet (fun x hx => (hC₂N hx).2.le))
      rw [← ENNReal.ofReal_add p1 p2, ← sub_eq_add_neg]
      exact ENNReal.ofReal_le_ofReal hA
    calc ∫⁻ x in K, ‖f x‖ₑ ≤ ((∫⁻ x in C₁, ‖f x‖ₑ) + (∫⁻ x in Pset \ C₁, ‖f x‖ₑ)) +
        ((∫⁻ x in C₂, ‖f x‖ₑ) + (∫⁻ x in Nset \ C₂, ‖f x‖ₑ)) := hle1
      _ ≤ (ENNReal.ofReal (∫ x in C₁, f x) + (ε : ℝ≥0∞) / 2) +
          (ENNReal.ofReal (-(∫ x in C₂, f x)) + (ε : ℝ≥0∞) / 2) := by
        exact add_le_add (add_le_add e1.le r1.le) (add_le_add e2.le r2.le)
      _ = (ENNReal.ofReal (∫ x in C₁, f x) + ENNReal.ofReal (-(∫ x in C₂, f x))) +
          ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := add_add_add_comm _ _ _ _
      _ ≤ ENNReal.ofReal c + ε := add_le_add hsum (ENNReal.add_halves _).le
  /- Step 3(ii) / Remark 2.35: the translation estimate. -/
  have hTE : ∀ (β : Eucl (m+1) → ℝ) (K V : Set (Eucl (m+1))) (δ B : ℝ), Measurable β → IsCompact K → IsOpen V →
    0 < δ → cthickening (2 * δ) K ⊆ V →
    (∀ K' : Set (Eucl (m+1)), IsCompact K' → K' ⊆ V → IntegrableOn β K') →
    (∀ (ψ : Eucl (m+1) → ℝ) (z : Eucl (m+1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∀ x, |ψ x| ≤ 1) → |∫ x, β x * fderiv ℝ ψ x z| ≤ ‖z‖ * B) →
    ∀ z : Eucl (m+1), ‖z‖ ≤ δ → ∫⁻ x in K, ‖β x - β (x - z)‖ₑ ≤ ENNReal.ofReal (‖z‖ * B) := by
    intro β K V δ B hβ hK hV hδ hKV hint hH z hz
    -- geometry: points of the δ-thickening stay in V after a shift by t•z, |t| ≤ 1
    have hshift : ∀ y ∈ thickening δ K, ∀ t : ℝ, |t| ≤ 1 → y - t • z ∈ cthickening (2 * δ) K := by
      intro y hy t ht
      obtain ⟨x, hxK, hyx⟩ := mem_thickening_iff.1 hy
      apply mem_cthickening_of_dist_le _ x _ _ hxK
      have h1 : ‖t • z‖ ≤ δ := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖z‖ ≤ 1 * δ := mul_le_mul ht hz (norm_nonneg _) zero_le_one
          _ = δ := one_mul δ
      calc dist (y - t • z) x = ‖(y - x) - t • z‖ := by rw [dist_eq_norm, sub_right_comm]
        _ ≤ ‖y - x‖ + ‖t • z‖ := norm_sub_le _ _
        _ ≤ δ + δ := add_le_add (by rw [← dist_eq_norm]; exact hyx.le) h1
        _ = 2 * δ := (two_mul δ).symm
    have hK2 : IsCompact (cthickening (2 * δ) K) := hK.cthickening
    have hβK2 : IntegrableOn β (cthickening (2 * δ) K) := hint _ hK2 hKV
    -- integrability of the translate on compact subsets of the δ-thickening
    have htrans : ∀ K' : Set (Eucl (m+1)), IsCompact K' → K' ⊆ thickening δ K →
        IntegrableOn (fun x => β (x - z)) K' := by
      intro K' hK' hK'V
      have hS : (fun x => x - z) '' K' ⊆ cthickening (2 * δ) K := by
        rintro _ ⟨x, hx, rfl⟩
        simpa only [one_smul] using hshift x (hK'V hx) 1 abs_one.le
      have hSc : IsCompact ((fun x => x - z) '' K') := hK'.image (continuous_id.sub continuous_const)
      have hI : Integrable (((fun x => x - z) '' K').indicator β) :=
        (integrable_indicator_iff hSc.measurableSet).2 (hβK2.mono_set hS)
      refine (hI.comp_sub_right z).integrableOn.congr_fun (fun x hx => ?_) hK'.measurableSet
      simp only
      rw [indicator_of_mem (show x - z ∈ (fun x => x - z) '' K' from ⟨x, hx, rfl⟩)]
    apply hL5 (fun x => β x - β (x - z)) K (thickening δ K) (‖z‖ * B)
      (hβ.sub (hβ.comp (measurable_id.sub_const z))) hK isOpen_thickening (self_subset_thickening hδ K)
    · intro K' hK' hK'V
      exact (hint K' hK' (fun y hy => hKV (by simpa only [zero_smul, sub_zero] using hshift y (hK'V hy) 0 (abs_zero.trans_le zero_le_one)))).sub
        (htrans K' hK' hK'V)
    · intro ψ hψ hψc hψV hψ1
      have hψd : Differentiable ℝ ψ := hψ.differentiable hT0
      have hKψ : IsCompact (tsupport ψ) := hψc
      have hKψV : tsupport ψ ⊆ V := fun y hy => hKV (by simpa only [zero_smul, sub_zero] using hshift y (hψV hy) 0 (abs_zero.trans_le zero_le_one))
      -- integrability of the two products
      have hI1 : Integrable (fun x => β x * ψ x) := by
        rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
        · exact (hint _ hKψ hKψV).mul_continuousOn hψ.continuous.continuousOn hKψ
        · intro x hx; exact subset_tsupport _ (right_ne_zero_of_mul hx)
      have hI2 : Integrable (fun x => β (x - z) * ψ x) := by
        rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
        · exact (htrans _ hKψ hψV).mul_continuousOn hψ.continuous.continuousOn hKψ
        · intro x hx; exact subset_tsupport _ (right_ne_zero_of_mul hx)
      have hI3 : Integrable (fun y => β y * ψ (y + z)) := by
        have := hI2.comp_add_right z
        simpa only [add_sub_cancel_right] using this
      -- reduce to the shifted difference
      have hshiftint : ∫ x, β (x - z) * ψ x = ∫ y, β y * ψ (y + z) := by
        have := integral_sub_right_eq_self (μ := (volume : Measure (Eucl (m+1))))
          (fun y => β y * ψ (y + z)) z
        simpa only [sub_add_cancel] using this
      have hsplit : ∫ x, (β x - β (x - z)) * ψ x = -∫ y, β y * (ψ (y + z) - ψ y) := by
        have e1 : (fun x => (β x - β (x - z)) * ψ x) = fun x => β x * ψ x - β (x - z) * ψ x := by
          funext x; ring
        have e2 : (fun y => β y * (ψ (y + z) - ψ y)) = fun y => β y * ψ (y + z) - β y * ψ y := by
          funext y; ring
        rw [e1, e2, integral_sub hI1 hI2, integral_sub hI3 hI1, hshiftint]
        ring
      -- fundamental theorem of calculus along the segment
      let D : ℝ → Eucl (m+1) → ℝ := fun t y => β y * fderiv ℝ ψ (y + t • z) z
      have hD : D = fun t y => β y * fderiv ℝ ψ (y + t • z) z := rfl
      have hFTC : ∀ y, ψ (y + z) - ψ y = ∫ t in (0:ℝ)..1, fderiv ℝ ψ (y + t • z) z := by
        intro y
        have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => ψ (y + t • z))
            (fderiv ℝ ψ (y + t • z) z) t := by
          intro t _
          have h1 : HasDerivAt (fun t : ℝ => y + t • z) z t := by
            simpa only [hasDerivAt_const_add_iff, id_eq, one_smul] using ((hasDerivAt_id t).smul_const z).const_add y
          exact (hψd (y + t • z)).hasFDerivAt.comp_hasDerivAt t h1
        have hcont : Continuous (fun t : ℝ => fderiv ℝ ψ (y + t • z) z) :=
          ((hψ.continuous_fderiv hT0).comp (continuous_const.add
            (continuous_id.smul continuous_const))).clm_apply continuous_const
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
        simp only [one_smul, zero_smul, add_zero]
      -- Fubini
      obtain ⟨C, hC⟩ := (hψc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv hT0)
      have : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) 1)) :=
        isFiniteMeasure_restrict.2 (by simp only [uIoc, zero_le_one, inf_of_le_left, sup_of_le_right, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true])
      have hmem : ∀ᵐ p ∂((volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Eucl (m+1)))),
          p.1 ∈ uIoc (0:ℝ) 1 := by
        have e : (volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Eucl (m+1))) =
            ((volume : Measure ℝ).prod (volume : Measure (Eucl (m+1)))).restrict (uIoc 0 1 ×ˢ univ) := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
        rw [e]
        filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod MeasurableSet.univ)] with p hp
        exact hp.1
      have hfz : ∀ x, x ∉ tsupport ψ → fderiv ℝ ψ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
      have hDint : Integrable (Function.uncurry D) ((volume.restrict (uIoc (0:ℝ) 1)).prod volume) := by
        have hbound : Integrable (fun p : ℝ × Eucl (m+1) =>
            (C * ‖z‖) * (cthickening (2 * δ) K).indicator (fun y => ‖β y‖) p.2)
            ((volume.restrict (uIoc (0:ℝ) 1)).prod volume) := by
          have h1 : Integrable (fun _ : ℝ => C * ‖z‖) (volume.restrict (uIoc (0:ℝ) 1)) :=
            integrable_const _
          have h2 : Integrable ((cthickening (2 * δ) K).indicator (fun y => ‖β y‖)) :=
            (integrable_indicator_iff hK2.measurableSet).2 hβK2.norm
          exact h1.mul_prod h2
        refine hbound.mono' ?_ ?_
        · exact ((hβ.comp measurable_snd).aestronglyMeasurable).mul
            (((hψ.continuous_fderiv hT0).comp (continuous_snd.add
              (continuous_fst.smul continuous_const))).clm_apply continuous_const).aestronglyMeasurable
        · filter_upwards [hmem] with p hp
          rcases p with ⟨t, y⟩
          have ht1 : |t| ≤ 1 := by
            rw [uIoc_of_le zero_le_one] at hp
            rw [abs_of_pos hp.1]; exact hp.2
          simp only [Function.uncurry_apply_pair, D, norm_mul]
          by_cases hy : y ∈ cthickening (2 * δ) K
          · rw [indicator_of_mem hy]
            calc ‖β y‖ * ‖fderiv ℝ ψ (y + t • z) z‖ ≤ ‖β y‖ * (C * ‖z‖) :=
                  mul_le_mul_of_nonneg_left (((fderiv ℝ ψ (y + t • z)).le_opNorm z).trans
                    (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))) (norm_nonneg _)
              _ = C * ‖z‖ * ‖β y‖ := by ring
          · have hnot : y + t • z ∉ tsupport ψ := by
              intro h
              apply hy
              simpa only [add_sub_cancel_right] using hshift (y + t • z) (hψV h) t ht1
            rw [hfz _ hnot, indicator_of_notMem hy]
            simp only [Real.norm_eq_abs, zero_apply, norm_zero, mul_zero, Std.le_refl]
      have hswap : ∫ y, β y * (ψ (y + z) - ψ y) = ∫ t in (0:ℝ)..1, ∫ y, D t y := by
        rw [intervalIntegral_integral_swap hDint]
        congr 1
        funext y
        rw [hFTC y, ← intervalIntegral.integral_const_mul]
      have hbd : ∀ t ∈ uIoc (0:ℝ) 1, ‖∫ y, D t y‖ ≤ ‖z‖ * B := by
        intro t ht
        have ht1 : |t| ≤ 1 := by
          rw [uIoc_of_le zero_le_one] at ht
          rw [abs_of_pos ht.1]; exact ht.2
        have hts : tsupport (fun y => ψ (y + t • z)) ⊆ V := by
          have e : (fun y => ψ (y + t • z)) = ψ ∘ (Homeomorph.addRight (t • z)) := rfl
          rw [e, tsupport_comp_eq_preimage]
          intro y hy
          apply hKV
          simpa only [add_sub_cancel_right] using hshift (y + t • z) (hψV hy) t ht1
        have h := hH (fun y => ψ (y + t • z)) z (hψ.comp (contDiff_id.add contDiff_const))
          (hψc.comp_homeomorph (Homeomorph.addRight (t • z))) hts (fun x => hψ1 _)
        simp only [fderiv_comp_add_right] at h
        rw [Real.norm_eq_abs]
        exact h
      have hfinal := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      rw [hsplit, hswap]
      rw [Real.norm_eq_abs] at hfinal
      have : |∫ t in (0:ℝ)..1, ∫ y, D t y| ≤ ‖z‖ * B := by simpa only [sub_zero, abs_one, mul_one] using hfinal
      exact (neg_le_abs _).trans this
  /- Step 4 (Simon 2.6 for this sequence): the mollification Cauchy estimate. -/
  have hR4 : ∀ (β : ℕ → Eucl (m+1) → ℝ) (K V : Set (Eucl (m+1))) (δ B : ℝ),
    (∀ j, Measurable (β j)) → IsCompact K → IsOpen V → 0 < δ → cthickening δ K ⊆ V → 0 ≤ B →
    (∀ j (K' : Set (Eucl (m+1))), IsCompact K' → K' ⊆ V → IntegrableOn (β j) K') →
    (∀ j (z : Eucl (m+1)), ‖z‖ ≤ δ → ∫⁻ x in K, ‖β j x - β j (x - z)‖ₑ ≤ ENNReal.ofReal (‖z‖ * B)) →
    (∀ φ : Eucl (m+1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ closedBall 0 δ →
      (∃ A : ℝ, ∀ j, ∀ x ∈ K, |∫ y, β j y * φ (x - y)| ≤ A) ∧
      ∀ x ∈ K, ∃ L : ℝ, Tendsto (fun j => ∫ y, β j y * φ (x - y)) atTop (𝓝 L)) →
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ x in K, ‖β j x - β k x‖ₑ ≤ ENNReal.ofReal η := by
    intro β K V δ B hβ hK hV hδ hKV hB hint hTE hmoll η hη
    -- choose the scale ε
    have hB1 : 0 < B + 1 := add_pos_of_nonneg_of_pos hB one_pos
    have hη4 : 0 < η / 4 / (B + 1) := div_pos (div_pos hη four_pos) hB1
    let ε : ℝ := min δ (η / 4 / (B + 1))
    have hε0 : 0 < ε := lt_min hδ hη4
    have hεδ : ε ≤ δ := min_le_left _ _
    have hεB : ε * B ≤ η / 4 :=
      calc ε * B ≤ η / 4 / (B + 1) * (B + 1) :=
            mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one) hB hη4.le
        _ = η / 4 := div_mul_cancel₀ _ hB1.ne'
    -- normalized bump φ supported in closedBall 0 ε
    let b : ContDiffBump (0 : Eucl (m+1)) := ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩
    have hbint : Integrable (b : Eucl (m+1) → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    have hbpos : 0 < ∫ x, (b : Eucl (m+1) → ℝ) x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => b.nonneg) hbint, b.support_eq]
      exact measure_ball_pos _ _ hε0
    let I := ∫ x, (b : Eucl (m+1) → ℝ) x
    have hI : I = ∫ x, (b : Eucl (m+1) → ℝ) x := rfl
    let φ : Eucl (m+1) → ℝ := fun x => I⁻¹ * b x
    have hφ : φ = fun x => I⁻¹ * b x := rfl
    have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := contDiff_const.mul b.contDiff
    have hφc : HasCompactSupport φ := b.hasCompactSupport.mul_left
    have hφnn : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (inv_nonneg.2 hbpos.le) b.nonneg
    have hφint : ∫ x, φ x = 1 := by
      rw [hφ, integral_const_mul, ← hI, inv_mul_cancel₀ hbpos.ne']
    have hφsupp : ∀ z, φ z ≠ 0 → ‖z‖ ≤ ε := by
      intro z hz
      have : z ∈ Function.support (b : Eucl (m+1) → ℝ) := by
        intro h; exact hz (by simp only [h, mul_zero, φ])
      rw [b.support_eq] at this
      simpa only [ge_iff_le] using (mem_ball_zero_iff.1 this).le
    have hφts : tsupport φ ⊆ closedBall 0 δ := by
      refine (tsupport_mul_subset_right).trans ?_
      rw [b.tsupport_eq]
      exact closedBall_subset_closedBall hεδ
    obtain ⟨⟨A, hA⟩, hlim⟩ := hmoll φ hφs hφc hφts
    let G : ℕ → Eucl (m+1) → ℝ := fun j x => ∫ y, β j y * φ (x - y)
    have hG : G = fun j x => ∫ y, β j y * φ (x - y) := rfl
    have hφc0 : Continuous φ := hφs.continuous
    -- measurability of the mollifications
    have hGm : ∀ j, Measurable (G j) := by
      intro j
      have : StronglyMeasurable (Function.uncurry (fun x y => β j y * φ (x - y))) :=
        (((hβ j).comp measurable_snd).mul
          (hφc0.measurable.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
      exact (this.integral_prod_right).measurable
    -- mollification error, uniformly in j
    have herr : ∀ j, ∫⁻ x in K, ‖β j x - G j x‖ₑ ≤ ENNReal.ofReal (ε * B) := by
      intro j
      have hpt : ∀ x ∈ K, ‖β j x - G j x‖ₑ ≤
          ∫⁻ z, ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z) := by
        intro x hx
        -- integrability of the translated density against φ
        have hS : (fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε ⊆ V := by
          rintro _ ⟨z, hz, rfl⟩
          apply hKV
          apply mem_cthickening_of_dist_le _ x _ _ hx
          rw [dist_eq_norm]
          simpa only [sub_sub_cancel_left, norm_neg] using (mem_closedBall_zero_iff.1 hz).trans hεδ
        have hSc : IsCompact ((fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε) :=
          (isCompact_closedBall 0 ε).image (continuous_const.sub continuous_id)
        have hI0 : Integrable (((fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε).indicator (β j)) :=
          (integrable_indicator_iff hSc.measurableSet).2 (hint j _ hSc hS)
        have hI1 : IntegrableOn (fun z => β j (x - z)) (closedBall (0 : Eucl (m+1)) ε) := by
          refine (hI0.comp_sub_left x).integrableOn.congr_fun (fun z hz => ?_) measurableSet_closedBall
          simp only
          rw [indicator_of_mem (show x - z ∈ (fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε from
            ⟨z, hz, rfl⟩)]
        have hI2 : Integrable (fun z => β j (x - z) * φ z) := by
          rw [← integrableOn_iff_integrable_of_support_subset (s := closedBall (0 : Eucl (m+1)) ε)]
          · exact hI1.mul_continuousOn hφc0.continuousOn (isCompact_closedBall 0 ε)
          · intro z hz
            exact mem_closedBall_zero_iff.2 (hφsupp z (right_ne_zero_of_mul hz))
        have hI3 : Integrable (fun z => β j x * φ z) :=
          (hφc0.integrable_of_hasCompactSupport hφc).const_mul _
        have hGx : G j x = ∫ z, β j (x - z) * φ z := by
          have := integral_sub_left_eq_self (fun y => β j y * φ (x - y))
            (volume : Measure (Eucl (m+1))) x
          simpa only [sub_sub_cancel] using this.symm
        have hdiff : β j x - G j x = ∫ z, (β j x - β j (x - z)) * φ z := by
          have e : (fun z => (β j x - β j (x - z)) * φ z) = fun z => β j x * φ z - β j (x - z) * φ z := by
            funext z; ring
          rw [e, integral_sub hI3 hI2, integral_const_mul, hφint, mul_one, hGx]
        rw [hdiff]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1
        funext z
        rw [enorm_mul, Real.enorm_of_nonneg (hφnn z)]
      have hjoint : Measurable (Function.uncurry
          (fun x z => ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z))) :=
        ((((hβ j).comp measurable_fst).sub ((hβ j).comp (measurable_fst.sub measurable_snd))).enorm).mul
          (ENNReal.measurable_ofReal.comp (hφc0.measurable.comp measurable_snd))
      calc ∫⁻ x in K, ‖β j x - G j x‖ₑ
          ≤ ∫⁻ x in K, ∫⁻ z, ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z) :=
            setLIntegral_mono hjoint.lintegral_prod_right' hpt
        _ = ∫⁻ z, ∫⁻ x in K, ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z) :=
            lintegral_lintegral_swap hjoint.aemeasurable
        _ = ∫⁻ z, ENNReal.ofReal (φ z) * ∫⁻ x in K, ‖β j x - β j (x - z)‖ₑ := by
            congr 1
            funext z
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
        _ ≤ ∫⁻ z, ENNReal.ofReal (φ z) * ENNReal.ofReal (ε * B) := by
            refine lintegral_mono (fun z => ?_)
            by_cases hz : φ z = 0
            · simp only [hz, ENNReal.ofReal_zero, zero_mul, Std.le_refl]
            · gcongr
              exact (hTE j z ((hφsupp z hz).trans hεδ)).trans
                (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hφsupp z hz) hB))
        _ = ENNReal.ofReal (ε * B) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
              ← ofReal_integral_eq_lintegral_ofReal (hφc0.integrable_of_hasCompactSupport hφc)
                (Eventually.of_forall hφnn), hφint, ENNReal.ofReal_one, one_mul]
    -- Cauchy property of the mollifications in L¹(K), from pointwise convergence
    have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
    have hGG : Tendsto (fun p : ℕ × ℕ => ∫⁻ x in K, ‖G p.1 x - G p.2 x‖ₑ) atTop (𝓝 0) := by
      have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict K)
        (l := (atTop : Filter (ℕ × ℕ))) (F := fun p x => ‖G p.1 x - G p.2 x‖ₑ) (f := fun _ => 0)
        (fun _ => ENNReal.ofReal (2 * A))
        (Eventually.of_forall (fun p => ((hGm p.1).sub (hGm p.2)).enorm))
        (Eventually.of_forall (fun p => by
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          have h1 := hA p.1 x hx
          have h2 := hA p.2 x hx
          have hA0 : 0 ≤ A := (abs_nonneg _).trans h1
          calc ‖G p.1 x - G p.2 x‖ₑ ≤ ‖G p.1 x‖ₑ + ‖G p.2 x‖ₑ := enorm_sub_le
            _ ≤ ENNReal.ofReal A + ENNReal.ofReal A := by
                rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
                exact add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
            _ = ENNReal.ofReal (2 * A) := by rw [← ENNReal.ofReal_add hA0 hA0, two_mul]))
        (by rw [lintegral_const, Measure.restrict_apply_univ]
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin)
        (by
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          obtain ⟨L, hL⟩ := hlim x hx
          have h1 : Tendsto (fun p : ℕ × ℕ => G p.1 x - G p.2 x) atTop (𝓝 (L - L)) := by
            rw [← prod_atTop_atTop_eq]
            exact (hL.comp tendsto_fst).sub (hL.comp tendsto_snd)
          rw [sub_self] at h1
          have h2 := (continuous_enorm.tendsto (0 : ℝ)).comp h1
          rw [enorm_zero] at h2
          exact h2)
      simpa only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, zero_mul] using h
    have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (half_pos hη)
    obtain ⟨N2, hN2⟩ := (ENNReal.tendsto_atTop_zero.1 hGG) (ENNReal.ofReal (η / 2)) hη2
    refine ⟨max N2.1 N2.2, fun j hj k hk => ?_⟩
    have hjk : ∫⁻ x in K, ‖G j x - G k x‖ₑ ≤ ENNReal.ofReal (η / 2) :=
      hN2 (j, k) ⟨le_trans (le_max_left _ _) hj, le_trans (le_max_right _ _) hk⟩
    have hm1 : Measurable (fun x => ‖β j x - G j x‖ₑ) := ((hβ j).sub (hGm j)).enorm
    have hm2 : Measurable (fun x => ‖G j x - G k x‖ₑ) := ((hGm j).sub (hGm k)).enorm
    calc ∫⁻ x in K, ‖β j x - β k x‖ₑ
        ≤ ∫⁻ x in K, (‖β j x - G j x‖ₑ + ‖G j x - G k x‖ₑ + ‖β k x - G k x‖ₑ) := by
          refine lintegral_mono (fun x => ?_)
          calc ‖β j x - β k x‖ₑ = ‖(β j x - G j x) + (G j x - G k x) - (β k x - G k x)‖ₑ := by
                congr 1; ring
            _ ≤ ‖(β j x - G j x) + (G j x - G k x)‖ₑ + ‖β k x - G k x‖ₑ := enorm_sub_le
            _ ≤ ‖β j x - G j x‖ₑ + ‖G j x - G k x‖ₑ + ‖β k x - G k x‖ₑ :=
                add_le_add (enorm_add_le _ _) le_rfl
      _ = (∫⁻ x in K, ‖β j x - G j x‖ₑ) + (∫⁻ x in K, ‖G j x - G k x‖ₑ) +
          (∫⁻ x in K, ‖β k x - G k x‖ₑ) := by
          have hm3 : Measurable (fun x => ‖β k x - G k x‖ₑ) := ((hβ k).sub (hGm k)).enorm
          rw [lintegral_add_right _ hm3, lintegral_add_right _ hm2]
      _ ≤ ENNReal.ofReal (ε * B) + ENNReal.ofReal (η / 2) + ENNReal.ofReal (ε * B) :=
          add_le_add (add_le_add (herr j) hjk) (herr k)
      _ ≤ ENNReal.ofReal η := by
          have h0 : 0 ≤ ε * B := mul_nonneg hε0.le hB
          rw [← ENNReal.ofReal_add h0 (half_pos hη).le,
            ← ENNReal.ofReal_add (add_nonneg h0 (half_pos hη).le) h0]
          exact ENNReal.ofReal_le_ofReal (by linarith only [hεB])
  have hhalf : ∀ k : ℕ, ENNReal.ofReal ((1/2 : ℝ) ^ k) = (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hint1 : ∀ a b : ℝ, (∃ k : ℤ, a = k) → (∃ k : ℤ, b = k) → a ≠ b → (1 : ℝ≥0∞) ≤ ‖a - b‖ₑ := by
    rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩ hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    have h1 : (1 : ℝ) ≤ |(p : ℝ) - q| := by
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hpq)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.one_le_ofReal.2 h1
  /- Step 6: Lebesgue points of `βh` in the blow-up form required by the tangent locality. -/
  have hLeb : ∀ (f : Eucl (m+1) → ℝ) (C : Set (Eucl (m+1))), IsCompact C → IntegrableOn f C →
      ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), ∀ ρ : ℝ, 0 < ρ → closedBall x ρ ⊆ C → ∀ R : ℝ, 0 < R →
        Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ (m+1))⁻¹) *
          ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ) (𝓝[>] 0) (𝓝 0) := by
    intro f C hC hf
    let g := C.indicator f
    have hg : g = C.indicator f := rfl
    have hgi : Integrable g := (integrable_indicator_iff hC.measurableSet).2 hf
    have hv := (Besicovitch.vitaliFamily (volume : Measure (Eucl (m+1)))).ae_tendsto_lintegral_enorm_sub_div
      hgi.locallyIntegrable
    filter_upwards [hv] with x hx ρ hρ hxC R hR
    have hxC' : x ∈ C := hxC (mem_closedBall_self hρ.le)
    have h1 := hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (Eucl (m+1))) x)
    have hRr : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa only [mul_zero] using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hR hr
    have h2 := h1.comp hRr
    let c0 : ℝ≥0∞ := volume (ball (0 : Eucl (m+1)) 1)
    have hc0 : c0 = volume (ball (0 : Eucl (m+1)) 1) := rfl
    have hc0fin : c0 ≠ ⊤ := measure_ball_lt_top.ne
    have h3 := ENNReal.Tendsto.const_mul h2
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc0fin) :
        (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal (R ^ (m+1)) * c0 ≠ ⊤)
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (show (0:ℝ) < ρ / R from div_pos hρ hR))] with r hr hrρ
    have hr0 : 0 < r := hr
    have hr0' : r ≠ 0 := hr0.ne'
    have hRrρ : R * r ≤ ρ := (le_div_iff₀' hR).1 hrρ
    have hball : closedBall x (R * r) ⊆ C := (closedBall_subset_closedBall hRrρ).trans hxC
    have hvolB : volume (closedBall x (R * r)) = ENNReal.ofReal ((R * r) ^ (m+1)) * c0 := by
      rw [Measure.addHaar_closedBall _ _ (mul_pos hR hr0).le, finrank_euclideanSpace, Fintype.card_fin]
    have hvol0 : volume (closedBall x (R * r)) ≠ 0 := (measure_closedBall_pos _ _ (mul_pos hR hr0)).ne'
    have hvolT : volume (closedBall x (R * r)) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hint : ∫⁻ z in closedBall x (R * r), ‖g z - g x‖ₑ =
        ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ := by
      refine setLIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
      simp only [g, indicator_of_mem (hball hz), indicator_of_mem hxC']
    simp only [Function.comp_apply]
    rw [hint]
    let I := ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ
    have hI : I = ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ := rfl
    calc ENNReal.ofReal (R ^ (m+1)) * c0 * (I / volume (closedBall x (R * r)))
        = (ENNReal.ofReal ((r ^ (m+1))⁻¹) * volume (closedBall x (R * r))) *
            (I / volume (closedBall x (R * r))) := by
          congr 1
          rw [hvolB, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hr0.le _))]
          congr 2
          rw [mul_pow, mul_comm (R ^ (m+1)), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr0'),
            one_mul]
      _ = ENNReal.ofReal ((r ^ (m+1))⁻¹) * I := by
          rw [mul_assoc, ENNReal.mul_div_cancel hvol0 hvolT]
  have hconstTan : ∀ (c : ℝ) (x : Eucl (m+1)),
      HasWeightedApproximateTangentSpaceAt (m+1) (univ : Set (Eucl (m+1))) (fun _ => c) x ⊤ := by
    intro c x
    refine ⟨by simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin], fun f => ?_⟩
    have himg : ∀ r : ℝ, 0 < r →
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (univ : Set (Eucl (m+1))) = univ := by
      intro r hr
      refine eq_univ_of_forall (fun y => ⟨x + r • y, mem_univ _, ?_⟩)
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [himg r hr, Measure.restrict_univ, Submodule.top_coe, Measure.restrict_univ, integral_mul_const,
      mul_comm]
  intro U hU Tj T hTj hbd hconv
  /- A compact exhaustion of `U` (no `infDist`). -/
  obtain ⟨K, hKc, hKU, hKmono, hKcov⟩ : ∃ K : ℕ → Set (Eucl (m+1)),
      (∀ l, IsCompact (K l)) ∧ (∀ l, K l ⊆ U) ∧ (∀ l l', l ≤ l' → K l ⊆ K l') ∧
      (∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → ∃ l, C ⊆ K l) := by
    refine ⟨fun l => {x | ‖x‖ ≤ l ∧ ∀ y, y ∉ U → ((l:ℝ) + 1)⁻¹ ≤ dist x y}, fun l => ?_,
      fun l x hx => ?_, fun l l' hll' x hx => ?_, fun C hC hCU => ?_⟩
    · apply isCompact_of_isClosed_isBounded
      · have h1 : IsClosed {x : Eucl (m+1) | ‖x‖ ≤ (l:ℝ)} := isClosed_le continuous_norm continuous_const
        have h2 : IsClosed {x : Eucl (m+1) | ∀ y, y ∉ U → ((l:ℝ) + 1)⁻¹ ≤ dist x y} := by
          simp only [ofPred_forall]
          exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
            isClosed_le continuous_const (continuous_id.dist continuous_const)))
        exact h1.inter h2
      · exact (isBounded_closedBall (x := (0 : Eucl (m+1))) (r := (l:ℝ))).subset
          (fun x hx => mem_closedBall_zero_iff.2 hx.1)
    · by_contra hxU
      exact absurd ((hx.2 x hxU).trans_eq (dist_self x)) (not_le.2 (inv_pos.2 (Nat.cast_add_one_pos l)))
    · have hl : (l:ℝ) ≤ l' := Nat.cast_le.2 hll'
      exact ⟨hx.1.trans hl, fun y hy => (inv_anti₀ (Nat.cast_add_one_pos l)
        (add_le_add_left hl 1)).trans (hx.2 y hy)⟩
    · obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
      obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Eucl (m+1))
      obtain ⟨l, hl⟩ := exists_nat_gt (max R δ⁻¹)
      have h1 : ((l:ℝ) + 1)⁻¹ ≤ δ := by
        rw [inv_le_comm₀ (Nat.cast_add_one_pos l) hδ]
        exact ((le_max_right R δ⁻¹).trans hl.le).trans (le_add_of_nonneg_right zero_le_one)
      refine ⟨l, fun x hx => ⟨(mem_closedBall_zero_iff.1 (hR hx)).trans
        ((le_max_left R δ⁻¹).trans hl.le), fun y hy => ?_⟩⟩
      by_contra hlt
      exact hy (hδU (mem_cthickening_of_dist_le y x δ C hx
        (by rw [dist_comm]; exact (le_of_lt (not_le.1 hlt)).trans h1)))
  /- Step 2: every `T_j` has a Borel integer-valued locally integrable density. -/
  have hdens : ∀ j, ∃ β : Eucl (m+1) → ℝ, Measurable β ∧ (∀ x, ∃ k : ℤ, β x = k) ∧
      (∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → IntegrableOn β C) ∧
      ∀ ω : TestFormOn U (m+1),
        Tj j ω = ∫ x, β x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
    intro j
    obtain ⟨M, θ, ξ, htr, hθN, hact⟩ := hTj j
    have hMn : NullMeasurableSet M (volume : Measure (Eucl (m+1))) := by
      rw [← hvol]; exact htr.nullMeasurableSet
    obtain ⟨M', hM'M, hM'm, hMM'⟩ := hMn.exists_measurable_subset_ae_eq
    let f : Eucl (m+1) → ℝ := fun x => θ x * ξ x dx
    have hf : f = fun x => θ x * ξ x dx := rfl
    let b : Eucl (m+1) → ℝ := M'.indicator f
    have hb : b = M'.indicator f := rfl
    have hbact : ∀ ω : TestFormOn U (m+1),
        Tj j ω = ∫ x, b x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
      intro ω
      rw [hact ω, tauAction, hvol, ← setIntegral_congr_set hMM', ← integral_indicator hM'm]
      congr 1
      funext x
      by_cases hx : x ∈ M'
      · simp only [b, indicator_of_mem hx, f]
        rw [hP1' (ξ x) ((ω : DifferentialForm (Eucl (m+1)) (m+1)) x)]
        ring
      · simp only [indicator_of_notMem hx, zero_mul, b]
    have hae : ∀ᵐ x ∂(volume.restrict M'), (∃ k : ℤ, f x = k) ∧ |f x| = θ x := by
      have ho := htr.orients
      rw [hvol] at ho
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hM'M ho, ae_restrict_mem hM'm]
        with x hx hxM'
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      obtain ⟨k, hk⟩ := hθN x (hM'M hxM')
      have hθpos := htr.pos x (hM'M hxM')
      have hs : ξ x dx = 1 ∨ ξ x dx = -1 := by
        rcases hξ with h | h <;> rw [h]
        · simpa only [simpleNVector_apply] using hP3 τ hτ
        · rcases hP3 τ hτ with h' | h' <;> simp only [neg_apply, simpleNVector_apply, h', or_true, neg_neg, true_or]
      refine ⟨?_, ?_⟩
      · rcases hs with h | h
        · exact ⟨k, by simp only [hk, h, mul_one, Int.cast_natCast, f]⟩
        · exact ⟨-k, by simp only [hk, h, mul_neg, mul_one, Int.cast_neg, Int.cast_natCast, f]⟩
      · rcases hs with h | h <;> simp only [h, mul_one, abs_of_pos hθpos, f, mul_neg, abs_neg]
    have hfm : AEStronglyMeasurable f (volume.restrict M') := by
      have hξm : AEStronglyMeasurable ξ (volume.restrict M) := by
        rw [← hvol]; exact htr.aestronglyMeasurable
      have hσ : AEStronglyMeasurable (fun x => ξ x dx) (volume.restrict M) :=
        hξm.apply_continuousLinearMap dx
      have hθ : AEStronglyMeasurable θ (volume.restrict M) := by
        have hMU : M = ⋃ l, M ∩ K l := by
          ext x
          constructor
          · intro hx
            obtain ⟨l, hl⟩ := hKcov {x} isCompact_singleton (singleton_subset_iff.2 (htr.subset hx))
            exact mem_iUnion.2 ⟨l, hx, hl rfl⟩
          · intro hx
            obtain ⟨l, hl⟩ := mem_iUnion.1 hx
            exact hl.1
        rw [hMU, aestronglyMeasurable_iUnion_iff]
        intro l
        have := htr.integrableOn (K l) (hKc l) (hKU l)
        rw [hvol] at this
        exact this.aestronglyMeasurable
      exact (hθ.mul hσ).mono_measure (Measure.restrict_mono hM'M le_rfl)
    have hbm : AEStronglyMeasurable b volume := (aestronglyMeasurable_indicator_iff hM'm).2 hfm
    have hbi : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → IntegrableOn b C := by
      intro C hC hCU
      have hθi := htr.integrableOn C hC hCU
      rw [hvol] at hθi
      have hfi : IntegrableOn f (M' ∩ C) := by
        refine (hθi.mono_set (inter_subset_inter_left _ hM'M)).mono' ?_ ?_
        · exact hfm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
        · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae] with x hx
          rw [Real.norm_eq_abs, hx.2]
      exact IntegrableOn.integrable_indicator
        (by rw [IntegrableOn, Measure.restrict_restrict hM'm]; exact hfi) hM'm
    obtain ⟨b', hb'm, hbb'⟩ : ∃ b' : Eucl (m+1) → ℝ, StronglyMeasurable b' ∧ b =ᵐ[volume] b' :=
      ⟨hbm.mk b, hbm.stronglyMeasurable_mk, hbm.ae_eq_mk⟩
    have hbz : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), ∃ k : ℤ, b x = k := by
      have h1 : ∀ᵐ x ∂(volume.restrict M'), ∃ k : ℤ, b x = k := by
        filter_upwards [hae, ae_restrict_mem hM'm] with x hx hxM'
        obtain ⟨k, hk⟩ := hx.1
        exact ⟨k, by simp only [indicator_of_mem hxM', hk, b]⟩
      have h2 : ∀ᵐ x ∂(volume.restrict M'ᶜ), ∃ k : ℤ, b x = k := by
        filter_upwards [ae_restrict_mem hM'm.compl] with x hx
        exact ⟨0, by simp only [indicator_of_notMem hx, Int.cast_zero, b]⟩
      exact ae_of_ae_restrict_of_ae_restrict_compl M' h1 h2
    let β : Eucl (m+1) → ℝ := fun x => if (∃ k : ℤ, b' x = k) then b' x else 0
    have hβ : β = fun x => if (∃ k : ℤ, b' x = k) then b' x else 0 := rfl
    have hset : MeasurableSet {x | ∃ k : ℤ, b' x = k} := by
      have : {x | ∃ k : ℤ, b' x = k} = b' ⁻¹' (range (Int.cast : ℤ → ℝ)) := by
        ext x
        simp only [mem_ofPred_eq, mem_preimage, mem_range, eq_comm]
      rw [this]
      exact hb'm.measurable (countable_range _).measurableSet
    have hβm : Measurable β := Measurable.ite hset hb'm.measurable measurable_const
    have hββ : b =ᵐ[volume] β := by
      filter_upwards [hbb', hbz] with x h1 h2
      have h3 : ∃ k : ℤ, b' x = k := h1 ▸ h2
      simp only [β, ite_eq_left h3, h1]
    refine ⟨β, hβm, fun x => ?_, fun C hC hCU => (hbi C hC hCU).congr_fun_ae (ae_restrict_of_ae hββ),
      fun ω => ?_⟩
    · by_cases h : ∃ k : ℤ, b' x = k
      · simp only [β, ite_eq_left h]
        exact h
      · simp only [β, ite_eq_right h]
        exact ⟨0, by simp only [Int.cast_zero]⟩
    · rw [hbact ω]
      exact integral_congr_ae (hββ.mono fun x hx => by simp only [hx])
  choose β hβm hβz hβi hβT using hdens
  /- Step 4: `(β j)` is Cauchy in L¹(C) for every compact `C ⊆ U`. -/
  have hCauchy : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ∫⁻ x in C, ‖β j x - β k x‖ₑ ≤ ENNReal.ofReal η := by
    intro C hC hCU η hη
    obtain ⟨r, hr0, hrU⟩ := hC.exists_cthickening_subset_open hU hCU
    let V : Set (Eucl (m+1)) := thickening r C
    have hVo : IsOpen V := isOpen_thickening
    have hVU : V ⊆ U := (thickening_subset_cthickening _ _).trans hrU
    have hδ0 : 0 < r / 4 := div_pos hr0 four_pos
    have h2δ : cthickening (2 * (r / 4)) C ⊆ V :=
      cthickening_subset_thickening' hr0 (by linarith only [hr0]) C
    have hδV : cthickening (r / 4) C ⊆ V :=
      (cthickening_mono (by linarith only [hr0]) C).trans h2δ
    have hS := hbd V ⟨hVo, hC.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening _ _), (closure_thickening_subset_cthickening _ _).trans hrU⟩
    let S := ⨆ j, ((Tj j).massOn V + (Tj j).boundary.massOn V)
    have hSfin : S ≠ ⊤ := hS.ne
    have hmT : ∀ j, (Tj j).massOn V ≤ S := fun j =>
      le_trans le_self_add (le_iSup (fun j => (Tj j).massOn V + (Tj j).boundary.massOn V) j)
    have hmB : ∀ j, (Tj j).boundary.massOn V ≤ S := fun j =>
      le_trans le_add_self (le_iSup (fun j => (Tj j).massOn V + (Tj j).boundary.massOn V) j)
    let B : ℝ := κ * S.toReal
    have hB0 : 0 ≤ B := mul_nonneg hκ0.le ENNReal.toReal_nonneg
    -- the boundary hypothesis of the translation estimate
    have hH : ∀ j (ψ : Eucl (m+1) → ℝ) (z : Eucl (m+1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ V → (∀ x, |ψ x| ≤ 1) →
        |∫ x, β j x * fderiv ℝ ψ x z| ≤ ‖z‖ * B := by
      intro j ψ z hψ hψc hψV hψ1
      rcases eq_or_ne z 0 with rfl | hz
      · simp only [map_zero, mul_zero, integral_zero, abs_zero, norm_zero, zero_mul, le_refl]
      obtain ⟨ω, hω⟩ := hform U m ψ (dx.curryLeft z) hψ hψc (hψV.trans hVU)
      have hωfun : (ω : DifferentialForm (Eucl (m+1)) m) = fun y => ψ y • dx.curryLeft z := funext hω
      have hval : (Tj j).boundary ω = ∫ x, β j x * fderiv ℝ ψ x z := by
        rw [GeometricCurrentOn.boundary_apply, hβT]
        congr 1
        funext x
        congr 1
        change exteriorDerivative (ω : DifferentialForm (Eucl (m+1)) m) x e = _
        rw [hωfun]
        exact hP7 ψ hψ z x
      have h1 := hmassb U m (Tj j).boundary V ω (κ * ‖z‖) (mul_pos hκ0 (norm_pos_iff.2 hz))
        (by rw [hωfun]; exact (tsupport_smul_subset_left _ _).trans hψV)
        (fun x => by
          rw [hω x, hP6]
          exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hψ1 x)).trans (hκN z))
        (ne_top_of_le_ne_top hSfin (hmB j))
      rw [hval] at h1
      calc |∫ x, β j x * fderiv ℝ ψ x z| ≤ κ * ‖z‖ * ((Tj j).boundary.massOn V).toReal := h1
        _ ≤ κ * ‖z‖ * S.toReal := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hSfin (hmB j))
            (mul_nonneg hκ0.le (norm_nonneg z))
        _ = ‖z‖ * B := by rw [mul_comm κ, mul_assoc]
    have hTEj : ∀ j (z : Eucl (m+1)), ‖z‖ ≤ r / 4 →
        ∫⁻ x in C, ‖β j x - β j (x - z)‖ₑ ≤ ENNReal.ofReal (‖z‖ * B) := fun j z hz =>
      hTE (β j) C V (r / 4) B (hβm j) hC hVo hδ0 h2δ
        (fun K' hK' hK'V => hβi j K' hK' (hK'V.trans hVU)) (hH j) z hz
    -- mollifications of the T_j are tested by `φ(x - ·) dx`
    have hmoll : ∀ φ : Eucl (m+1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ closedBall 0 (r / 4) →
        (∃ A : ℝ, ∀ j, ∀ x ∈ C, |∫ y, β j y * φ (x - y)| ≤ A) ∧
        ∀ x ∈ C, ∃ L : ℝ, Tendsto (fun j => ∫ y, β j y * φ (x - y)) atTop (𝓝 L) := by
      intro φ hφ hφc hφts
      obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
      have hax : ∀ x ∈ C, ∃ ω : TestFormOn U (m+1),
          (∀ y, (ω : DifferentialForm (Eucl (m+1)) (m+1)) y = φ (x - y) • dx) ∧
          tsupport (ω : DifferentialForm (Eucl (m+1)) (m+1)) ⊆ V ∧
          ∀ j, Tj j ω = ∫ y, β j y * φ (x - y) := by
        intro x hx
        have hts : tsupport (fun y => φ (x - y)) ⊆ V := by
          have e1 : (fun y => φ (x - y)) = φ ∘ (Homeomorph.subLeft x) := rfl
          rw [e1, tsupport_comp_eq_preimage]
          intro y hy
          apply hδV
          have h1 := hφts hy
          rw [mem_closedBall, dist_zero_right] at h1
          apply mem_cthickening_of_dist_le y x (r / 4) C hx
          rw [dist_comm, dist_eq_norm]
          simpa only [Homeomorph.subLeft_apply] using h1
        obtain ⟨ω, hω⟩ := hform U (m+1) (fun y => φ (x - y)) dx
          (hφ.comp (contDiff_const.sub contDiff_id))
          (hφc.comp_homeomorph (Homeomorph.subLeft x)) (hts.trans hVU)
        refine ⟨ω, hω, ?_, fun j => ?_⟩
        · rw [show (ω : DifferentialForm (Eucl (m+1)) (m+1)) = fun y => φ (x - y) • dx from funext hω]
          exact (tsupport_smul_subset_left _ _).trans hts
        · rw [hβT]
          congr 1
          funext y
          rw [hω y, ContinuousAlternatingMap.smul_apply, hdxe, smul_eq_mul, mul_one]
      have hCm : 0 < (|Cφ| + 1) * (covectorEuclideanNorm dx + 1) :=
        mul_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos)
          (add_pos_of_nonneg_of_pos (covectorEuclideanNorm_nonneg _) one_pos)
      refine ⟨⟨(|Cφ| + 1) * (covectorEuclideanNorm dx + 1) * S.toReal, fun j x hx => ?_⟩,
        fun x hx => ?_⟩
      · obtain ⟨ω, hω, hωV, hωT⟩ := hax x hx
        rw [← hωT j]
        refine (hmassb U (m+1) (Tj j) V ω _ hCm hωV (fun y => ?_)
          (ne_top_of_le_ne_top hSfin (hmT j))).trans
          (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hSfin (hmT j)) hCm.le)
        rw [hω y, hP6]
        exact mul_le_mul ((Real.norm_eq_abs _).symm.le.trans ((hCφ _).trans ((le_abs_self Cφ).trans
          (le_add_of_nonneg_right zero_le_one)))) (le_add_of_nonneg_right zero_le_one)
          (covectorEuclideanNorm_nonneg _) (add_nonneg (abs_nonneg _) zero_le_one)
      · obtain ⟨ω, hω, hωV, hωT⟩ := hax x hx
        exact ⟨T ω, (hconv ω).congr (fun j => hωT j)⟩
    exact hR4 β C V (r / 4) B hβm hC hVo hδ0 hδV hB0
      (fun j K' hK' hK'V => hβi j K' hK' (hK'V.trans hVU)) hTEj hmoll η hη
  /- Step 4: a subsequence converging a.e. on `U` to an integer-valued Borel limit. -/
  have hN : ∀ l : ℕ, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ x in K l, ‖β j x - β k x‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ l := by
    intro l
    obtain ⟨N, hN⟩ := hCauchy (K l) (hKc l) (hKU l) ((1/2 : ℝ) ^ l) (pow_pos one_half_pos l)
    exact ⟨N, fun j hj k hk => (hN j hj k hk).trans (hhalf l).le⟩
  choose N hN using hN
  obtain ⟨φ, hφmono, hφN⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ l, N l ≤ φ l := by
    refine ⟨fun l => l + ∑ i ∈ Finset.range (l+1), N i, strictMono_nat_of_lt_succ (fun l => ?_),
      fun l => ?_⟩
    · show l + ∑ i ∈ Finset.range (l+1), N i < (l + 1) + ∑ i ∈ Finset.range (l+1+1), N i
      simp only [Finset.sum_range_succ]
      omega
    · have : N l ≤ ∑ i ∈ Finset.range (l+1), N i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ l)
      show N l ≤ l + ∑ i ∈ Finset.range (l+1), N i
      omega
  have hpair : ∀ l k k', l ≤ k → k ≤ k' →
      ∫⁻ x in K l, ‖β (φ k) x - β (φ k') x‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro l k k' hlk hkk'
    calc ∫⁻ x in K l, ‖β (φ k) x - β (φ k') x‖ₑ ≤ ∫⁻ x in K k, ‖β (φ k) x - β (φ k') x‖ₑ :=
          lintegral_mono_set (hKmono l k hlk)
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ k := hN k (φ k) (hφN k) (φ k') ((hφN k).trans (hφmono.monotone hkk'))
  have hev : ∀ l, ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ K l →
      ∀ᶠ k in atTop, β (φ (k+1)) x = β (φ k) x := by
    intro l
    let A : ℕ → Set (Eucl (m+1)) := fun k => K l ∩ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x}
     
    have hA : A = fun k => K l ∩ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} := rfl
    have hAle : ∀ k, volume (A k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
      intro k
      have hmeas : MeasurableSet {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} :=
        (measurableSet_eq_fun (hβm _) (hβm _)).compl
      calc volume (A k)
          = ∫⁻ x in K l, {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x}.indicator 1 x := by
            rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas, inter_comm]
        _ ≤ ∫⁻ x in K l, ‖β (φ (k + l)) x - β (φ (k + l + 1)) x‖ₑ := by
            refine lintegral_mono (fun x => ?_)
            by_cases hx : β (φ (k + l + 1)) x ≠ β (φ (k + l)) x
            · rw [indicator_of_mem (show x ∈ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} from hx),
                Pi.one_apply]
              exact hint1 _ _ (hβz _ x) (hβz _ x) (Ne.symm hx)
            · rw [indicator_of_notMem (show x ∉ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} from hx)]
              exact zero_le
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + l) := hpair l (k + l) (k + l + 1) (by omega) (by omega)
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ k := pow_le_pow_of_le_one (zero_le) (ENNReal.inv_le_one.2 one_le_two) (by omega)
    have hsum : ∑' k, volume (A k) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAle)
      rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    filter_upwards [ae_eventually_notMem hsum] with x hx hxK
    rw [eventually_atTop] at hx ⊢
    obtain ⟨k0, hk0⟩ := hx
    refine ⟨k0 + l, fun k hk => ?_⟩
    have h1 := hk0 (k - l) (by omega)
    have e1 : k - l + l = k := by omega
    simp only [A, mem_inter_iff, mem_ofPred_eq, not_and, not_not, e1] at h1
    exact h1 hxK
  have hconvx : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ U →
      ∃ c, Tendsto (fun k => β (φ k) x) atTop (𝓝 c) ∧ ∃ z : ℤ, c = z := by
    filter_upwards [ae_all_iff.2 hev] with x hx hxU
    obtain ⟨l, hl⟩ := hKcov {x} isCompact_singleton (singleton_subset_iff.2 hxU)
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hx l (hl rfl))
    have hconst : ∀ k ≥ k0, β (φ k) x = β (φ k0) x := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [hk0 k hk, ih]
    exact ⟨β (φ k0) x, tendsto_atTop_of_eventually_const hconst, hβz _ x⟩
  let βl : Eucl (m+1) → ℝ := fun x => limUnder atTop (fun k => β (φ k) x)
  have hβl : βl = fun x => limUnder atTop (fun k => β (φ k) x) := rfl
  have hβlm : Measurable βl :=
    (StronglyMeasurable.limUnder (fun k => (hβm (φ k)).stronglyMeasurable)).measurable
  let βh : Eucl (m+1) → ℝ := fun x => if (∃ k : ℤ, βl x = k) then βl x else 0
  have hβh : βh = fun x => if (∃ k : ℤ, βl x = k) then βl x else 0 := rfl
  have hβhm : Measurable βh := by
    have hset : MeasurableSet {x | ∃ k : ℤ, βl x = k} := by
      have : {x | ∃ k : ℤ, βl x = k} = βl ⁻¹' (range (Int.cast : ℤ → ℝ)) := by
        ext x
        simp only [eq_comm, mem_ofPred_eq, mem_preimage, mem_range]
      rw [this]
      exact hβlm (countable_range _).measurableSet
    exact Measurable.ite hset hβlm measurable_const
  have hβhz : ∀ x, ∃ k : ℤ, βh x = k := by
    intro x
    by_cases h : ∃ k : ℤ, βl x = k
    · simp only [βh, ite_eq_left h]
      exact h
    · simp only [βh, ite_eq_right h]
      exact ⟨0, by simp only [Int.cast_zero]⟩
  have hlim : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ U →
      Tendsto (fun k => β (φ k) x) atTop (𝓝 (βh x)) := by
    filter_upwards [hconvx] with x hx hxU
    obtain ⟨c, hc, z, hz⟩ := hx hxU
    have h1 : βl x = c := hc.limUnder_eq
    have h2 : βh x = c := by
      simp only [βh, h1]
      rw [ite_eq_left ⟨z, hz⟩]
    rw [h2]
    exact hc
  /- Fatou: L¹ convergence on the exhaustion. -/
  have hfatou : ∀ l k, l ≤ k → ∫⁻ x in K l, ‖β (φ k) x - βh x‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro l k hlk
    have hae : ∀ᵐ x ∂(volume.restrict (K l)),
        Tendsto (fun k' => ‖β (φ k) x - β (φ k') x‖ₑ) atTop (𝓝 ‖β (φ k) x - βh x‖ₑ) := by
      filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem (hKc l).measurableSet] with x hx hxK
      exact (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub (hx (hKU l hxK)))
    calc ∫⁻ x in K l, ‖β (φ k) x - βh x‖ₑ
        = ∫⁻ x in K l, liminf (fun k' => ‖β (φ k) x - β (φ k') x‖ₑ) atTop :=
          lintegral_congr_ae (hae.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun k' => ∫⁻ x in K l, ‖β (φ k) x - β (φ k') x‖ₑ) atTop :=
          lintegral_liminf_le' (fun k' => (((hβm _).sub (hβm _)).enorm).aemeasurable)
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ k :=
          liminf_le_of_frequently_le' ((eventually_atTop.2
            ⟨k, fun k' hk' => hpair l k k' hlk hk'⟩).frequently)
  have hβhi : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → IntegrableOn βh C := by
    intro C hC hCU
    obtain ⟨l, hl⟩ := hKcov C hC hCU
    refine IntegrableOn.mono_set ?_ hl
    have h1 := hβi (φ l) (K l) (hKc l) (hKU l)
    refine ⟨hβhm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ x in K l, ‖βh x‖ₑ ≤ ∫⁻ x in K l, (‖β (φ l) x‖ₑ + ‖β (φ l) x - βh x‖ₑ) :=
          lintegral_mono (fun x => by
            calc ‖βh x‖ₑ = ‖β (φ l) x - (β (φ l) x - βh x)‖ₑ := by congr 1; ring
              _ ≤ ‖β (φ l) x‖ₑ + ‖β (φ l) x - βh x‖ₑ := enorm_sub_le)
      _ = (∫⁻ x in K l, ‖β (φ l) x‖ₑ) + ∫⁻ x in K l, ‖β (φ l) x - βh x‖ₑ :=
          lintegral_add_left ((hβm _).enorm) _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1.hasFiniteIntegral,
          (hfatou l l le_rfl).trans_lt (ENNReal.pow_lt_top (ENNReal.inv_lt_top.2 two_pos))⟩
  have hL1 : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U →
      Tendsto (fun k => ∫⁻ x in C, ‖β (φ k) x - βh x‖ₑ) atTop (𝓝 0) := by
    intro C hC hCU
    obtain ⟨l, hl⟩ := hKcov C hC hCU
    have hgeom : Tendsto (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeom
      (Eventually.of_forall fun k => zero_le) ?_
    filter_upwards [eventually_ge_atTop l] with k hk
    exact (lintegral_mono_set hl).trans (hfatou l k hk)
  /- Step 5: `T = [[U]] ⌞ βh`. -/
  have hTβ : ∀ ω : TestFormOn U (m+1),
      T ω = ∫ x, βh x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
    intro ω
    let a : Eucl (m+1) → ℝ := fun x => (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e
    have ha : a = fun x => (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := rfl
    have hωc : Continuous (ω : DifferentialForm (Eucl (m+1)) (m+1)) := ω.property.1.1.continuous
    have hac : Continuous a := (continuous_eval_const e).comp hωc
    let KΩ := tsupport (ω : DifferentialForm (Eucl (m+1)) (m+1))
    have hKΩ : KΩ = tsupport (ω : DifferentialForm (Eucl (m+1)) (m+1)) := rfl
    have hKΩc : IsCompact KΩ := ω.property.1.2
    have hKΩU : KΩ ⊆ U := ω.property.2
    have ha0 : ∀ x, x ∉ KΩ → a x = 0 := by
      intro x hx
      simp only [a, image_eq_zero_of_notMem_tsupport hx]
      rfl
    obtain ⟨Ca, hCa⟩ : ∃ Ca : ℝ, ∀ x, |a x| ≤ Ca := by
      obtain ⟨Ca, hCa⟩ := hKΩc.exists_bound_of_continuousOn hac.continuousOn
      refine ⟨max Ca 0, fun x => ?_⟩
      by_cases hx : x ∈ KΩ
      · exact ((Real.norm_eq_abs (a x)).symm.le.trans (hCa x hx)).trans (le_max_left _ _)
      · rw [ha0 x hx, abs_zero]
        exact le_max_right _ _
    have hsupp : ∀ g : Eucl (m+1) → ℝ, Function.support (fun x => g x * a x) ⊆ KΩ := by
      intro g x hx
      by_contra h
      exact hx (show g x * a x = 0 by rw [ha0 x h, mul_zero])
    have hint : ∀ g : Eucl (m+1) → ℝ, IntegrableOn g KΩ → Integrable (fun x => g x * a x) := by
      intro g hg
      rw [← integrableOn_iff_integrable_of_support_subset (hsupp g)]
      exact hg.mul_continuousOn hac.continuousOn hKΩc
    have h1 : Tendsto (fun k => Tj (φ k) ω) atTop (𝓝 (T ω)) :=
      (hconv ω).comp hφmono.tendsto_atTop
    have h2 : Tendsto (fun k => ∫ x, β (φ k) x * a x) atTop (𝓝 (∫ x, βh x * a x)) := by
      have hbound : ∀ k, ‖(∫ x, β (φ k) x * a x) - ∫ x, βh x * a x‖ₑ ≤
          ENNReal.ofReal Ca * ∫⁻ x in KΩ, ‖β (φ k) x - βh x‖ₑ := by
        intro k
        rw [← integral_sub (hint _ (hβi (φ k) KΩ hKΩc hKΩU)) (hint _ (hβhi KΩ hKΩc hKΩU))]
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        rw [← lintegral_indicator hKΩc.measurableSet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono (fun x => ?_)
        by_cases hx : x ∈ KΩ
        · rw [indicator_of_mem hx, ← sub_mul, enorm_mul, mul_comm (ENNReal.ofReal Ca)]
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hCa x)
        · rw [indicator_of_notMem hx, ha0 x hx]
          simp
      have h3 : Tendsto (fun k => ENNReal.ofReal Ca * ∫⁻ x in KΩ, ‖β (φ k) x - βh x‖ₑ) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Ca) (hL1 KΩ hKΩc hKΩU)
          (Or.inr ENNReal.ofReal_ne_top)
        rwa [mul_zero] at this
      have h4 : Tendsto (fun k => ‖(∫ x, β (φ k) x * a x) - ∫ x, βh x * a x‖ₑ) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun k => zero_le) hbound
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h4
      simpa [Function.comp_def, toReal_enorm] using h5
    have h1' : Tendsto (fun k => ∫ x, β (φ k) x * a x) atTop (𝓝 (T ω)) :=
      h1.congr (fun k => hβT (φ k) ω)
    exact tendsto_nhds_unique h1' h2
  /- Step 6: the tangent spaces of `({βh ≠ 0}, |βh|)`. -/
  let Mh : Set (Eucl (m+1)) := {x | x ∈ U ∧ βh x ≠ 0}
  have hMh : Mh = {x | x ∈ U ∧ βh x ≠ 0} := rfl
  have hMhm : MeasurableSet Mh := hU.measurableSet.inter (hβhm (measurableSet_singleton 0).compl)
  have htan : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ U → βh x ≠ 0 →
      HasWeightedApproximateTangentSpaceAt (m+1) Mh (fun x => |βh x|) x ⊤ := by
    have hall := ae_all_iff.2 (fun l => hLeb βh (K l) (hKc l) (hβhi _ (hKc l) (hKU l)))
    filter_upwards [hall] with x hx hxU hx0
    obtain ⟨ρ, hρ0, hρU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hxU)
    obtain ⟨l, hl⟩ := hKcov _ (isCompact_closedBall x ρ) hρU
    refine (Submission.iwl_weighted_tangent_locality (m+1) (m+1) Mh univ (fun y => |βh y|)
      (fun _ => |βh x|) x ?_ ?_ rfl ?_ ?_ ⊤).2 (hconstTan _ x)
    · rw [hvol]
      exact hMhm.nullMeasurableSet
    · rw [hvol]
      exact MeasurableSet.univ.nullMeasurableSet
    · refine ⟨ρ, hρ0, ?_, ?_⟩
      · rw [hvol]
        exact IntegrableOn.mono_set (Integrable.abs (hβhi _ (isCompact_closedBall x ρ) hρU))
          inter_subset_right
      · rw [hvol]
        exact (integrableOn_const (measure_closedBall_lt_top.ne)).mono_set inter_subset_right
    · intro R hR
      rw [hvol]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hx l ρ hρ0 hl R hR)
        (Eventually.of_forall fun r => zero_le) ?_
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_le_nhds (div_pos hρ0 hR))] with r hr hrρ
      have hRrρ : R * r ≤ ρ := (le_div_iff₀' hR).1 hrρ
      refine mul_le_mul_right (setLIntegral_mono ((hβhm.sub measurable_const).enorm)
        (fun z hz => ?_)) _
      have hzU : z ∈ U := hρU (closedBall_subset_closedBall hRrρ hz)
      have hind : Mh.indicator (fun x => |βh x|) z = |βh z| := by
        by_cases h0 : βh z = 0
        · rw [indicator_of_notMem (fun h => h.2 h0), h0, abs_zero]
        · rw [indicator_of_mem (show z ∈ Mh from ⟨hzU, h0⟩)]
      rw [hind, indicator_of_mem (mem_univ z)]
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub _ _)
  /- Step 6: `T = τ(Mh, |βh|, sign(βh) e₁ ∧ ⋯ ∧ eₙ)` is integer multiplicity. -/
  let ξ : Eucl (m+1) → NVector (Eucl (m+1)) (m+1) :=
    fun x => if 0 ≤ βh x then simpleNVector e else -simpleNVector e
  have hξ : ξ = fun x => if 0 ≤ βh x then simpleNVector e else -simpleNVector e := rfl
  have hval : ∀ (ω : TestFormOn U (m+1)) x,
      |βh x| * ξ x ((ω : DifferentialForm (Eucl (m+1)) (m+1)) x) =
        βh x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
    intro ω x
    by_cases h : 0 ≤ βh x
    · simp only [ξ, ite_eq_left h, simpleNVector_apply, abs_of_nonneg h]
    · simp only [ξ, ite_eq_right h, neg_apply, simpleNVector_apply,
        abs_of_neg (lt_of_not_ge h)]
      ring
  refine ⟨Mh, fun x => |βh x|, ξ, ⟨fun x hx => hx.1, (by rw [hvol]; exact hMhm.nullMeasurableSet), ?_,
    fun x hx => abs_pos.2 hx.2, fun C hC hCU => ?_, ?_, ?_⟩, fun x hx => ?_,
    fun ω => ?_⟩
  · refine ⟨∅, measure_empty, fun _ => id, fun _ => ⟨1, LipschitzWith.id⟩, fun x _ => Or.inr ?_⟩
    exact mem_iUnion.2 ⟨0, mem_range_self x⟩
  · rw [hvol]
    exact IntegrableOn.mono_set (Integrable.abs (hβhi C hC hCU)) inter_subset_right
  · exact (stronglyMeasurable_const.piecewise (measurableSet_le measurable_const hβhm)
      stronglyMeasurable_const).aestronglyMeasurable
  · rw [hvol]
    filter_upwards [ae_restrict_of_ae htan, ae_restrict_mem hMhm] with x hx hxM
    refine ⟨e, hbe ▸ (EuclideanSpace.basisFun (Fin (m+1)) ℝ).orthonormal, ?_, ?_⟩
    · have hspan : Submodule.span ℝ (range e) = ⊤ := by
        rw [← hbe, ← OrthonormalBasis.coe_toBasis]
        exact (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis.span_eq
      rw [hspan]
      exact hx hxM.1 hxM.2
    · by_cases h : 0 ≤ βh x
      · exact Or.inl (ite_eq_left h)
      · exact Or.inr (ite_eq_right h)
  · obtain ⟨k, hk⟩ := hβhz x
    exact ⟨k.natAbs, by simp only [hk, Nat.cast_natAbs, Int.cast_abs]⟩
  · rw [hTβ ω, tauAction, hvol]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Mh) (fun x hx => ?_)]
    · exact setIntegral_congr_fun hMhm (fun x _ => (hval ω x).symm)
    · by_cases hxU : x ∈ U
      · have h0 : βh x = 0 := by
          by_contra h
          exact hx ⟨hxU, h⟩
        simp [h0]
      · have h0 : (ω : DifferentialForm (Eucl (m+1)) (m+1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hxU (ω.property.2 h))
        simp [h0]

end GMT.Ch06
