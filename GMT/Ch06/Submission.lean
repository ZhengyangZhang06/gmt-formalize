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

/-- **Conical density lemma for purely unrectifiable sets** (Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, 15.13–15.15; Hovila–Järvenpää–Järvenpää–Ledrappier,
arXiv:1104.3453, Lemma 2.2).  Let `k = m + 1`, `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩) ∈ ℝᵏ` and
`X_v(a,r,s) = {x : |x - a| < r, |L_v(x - a)| < s |x - a|}`.  If `E ⊆ ℝ^N` is purely
`k`-unrectifiable, the set of `a ∈ E` at which, for every `η > 0`, some aperture `s ∈ (0,1)`
gives `Hᵏ(E ∩ X_v(a,r,s)) ≤ η (r s)ᵏ` for all `r ∈ (0,δ)` is `Hᵏ`-null.  The three steps of the
proof (the conical density estimate, the uniform density bound forcing measure zero, and the
reduction to rational apertures) are local `have`s of this single declaration. -/
theorem Submission.rectifiability_bf_cone_density : ∀ (N m : ℕ) (E : Set (Eucl N)) (v : Fin (m + 1) → Eucl N) (δ : ℝ), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → 0 < δ → (μHE[m + 1] : Measure (Eucl N)) {a | a ∈ E ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))} = 0 := by
  -- Step 1(a) (Mattila 15.13): a set on which `L_v` is bi-Lipschitz lies in a Lipschitz image of `ℝᵏ`, hence is countably `k`-rectifiable, hence null in the purely unrectifiable `E`.
  have graph_null : ∀ (N m : ℕ) (E F : Set (Eucl N)) (v : Fin (m + 1) → Eucl N) (c : ℝ), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → F ⊆ E → 0 < c → (∀ a ∈ F, ∀ b ∈ F, c * ‖b - a‖ ≤ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖) → (μHE[m + 1] : Measure (Eucl N)) F = 0 := by
    classical
    intro N m E F v c hE hFE hc hbi
    let L : Eucl N → Eucl (m + 1) := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      ext i
      simp only [L, PiLp.sub_apply]
      rw [← inner_sub_right]
    have hinj : InjOn L F := by
      intro a ha b hb hab
      have h1 := hbi a ha b hb
      have h2 : L (b - a) = 0 := by rw [← hLsub, hab, sub_self]
      change c * ‖b - a‖ ≤ ‖L (b - a)‖ at h1
      rw [h2, norm_zero] at h1
      have h3 : ‖b - a‖ ≤ 0 := by nlinarith [norm_nonneg (b - a)]
      exact (sub_eq_zero.1 (norm_le_zero_iff.1 h3)).symm
    let g : Eucl (m + 1) → Eucl N := Function.invFunOn L F
    have hg : ∀ a ∈ F, g (L a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
    have hglip : LipschitzOnWith (Real.toNNReal c⁻¹) g (L '' F) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hg a ha, hg b hb, dist_eq_norm, dist_eq_norm, hLsub,
        Real.coe_toNNReal _ (inv_nonneg.2 hc.le)]
      have h1 : c * ‖a - b‖ ≤ ‖L (a - b)‖ := hbi b hb a ha
      rw [inv_mul_eq_div, le_div_iff₀ hc]
      linarith
    obtain ⟨G, hGlip, hGeq⟩ := hglip.extend_finite_dimension
    have hFrange : F ⊆ range G := fun a ha =>
      ⟨L a, (hGeq (mem_image_of_mem L ha)).symm.trans (hg a ha)⟩
    have hrect : CountablyRectifiable (m + 1) F :=
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hGlip).mono hFrange
    exact hE F hFE hrect
  -- Step 1(b), geometry: with `h = h(a)` and a partner `b` with `3h/4 < |b - a| ≤ h` in the `s/4`-cone, the cylinder `{|L_v(x - a)| < sh/4}` meets `F` inside `X_v(a,2h,s) ∪ X_v(b,2h,s)`.
  have two_cone_cover : ∀ (N m : ℕ) (v : Fin (m + 1) → Eucl N) (F : Set (Eucl N)) (a b : Eucl N) (s h : ℝ), 0 < s → (∀ c ∈ F, ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ < s / 4 * ‖c - a‖ → ‖c - a‖ ≤ h) → ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖ < s / 4 * ‖b - a‖ → 3 * h / 4 < ‖b - a‖ → ‖b - a‖ ≤ h → F ∩ {x | ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * h / 4} ⊆ {x | dist x a < 2 * h ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} ∪ {x | dist x b < 2 * h ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - b)) : Eucl (m + 1))‖ < s * ‖x - b‖} := by
    intro N m v F a b s h hs hmax hb1 hb2 hb3
    have hh : 0 < h := by linarith [norm_nonneg (b - a)]
    have hlin : ∀ c : Eucl N,
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - b)) : Eucl (m + 1)) =
          WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) +
            WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) := by
      intro c
      ext i
      simp only [PiLp.add_apply]
      rw [← inner_add_right]
      congr 1
      abel
    have hneg : ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) : Eucl (m + 1))‖ =
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖ := by
      rw [← norm_neg]
      congr 1
      ext i
      simp only [PiLp.neg_apply]
      rw [← inner_neg_right, neg_sub]
    rintro c ⟨hcF, hc⟩
    change ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ <
      s * h / 4 at hc
    have hca : ‖c - a‖ ≤ h := by
      by_contra hlt
      push Not at hlt
      have hin : ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ <
          s / 4 * ‖c - a‖ := by
        calc _ < s * h / 4 := hc
          _ < s / 4 * ‖c - a‖ := by nlinarith
      linarith [hmax c hcF hin]
    by_cases hfar : h / 4 ≤ ‖c - a‖
    · left
      refine ⟨by rw [dist_eq_norm]; linarith, ?_⟩
      calc _ < s * h / 4 := hc
        _ ≤ s * ‖c - a‖ := by nlinarith
    · right
      push Not at hfar
      have htri1 : ‖b - a‖ ≤ ‖c - b‖ + ‖c - a‖ := by
        calc ‖b - a‖ ≤ ‖b - c‖ + ‖c - a‖ := norm_sub_le_norm_sub_add_norm_sub b c a
          _ = ‖c - b‖ + ‖c - a‖ := by rw [norm_sub_rev b c]
      have htri2 : ‖c - b‖ ≤ ‖c - a‖ + ‖b - a‖ := by
        calc ‖c - b‖ ≤ ‖c - a‖ + ‖a - b‖ := norm_sub_le_norm_sub_add_norm_sub c a b
          _ = ‖c - a‖ + ‖b - a‖ := by rw [norm_sub_rev a b]
      have hcb1 : h / 2 < ‖c - b‖ := by linarith
      have hcb2 : ‖c - b‖ < 2 * h := by linarith
      refine ⟨by rw [dist_eq_norm]; exact hcb2, ?_⟩
      rw [hlin c]
      calc _ ≤ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ +
            ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) : Eucl (m + 1))‖ :=
            norm_add_le _ _
        _ < s * h / 4 + s / 4 * ‖b - a‖ := by rw [hneg]; linarith
        _ ≤ s * h / 2 := by nlinarith
        _ < s * ‖c - b‖ := by nlinarith
  -- Step 1(c): Vitali covering (factor `τ = 2`, so `5r` enlargements) of the projected balls in `ℝᵏ`, countability, and the volume packing bound `Σ ρᵏ ≤ (M + R)ᵏ`.
  have vitali_packing : ∀ (N m : ℕ) (A : Set (Eucl N)) (y : Eucl N → Eucl (m + 1)) (ρ : Eucl N → ℝ) (y₀ : Eucl (m + 1)) (R M : ℝ), (∀ a ∈ A, 0 < ρ a ∧ ρ a ≤ R) → (∀ a ∈ A, dist (y a) y₀ ≤ M) → ∃ I : Set (Eucl N), I ⊆ A ∧ I.Countable ∧ I.PairwiseDisjoint (fun b => ball (y b) (ρ b)) ∧ (∀ a ∈ A, ∃ b ∈ I, ball (y a) (ρ a) ⊆ ball (y b) (5 * ρ b)) ∧ ∑' b : I, ENNReal.ofReal (ρ b ^ (m + 1)) ≤ ENNReal.ofReal ((M + R) ^ (m + 1)) := by
    intro N m A y ρ y₀ R M hρ hy
    obtain ⟨u, huA, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a => ball (y a) (ρ a)) A ρ 2 one_lt_two (fun a ha => (hρ a ha).1.le) R
      (fun a ha => (hρ a ha).2) (fun a ha => nonempty_ball.2 (hρ a ha).1)
    have hucount : u.Countable := hudisj.countable_of_isOpen (fun a _ => isOpen_ball)
      (fun a ha => nonempty_ball.2 (hρ a (huA ha)).1)
    refine ⟨u, huA, hucount, hudisj, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hbu, ⟨z, hza, hzb⟩, hab⟩ := hucov a ha
      refine ⟨b, hbu, fun w hw => ?_⟩
      rw [mem_ball] at hw hza hzb ⊢
      calc dist w (y b) ≤ dist w (y a) + dist (y a) z + dist z (y b) := dist_triangle4 _ _ _ _
        _ < ρ a + ρ a + ρ b := by rw [dist_comm (y a) z]; linarith
        _ ≤ 5 * ρ b := by linarith
    · rcases u.eq_empty_or_nonempty with hu | ⟨b₀, hb₀⟩
      · subst hu
        simp
      have hR : 0 < R := (hρ b₀ (huA hb₀)).1.trans_le (hρ b₀ (huA hb₀)).2
      have hM : 0 ≤ M := dist_nonneg.trans (hy b₀ (huA hb₀))
      set μ : Measure (Eucl (m + 1)) := volume with hμ
      have hω0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
      have hωtop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
      have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
      have hsub : (⋃ b ∈ u, ball (y b) (ρ b)) ⊆ ball y₀ (M + R) := by
        intro w hw
        obtain ⟨b, hbu, hwb⟩ := mem_iUnion₂.1 hw
        rw [mem_ball] at hwb ⊢
        calc dist w y₀ ≤ dist w (y b) + dist (y b) y₀ := dist_triangle _ _ _
          _ < ρ b + M := by linarith [hy b (huA hbu)]
          _ ≤ M + R := by linarith [(hρ b (huA hbu)).2]
      have key : (∑' b : u, ENNReal.ofReal (ρ b ^ (m + 1))) * μ (ball 0 1) ≤
          ENNReal.ofReal ((M + R) ^ (m + 1)) * μ (ball 0 1) := by
        rw [← ENNReal.tsum_mul_right]
        calc ∑' b : u, ENNReal.ofReal (ρ b ^ (m + 1)) * μ (ball 0 1)
            = ∑' b : u, μ (ball (y b) (ρ b)) := by
              congr 1
              funext b
              rw [Measure.addHaar_ball_of_pos μ _ (hρ b (huA b.2)).1, hfin]
          _ = μ (⋃ b ∈ u, ball (y b) (ρ b)) :=
              (measure_biUnion hucount hudisj (fun b _ => measurableSet_ball)).symm
          _ ≤ μ (ball y₀ (M + R)) := measure_mono hsub
          _ = ENNReal.ofReal ((M + R) ^ (m + 1)) * μ (ball 0 1) := by
              rw [Measure.addHaar_ball μ _ (by linarith), hfin]
      exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key
  -- Step 1 (Mattila 15.14): the conical density estimate `Hᵏ(B ∩ B(x₀,δ′/6)) ≤ C₁ λ δ′ᵏ`, `C₁ = 2(20/3)ᵏ(‖L_v‖ + 1)ᵏ`.
  have conical_density_estimate : ∀ (N m : ℕ) (E : Set (Eucl N)) (v : Fin (m + 1) → Eucl N), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (B : Set (Eucl N)) (s δ' l : ℝ), B ⊆ E → 0 < s → s < 1 → 0 < δ' → 0 ≤ l → (∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ δ' → (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (l * (r * s) ^ (m + 1))) → ∀ x₀ : Eucl N, (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₀ (δ' / 6)) ≤ ENNReal.ofReal (C₁ * l * δ' ^ (m + 1)) := by
    intro N m E v hE
    -- the linear map `L_v` and an operator-norm bound `Λ`
    let Lₗ : Eucl N →ₗ[ℝ] Eucl (m + 1) :=
      { toFun := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
        map_add' := fun x y => by
          ext i
          simp [inner_add_right]
        map_smul' := fun c x => by
          ext i
          simp [inner_smul_right] }
    let Lc : Eucl N →L[ℝ] Eucl (m + 1) := LinearMap.toContinuousLinearMap Lₗ
    let L : Eucl N → Eucl (m + 1) := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
    have hLc : ∀ x, Lc x = L x := fun x => rfl
    set Λ : ℝ := ‖Lc‖ with hΛ
    have hΛ0 : 0 ≤ Λ := norm_nonneg _
    have hLsub : ∀ x y, L x - L y = L (x - y) := fun x y => by
      rw [← hLc, ← hLc, ← hLc]; exact (map_sub Lc x y).symm
    have hLbound : ∀ x, ‖L x‖ ≤ Λ * ‖x‖ := fun x => by
      rw [← hLc]; exact Lc.le_opNorm x
    have hL0 : L 0 = 0 := by rw [← hLc]; exact map_zero Lc
    refine ⟨2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1), by positivity, ?_⟩
    intro B s δ' l hBE hs0 hs1 hδ' hl hcone x₀
    set F : Set (Eucl N) := B ∩ ball x₀ (δ' / 6) with hFdef
    have hFB : F ⊆ B := inter_subset_left
    have hFE : F ⊆ E := hFB.trans hBE
    have hFdist : ∀ a ∈ F, ∀ b ∈ F, ‖b - a‖ < δ' / 3 := by
      intro a ha b hb
      have h1 : dist a x₀ < δ' / 6 := ha.2
      have h2 : dist b x₀ < δ' / 6 := hb.2
      rw [← dist_eq_norm]
      calc dist b a ≤ dist b x₀ + dist a x₀ := dist_triangle_right b a x₀
        _ < δ' / 6 + δ' / 6 := add_lt_add h2 h1
        _ = δ' / 3 := by ring
    -- the partition `F = F₀ ∪ F₁`
    set F₀ : Set (Eucl N) := {a | a ∈ F ∧ ∀ b ∈ F, s / 4 * ‖b - a‖ ≤ ‖L (b - a)‖} with hF₀def
    set F₁ : Set (Eucl N) := {a | a ∈ F ∧ ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖} with hF₁def
    have hFsplit : F ⊆ F₀ ∪ F₁ := by
      intro a ha
      by_cases h : ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖
      · exact Or.inr ⟨ha, h⟩
      · push Not at h
        exact Or.inl ⟨ha, h⟩
    -- (a) graph part
    have hF₀null : (μHE[m + 1] : Measure (Eucl N)) F₀ = 0 :=
      graph_null N m E F₀ v (s / 4) hE (fun a ha => hFE ha.1)
        (by positivity) (fun a ha b hb => ha.2 b hb.1)
    -- (b) the function `h`
    let hfun : Eucl N → ℝ := fun a =>
      sSup ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖})
    have hbdd : ∀ a ∈ F,
        BddAbove ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖}) := by
      intro a ha
      refine ⟨δ' / 3, ?_⟩
      rintro t ⟨b, hb, rfl⟩
      exact (hFdist a ha b hb.1).le
    have hS_le : ∀ a ∈ F, ∀ c ∈ F, ‖L (c - a)‖ < s / 4 * ‖c - a‖ → ‖c - a‖ ≤ hfun a := by
      intro a ha c hc hc'
      exact le_csSup (hbdd a ha) ⟨c, ⟨hc, hc'⟩, rfl⟩
    have hpos : ∀ a ∈ F₁, 0 < hfun a := by
      rintro a ⟨ha, b, hb, hlt⟩
      have hba : b ≠ a := by
        rintro rfl
        simp only [sub_self, hL0, norm_zero, mul_zero, lt_self_iff_false] at hlt
      have : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hba)
      exact this.trans_le (hS_le a ha b hb hlt)
    have hle : ∀ a ∈ F₁, hfun a ≤ δ' / 3 := by
      rintro a ⟨ha, b, hb, hlt⟩
      refine csSup_le ⟨‖b - a‖, ⟨b, ⟨hb, hlt⟩, rfl⟩⟩ ?_
      rintro t ⟨c, hc, rfl⟩
      exact (hFdist a ha c hc.1).le
    have hpartner : ∀ a ∈ F₁, ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖ ∧
        3 * hfun a / 4 < ‖b - a‖ ∧ ‖b - a‖ ≤ hfun a := by
      intro a haF₁
      have hp := hpos a haF₁
      obtain ⟨ha, b, hb, hlt⟩ := haF₁
      have hne : ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖}).Nonempty :=
        ⟨‖b - a‖, ⟨b, ⟨hb, hlt⟩, rfl⟩⟩
      obtain ⟨t, ⟨c, hc, rfl⟩, htc⟩ := exists_lt_of_lt_csSup hne
        (show 3 * hfun a / 4 < hfun a by linarith)
      exact ⟨c, hc.1, hc.2, htc, hS_le a ha c hc.1 hc.2⟩
    -- two cones cover each cylinder
    have hcyl : ∀ a ∈ F₁, (μHE[m + 1] : Measure (Eucl N)) (F ∩ {x | ‖L (x - a)‖ < s * hfun a / 4}) ≤
        2 * ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) := by
      intro a haF₁
      obtain ⟨b, hbF, hb1, hb2, hb3⟩ := hpartner a haF₁
      have haF : a ∈ F := haF₁.1
      have hincl := two_cone_cover N m v F a b s (hfun a) hs0
        (hS_le a haF) hb1 hb2 hb3
      have h2h0 : 0 < 2 * hfun a := by linarith [hpos a haF₁]
      have h2hle : 2 * hfun a ≤ δ' := by linarith [hle a haF₁]
      calc (μHE[m + 1] : Measure (Eucl N)) (F ∩ {x | ‖L (x - a)‖ < s * hfun a / 4})
          ≤ (μHE[m + 1] : Measure (Eucl N))
              ((E ∩ {x | dist x a < 2 * hfun a ∧ ‖L (x - a)‖ < s * ‖x - a‖}) ∪
                (E ∩ {x | dist x b < 2 * hfun a ∧ ‖L (x - b)‖ < s * ‖x - b‖})) := by
            apply measure_mono
            intro x hx
            rcases hincl hx with h | h
            · exact Or.inl ⟨hFE hx.1, h⟩
            · exact Or.inr ⟨hFE hx.1, h⟩
        _ ≤ (μHE[m + 1] : Measure (Eucl N))
              (E ∩ {x | dist x a < 2 * hfun a ∧ ‖L (x - a)‖ < s * ‖x - a‖}) +
            (μHE[m + 1] : Measure (Eucl N))
              (E ∩ {x | dist x b < 2 * hfun a ∧ ‖L (x - b)‖ < s * ‖x - b‖}) :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) +
            ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) :=
            add_le_add (hcone a (hFB haF) _ h2h0 h2hle) (hcone b (hFB hbF) _ h2h0 h2hle)
        _ = 2 * ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) := (two_mul _).symm
    -- (c) Vitali covering of the projected balls
    obtain ⟨I, hIF₁, hIcount, -, hIcover, hIsum⟩ :=
      vitali_packing N m F₁ L (fun a => s * hfun a / 20) (L x₀)
        (s * δ' / 60) (Λ * δ' / 6)
        (fun a ha => by
          have h1 := hpos a ha
          have h2 := hle a ha
          refine ⟨by positivity, ?_⟩
          calc s * hfun a / 20 ≤ s * (δ' / 3) / 20 := by gcongr
            _ = s * δ' / 60 := by ring)
        (fun a ha => by
          have hax : ‖a - x₀‖ < δ' / 6 := by
            have := ha.1.2
            rwa [mem_ball, dist_eq_norm] at this
          rw [dist_eq_norm, hLsub]
          calc ‖L (a - x₀)‖ ≤ Λ * ‖a - x₀‖ := hLbound _
            _ ≤ Λ * (δ' / 6) := mul_le_mul_of_nonneg_left hax.le hΛ0
            _ = Λ * δ' / 6 := by ring)
    -- (d) covering of `F`
    have hcover : F ⊆ F₀ ∪ ⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4}) := by
      intro a ha
      rcases hFsplit ha with h0 | h1
      · exact Or.inl h0
      · right
        obtain ⟨b, hbI, hsub⟩ := hIcover a h1
        have hmem : L a ∈ ball (L a) (s * hfun a / 20) := by
          have := hpos a h1
          exact mem_ball_self (by positivity)
        have hab := hsub hmem
        rw [mem_ball, dist_eq_norm, hLsub] at hab
        refine mem_iUnion₂.2 ⟨b, hbI, ha, ?_⟩
        show ‖L (a - b)‖ < s * hfun b / 4
        linarith
    -- (e) the estimate
    have hsum' : ∑' b : I, ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) ≤
        ENNReal.ofReal ((Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) := hIsum
    calc (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₀ (δ' / 6))
        = (μHE[m + 1] : Measure (Eucl N)) F := rfl
      _ ≤ (μHE[m + 1] : Measure (Eucl N))
            (F₀ ∪ ⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4})) := measure_mono hcover
      _ ≤ (μHE[m + 1] : Measure (Eucl N)) F₀ + (μHE[m + 1] : Measure (Eucl N))
            (⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4})) := measure_union_le _ _
      _ ≤ 0 + ∑' b : I, (μHE[m + 1] : Measure (Eucl N))
            (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4}) := by
          rw [hF₀null]
          gcongr
          exact measure_biUnion_le _ hIcount _
      _ ≤ ∑' b : I, 2 * ENNReal.ofReal (l * (2 * hfun b * s) ^ (m + 1)) := by
          rw [zero_add]
          exact ENNReal.tsum_le_tsum fun b => hcyl b (hIF₁ b.2)
      _ = ∑' b : I, ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) := by
          congr 1
          funext b
          have hreal : 2 * l * 40 ^ (m + 1) * (s * hfun b / 20) ^ (m + 1) =
              2 * (l * (2 * hfun b * s) ^ (m + 1)) := by
            rw [show 2 * hfun b * s = 40 * (s * hfun b / 20) by ring, mul_pow]
            ring
          have h40 : (0 : ℝ) ≤ 2 * l * 40 ^ (m + 1) := mul_nonneg (mul_nonneg (by norm_num) hl) (by positivity)
          rw [← ENNReal.ofReal_mul h40, hreal, ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ∑' b : I, ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ENNReal.ofReal ((Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) := by gcongr
      _ = ENNReal.ofReal (2 * l * 40 ^ (m + 1) * (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) :=
          (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hl) (by positivity))).symm
      _ ≤ ENNReal.ofReal (2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1) * l * δ' ^ (m + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : Λ * δ' / 6 + s * δ' / 60 ≤ (Λ + 1) * δ' / 6 := by nlinarith
          have h2 : (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1) ≤ ((Λ + 1) * δ' / 6) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) h1 _
          calc 2 * l * 40 ^ (m + 1) * (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)
              ≤ 2 * l * 40 ^ (m + 1) * ((Λ + 1) * δ' / 6) ^ (m + 1) := by gcongr
            _ = 2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1) * l * δ' ^ (m + 1) := by
                rw [show (Λ + 1) * δ' / 6 = (Λ + 1) * δ' * (1 / 6) by ring, mul_pow, mul_pow,
                  show (20 / 3 : ℝ) = 40 * (1 / 6) by norm_num, mul_pow]
                ring
  -- Step 2 (Mattila 6.2(1), uniform form): `Hᵏ(B ∩ B̄(x,ρ)) ≤ (c_k/2) ρᵏ` for `x ∈ B`, `ρ ≤ ρ₀` forces `Hᵏ(B) = 0`, where `μHE[k] = c_k • μH[k]`.
  have uniform_density_null : ∀ (N m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (B : Set (Eucl N)) (ρ₀ : ℝ), 0 < ρ₀ → (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → (μHE[m + 1] : Measure (Eucl N)) (B ∩ closedBall x ρ) ≤ ENNReal.ofReal (c * ρ ^ (m + 1))) → (μHE[m + 1] : Measure (Eucl N)) B = 0 := by
    intro N m
    set κ : ℝ≥0 := Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      (μH[((m + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (m + 1)))) with hκ
    have hκ0 : κ ≠ 0 := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (m + 1)
    have hκ0' : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0
    have hdef : ∀ S : Set (Eucl N), (μHE[m + 1] : Measure (Eucl N)) S =
        (κ : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) S := by
      intro S
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have hκpos : (0 : ℝ) < κ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ0)
    refine ⟨(κ : ℝ) / 2, div_pos hκpos two_pos, ?_⟩
    intro B ρ₀ hρ₀ hB
    set c : ℝ := (κ : ℝ) / 2 with hc
    have hc0 : 0 < c := div_pos hκpos two_pos
    have : NullSingletonClass (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) :=
      Measure.nullSingletonClass_hausdorff (Eucl N) (by positivity)
    -- local claim on balls of radius `ρ₀ / 2`
    have hloc : ∀ x₁ ∈ B, (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₁ (ρ₀ / 2)) = 0 := by
      intro x₁ hx₁
      set B' : Set (Eucl N) := B ∩ ball x₁ (ρ₀ / 2) with hB'
      have hfin : (μHE[m + 1] : Measure (Eucl N)) B' < ⊤ := by
        calc (μHE[m + 1] : Measure (Eucl N)) B'
            ≤ (μHE[m + 1] : Measure (Eucl N)) (B ∩ closedBall x₁ (ρ₀ / 2)) :=
              measure_mono (inter_subset_inter_right _ ball_subset_closedBall)
          _ ≤ ENNReal.ofReal (c * (ρ₀ / 2) ^ (m + 1)) :=
              hB x₁ hx₁ _ (by positivity) (by linarith)
          _ < ⊤ := ENNReal.ofReal_lt_top
      have hcov : ∀ t : ℕ → Set (Eucl N), B' ⊆ ⋃ n, t n →
          (∀ n, ediam (t n) ≤ ENNReal.ofReal ρ₀) →
          (μHE[m + 1] : Measure (Eucl N)) B' ≤
            ENNReal.ofReal c * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
        intro t ht hdiam
        have hterm : ∀ n, (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n) ≤
            ENNReal.ofReal c * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
          intro n
          rcases (B' ∩ t n).eq_empty_or_nonempty with he | ⟨x, hxB', hxt⟩
          · rw [he, measure_empty]
            exact zero_le
          · have hne : (t n).Nonempty := ⟨x, hxt⟩
            rw [iSup_pos hne]
            have hdfin : ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
            set d : ℝ := (ediam (t n)).toReal with hd
            have hdeq : ENNReal.ofReal d = ediam (t n) := ENNReal.ofReal_toReal hdfin
            have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
            have hdle : d ≤ ρ₀ := by
              rw [← ENNReal.ofReal_le_ofReal_iff hρ₀.le, hdeq]
              exact hdiam n
            have hpow : ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) = ENNReal.ofReal (d ^ (m + 1)) := by
              rw [← hdeq, ENNReal.rpow_natCast, ENNReal.ofReal_pow hd0]
            rw [hpow, ← ENNReal.ofReal_mul hc0.le]
            rcases hd0.eq_or_lt with hd0' | hdpos
            · have hsub : B' ∩ t n ⊆ {x} := by
                rintro z ⟨-, hz⟩
                have h1 : edist z x ≤ ediam (t n) := edist_le_ediam_of_mem hz hxt
                rw [← hdeq, ← hd0', ENNReal.ofReal_zero, nonpos_iff_eq_zero, edist_eq_zero] at h1
                exact h1
              calc (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n)
                  ≤ (μHE[m + 1] : Measure (Eucl N)) {x} := measure_mono hsub
                _ = 0 := by rw [hdef, measure_singleton, mul_zero]
                _ ≤ _ := zero_le
            · have hsub : B' ∩ t n ⊆ B ∩ closedBall x d := by
                rintro z ⟨hzB', hz⟩
                refine ⟨hzB'.1, ?_⟩
                rw [mem_closedBall, ← ENNReal.ofReal_le_ofReal_iff hd0, ← edist_dist, hdeq]
                exact edist_le_ediam_of_mem hz hxt
              exact (measure_mono hsub).trans (hB x hxB'.1 d hdpos hdle)
        calc (μHE[m + 1] : Measure (Eucl N)) B'
            ≤ (μHE[m + 1] : Measure (Eucl N)) (⋃ n, B' ∩ t n) := by
              refine measure_mono fun x hx => ?_
              obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hx)
              exact mem_iUnion.2 ⟨n, hx, hn⟩
          _ ≤ ∑' n, (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n) := measure_iUnion_le _
          _ ≤ ∑' n, ENNReal.ofReal c * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) :=
              ENNReal.tsum_le_tsum hterm
          _ = ENNReal.ofReal c * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) :=
              ENNReal.tsum_mul_left
      have hc' : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc0).ne'
      have hle : (μHE[m + 1] : Measure (Eucl N)) B' ≤
          ENNReal.ofReal c * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' := by
        have hinf : (μHE[m + 1] : Measure (Eucl N)) B' ≤ ENNReal.ofReal c *
            ⨅ (t : ℕ → Set (Eucl N)) (_ : B' ⊆ ⋃ n, t n)
              (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal ρ₀),
              ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
          rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top)]
          refine le_iInf fun t => le_iInf fun ht => le_iInf fun hdiam => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hcov t ht hdiam
        refine hinf.trans ?_
        gcongr
        rw [Measure.hausdorffMeasure_apply]
        exact le_iSup₂_of_le (ENNReal.ofReal ρ₀) (ENNReal.ofReal_pos.2 hρ₀) le_rfl
      rw [hdef] at hle hfin ⊢
      have hμHfin : (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.mul_top hκ0'] at hfin
        exact lt_irrefl _ hfin
      by_contra hne
      have hμH0 : (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hκle : (κ : ℝ≥0∞) ≤ ENNReal.ofReal c := (ENNReal.mul_le_mul_iff_left hμH0 hμHfin).1 hle
      have hlt : ENNReal.ofReal c < κ := by
        rw [hc, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat]
        exact ENNReal.half_lt_self hκ0' ENNReal.coe_ne_top
      exact absurd hκle (not_le.2 hlt)
    -- globalize with a countable subcover
    obtain ⟨T, hTB, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable B
      (fun x => ball x (ρ₀ / 2)) (fun _ _ => isOpen_ball)
    have hcover : B ⊆ ⋃ x ∈ T, (B ∩ ball x (ρ₀ / 2)) := by
      intro z hz
      have hz' : z ∈ ⋃ x ∈ B, ball x (ρ₀ / 2) := mem_iUnion₂.2 ⟨z, hz, mem_ball_self (by positivity)⟩
      rw [← hTU] at hz'
      obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.1 hz'
      exact mem_iUnion₂.2 ⟨x, hxT, hz, hzx⟩
    exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 fun x hx => hloc x (hTB hx))
  -- Step 3: rational apertures, then Steps 1 and 2 on each `B_q`.
  intro N m E v δ hE hδ
  obtain ⟨c, hc, hudn⟩ := uniform_density_null N m
  obtain ⟨C₁, hC₁, hcde⟩ := conical_density_estimate N m E v hE
  set η₀ : ℝ := c / (C₁ * 24 ^ (m + 1)) with hη₀
  have hη₀pos : 0 < η₀ := by positivity
  -- the sets `B_{s'}` for rational apertures `s'`
  set Bq : ℚ → Set (Eucl N) := fun q => {a | a ∈ E ∧ ∀ r ∈ Ioo (0 : ℝ) δ,
    (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
      ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
        (q : ℝ) * ‖x - a‖}) ≤ ENNReal.ofReal (2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1))} with hBq
  -- Step 3(a)
  have hsub : {a | a ∈ E ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ,
      (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
          s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))} ⊆
      ⋃ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < 1), Bq q := by
    rintro a ⟨haE, ha⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := ha η₀ hη₀pos
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s / 2 < s by linarith)
    have hq0 : (0 : ℝ) < q := by linarith
    refine mem_iUnion₂.2 ⟨q, ⟨hq0, by linarith⟩, haE, fun r hr => ?_⟩
    calc (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            (q : ℝ) * ‖x - a‖})
        ≤ (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖}) := by
          refine measure_mono (inter_subset_inter_right _ fun x hx => ⟨hx.1, hx.2.trans_le ?_⟩)
          exact mul_le_mul_of_nonneg_right hq2.le (norm_nonneg _)
      _ ≤ ENNReal.ofReal (η₀ * (r * s) ^ (m + 1)) := hs r hr
      _ ≤ ENNReal.ofReal (2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have hr0 : 0 ≤ r := hr.1.le
          have h1 : (r * s) ^ (m + 1) ≤ (2 * (r * q)) ^ (m + 1) := by
            apply pow_le_pow_left₀ (by positivity)
            nlinarith
          calc η₀ * (r * s) ^ (m + 1) ≤ η₀ * (2 * (r * q)) ^ (m + 1) :=
                mul_le_mul_of_nonneg_left h1 hη₀pos.le
            _ = 2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1) := by rw [mul_pow]; ring
  -- Step 3(b)
  have hnull : ∀ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 → (μHE[m + 1] : Measure (Eucl N)) (Bq q) = 0 := by
    rintro q ⟨hq0, hq1⟩
    apply hudn (Bq q) (δ / 13) (by positivity)
    intro x hx ρ hρ hρle
    have hcd := hcde (Bq q) q (12 * ρ) (2 ^ (m + 1) * η₀) (fun a ha => ha.1) hq0 hq1
      (by positivity) (by positivity) (fun a ha r hr0 hrle => ha.2 r ⟨hr0, by linarith⟩) x
    calc (μHE[m + 1] : Measure (Eucl N)) (Bq q ∩ closedBall x ρ)
        ≤ (μHE[m + 1] : Measure (Eucl N)) (Bq q ∩ ball x (12 * ρ / 6)) :=
          measure_mono (inter_subset_inter_right _ (closedBall_subset_ball (by linarith)))
      _ ≤ ENNReal.ofReal (C₁ * (2 ^ (m + 1) * η₀) * (12 * ρ) ^ (m + 1)) := hcd
      _ = ENNReal.ofReal (c * ρ ^ (m + 1)) := by
          congr 1
          have h24 : (24 : ℝ) ^ (m + 1) = 2 ^ (m + 1) * 12 ^ (m + 1) := by
            rw [← mul_pow]; norm_num
          rw [hη₀, mul_pow, h24]
          field_simp
  apply measure_mono_null hsub
  refine measure_iUnion_null fun q => measure_iUnion_null fun hq => hnull q hq

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
