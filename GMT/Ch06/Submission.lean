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

/-- The distribution function `G(r) = ν((a,b) ∩ (-∞, r])` of a measure `ν` on `ℝ` with
`ν((a,b)) < ∞` is nondecreasing and right-continuous. -/
theorem Submission.slicing_mb_dm_distribution_mono_rightcont :
    ∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ →
      Monotone (fun r : ℝ => (ν (Ioo a b ∩ Iic r)).toReal) ∧
      ∀ s : ℝ, ContinuousWithinAt (fun r : ℝ => (ν (Ioo a b ∩ Iic r)).toReal) (Ici s) s := by
  intro ν a b hab
  -- Each `A_r = (a,b) ∩ (-∞, r]` lies in `(a,b)`, so `ν(A_r) < ∞`.
  have hfin : ∀ r : ℝ, ν (Ioo a b ∩ Iic r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top hab (measure_mono inter_subset_left)
  -- `r ↦ A_r` is monotone, hence so is `G`.
  have hsub : ∀ r r' : ℝ, r ≤ r' → Ioo a b ∩ Iic r ⊆ Ioo a b ∩ Iic r' := fun r r' h =>
    inter_subset_inter_right _ (Iic_subset_Iic.2 h)
  refine ⟨fun r r' h => ENNReal.toReal_mono (hfin r') (measure_mono (hsub r r' h)), fun s => ?_⟩
  -- Continuity within `[s, ∞)` is continuity within `(s, ∞)`.
  rw [← continuousWithinAt_Ioi_iff_Ici]
  -- `⋂_{r > s} A_r = A_s`.
  have hinter : (⋂ r > s, Ioo a b ∩ Iic r) = Ioo a b ∩ Iic s := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_Iic]
    constructor
    · intro h
      exact ⟨(h (s + 1) (by linarith)).1, le_of_forall_gt_imp_ge_of_dense fun r hr => (h r hr).2⟩
    · intro h r hr
      exact ⟨h.1, h.2.trans hr.le⟩
  -- Continuity of `ν` from above along `r ↓ s`, using `ν(A_{s+1}) < ∞`.
  have hlim : Tendsto (fun r => ν (Ioo a b ∩ Iic r)) (𝓝[>] s) (𝓝 (ν (Ioo a b ∩ Iic s))) := by
    rw [← hinter]
    exact tendsto_measure_biInter_gt (s := fun r => Ioo a b ∩ Iic r)
      (fun r _ => (measurableSet_Ioo.inter measurableSet_Iic).nullMeasurableSet)
      (fun i j _ hij => hsub i j hij) ⟨s + 1, by linarith, hfin (s + 1)⟩
  -- `toReal` is continuous at the finite value `ν(A_s)`.
  exact (ENNReal.tendsto_toReal (hfin s)).comp hlim
/-- The lower left Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` of a
nondecreasing right-continuous `G : ℝ → ℝ` is Borel measurable. -/
theorem Submission.slicing_mb_dm_lowerLeftDini_measurable :
    ∀ G : ℝ → ℝ, Monotone G → (∀ s : ℝ, ContinuousWithinAt G (Ici s) s) →
      Measurable (fun t : ℝ => liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k))
        (𝓝[>] 0)) := by
  intro G hG hG_cont
  -- The intervals `(0, 1/(j+1))`, `j ∈ ℕ`, form a basis of `𝓝[>] 0`.
  have hbasis : (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True)
      (fun j => Ioo 0 (1 / ((j : ℝ) + 1))) := by
    refine (nhdsGT_basis (0 : ℝ)).to_hasBasis (fun δ hδ => ?_) (fun j _ => ?_)
    · obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, trivial, Ioo_subset_Ioo_right hj.le⟩
    · exact ⟨1 / ((j : ℝ) + 1), Nat.one_div_pos_of_nat, subset_rfl⟩
  -- Right-continuity of `G` makes `k ↦ F_t(k)` left-continuous at each `k > 0`.
  have hleft : ∀ t k : ℝ, 0 < k → ContinuousWithinAt
      (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (Iio k) k := by
    intro t k hk
    have hGk : ContinuousWithinAt (fun x : ℝ => G (t - x)) (Iio k) k := by
      have h1 : ContinuousWithinAt G (Ioi (t - k)) (t - k) :=
        continuousWithinAt_Ioi_iff_Ici.2 (hG_cont (t - k))
      refine h1.comp (continuous_const.sub continuous_id).continuousWithinAt ?_
      intro x hx
      simp only [mem_Ioi, mem_Iio] at hx ⊢
      linarith
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_const.sub hGk).div continuousWithinAt_id hk.ne')
  -- The infimum over real `k ∈ (0, δ)` equals the infimum over rational `q ∈ (0, δ)`.
  have hrat : ∀ t δ : ℝ, (⨅ k ∈ Ioo 0 δ, ENNReal.ofReal ((G t - G (t - k)) / k)) =
      ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), ENNReal.ofReal ((G t - G (t - q)) / q) := by
    intro t δ
    refine le_antisymm (le_iInf₂ fun q hq => iInf₂_le (q : ℝ) hq) (le_iInf₂ fun k hk => ?_)
    -- Approximate `k` from the left by rationals `q n ∈ (max 0 (k - 1/(n+1)), k)`.
    have hex : ∀ n : ℕ, ∃ q : ℚ, max 0 (k - 1 / ((n : ℝ) + 1)) < q ∧ (q : ℝ) < k := fun n =>
      exists_rat_btwn (max_lt hk.1 (sub_lt_self k Nat.one_div_pos_of_nat))
    choose q hq_lo hq_hi using hex
    have hq_tendsto : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[<] k) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall hq_hi)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => k - 1 / ((n : ℝ) + 1))
        (h := fun _ => k) ?_ tendsto_const_nhds
        (fun n => (le_max_right _ _).trans (hq_lo n).le) (fun n => (hq_hi n).le)
      simpa using (tendsto_const_nhds (f := (atTop : Filter ℕ)) (x := k)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine ge_of_tendsto' ((hleft t k hk.1).tendsto.comp hq_tendsto) fun n => ?_
    exact iInf₂_le (q n) ⟨(le_max_left _ _).trans_lt (hq_lo n), (hq_hi n).trans hk.2⟩
  -- Hence `D(t) = ⨆ j, ⨅ q ∈ ℚ ∩ (0, 1/(j+1)), F_t(q)`, a countable formula.
  have hformula : (fun t : ℝ => liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k))
      (𝓝[>] 0)) = fun t => ⨆ j : ℕ, ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 (1 / ((j : ℝ) + 1))),
        ENNReal.ofReal ((G t - G (t - q)) / q) := by
    funext t
    rw [hbasis.liminf_eq_iSup_iInf]
    simp only [iSup_true]
    exact iSup_congr fun j => hrat t _
  -- `G` is monotone, hence measurable, so each `t ↦ F_t(q)` is measurable.
  rw [hformula]
  have hGm : Measurable G := hG.measurable
  refine Measurable.iSup fun j => Measurable.iInf fun q => Measurable.iInf_Prop _ ?_
  exact ENNReal.measurable_ofReal.comp
    ((hGm.sub (hGm.comp (measurable_id.sub_const _))).div_const _)
/-- For nondecreasing `G : ℝ → ℝ` and `a ≤ b`, the lower integral over `(a, b)` of the lower left
Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` is at most `G b - G a`. -/
theorem Submission.slicing_mb_dm_lintegral_lowerLeftDini_le :
    ∀ G : ℝ → ℝ, Monotone G → ∀ a b : ℝ, a ≤ b →
      ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤
        ENNReal.ofReal (G b - G a) := by
  intro G hG a b hab
  -- Step sizes `δ n = 1/(n+1) → 0+`.
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => Nat.one_div_pos_of_nat
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_tendsto : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ_lim
      (Eventually.of_forall hδ_pos)
  -- Truncated left difference quotients `F n t = 1_{t > a + δ n} ofReal (G t - G (t - δ n)) / δ n`.
  set F : ℕ → ℝ → ℝ≥0∞ := fun n => (Ioi (a + δ n)).indicator
    (fun t => ENNReal.ofReal ((G t - G (t - δ n)) / δ n)) with hF_def
  have hGm : Measurable G := hG.measurable
  have hF_meas : ∀ n, Measurable (F n) := fun n =>
    (ENNReal.measurable_ofReal.comp
      ((hGm.sub (hGm.comp (measurable_id.sub_const _))).div_const _)).indicator measurableSet_Ioi
  -- For `t ∈ (a, b)`: `δ n → 0+`, and `t > a + δ n` eventually, so `D(t) ≤ liminf_n F n t`.
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤
        liminf (fun n => F n t) atTop := by
    intro t ht
    refine hδ_tendsto.liminf_le_liminf_comp.trans_eq (liminf_congr ?_)
    filter_upwards [(tendsto_order.1 hδ_lim).2 _ (sub_pos.2 ht.1)] with n hn
    have hmem : t ∈ Ioi (a + δ n) := by
      simp only [mem_Ioi]
      linarith
    simp only [hF_def, Function.comp_apply, indicator_of_mem hmem]
  -- Each `F n` integrates over `(a, b)` to at most `G b - G a`.
  have hbound : ∀ n, ∫⁻ t in Ioo a b, F n t ≤ ENNReal.ofReal (G b - G a) := by
    intro n
    have hc : 0 < δ n := hδ_pos n
    simp only [hF_def]
    rw [setLIntegral_indicator measurableSet_Ioi, inter_comm, Ioo_inter_Ioi,
      max_eq_right (by linarith : a ≤ a + δ n)]
    rcases le_or_gt b (a + δ n) with hb | hb
    · rw [Ioo_eq_empty (not_lt.2 hb), setLIntegral_empty]
      exact zero_le
    -- On `(a + δ n, b)` the quotient is nonnegative and integrable, and
    -- `∫_{a+δ}^b (G t - G (t - δ)) dt = ∫_{b-δ}^b G - ∫_a^{a+δ} G ≤ δ (G b - G a)`.
    have hGc : Monotone (fun t => G (t - δ n)) := fun x y hxy => hG (by linarith)
    have hint : IntervalIntegrable (fun t => (G t - G (t - δ n)) / δ n) volume (a + δ n) b :=
      (hG.intervalIntegrable.sub hGc.intervalIntegrable).div_const _
    have hintOn : IntegrableOn (fun t => (G t - G (t - δ n)) / δ n) (Ioo (a + δ n) b) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 hint).mono_set Ioo_subset_Ioc_self
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (a + δ n) b)]
        (fun t => (G t - G (t - δ n)) / δ n) :=
      Eventually.of_forall fun t => div_nonneg (sub_nonneg.2 (hG (by linarith))) hc.le
    have hreal : ∫ t in Ioo (a + δ n) b, (G t - G (t - δ n)) / δ n ≤ G b - G a := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.le,
        intervalIntegral.integral_div,
        intervalIntegral.integral_sub hG.intervalIntegrable hGc.intervalIntegrable,
        intervalIntegral.integral_comp_sub_right G (δ n), add_sub_cancel_right, div_le_iff₀ hc]
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (μ := volume) (a := a + δ n) (b := b - δ n))
        (hG.intervalIntegrable (μ := volume) (a := b - δ n) (b := b))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (μ := volume) (a := a) (b := a + δ n))
        (hG.intervalIntegrable (μ := volume) (a := a + δ n) (b := b - δ n))
      have h3 : ∫ x in (b - δ n)..b, G x ≤ δ n * G b := by
        have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : b - δ n ≤ b)
          hG.intervalIntegrable intervalIntegrable_const (fun x hx => hG hx.2)
        simpa [intervalIntegral.integral_const] using this
      have h4 : δ n * G a ≤ ∫ x in a..(a + δ n), G x := by
        have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + δ n)
          intervalIntegrable_const hG.intervalIntegrable (fun x hx => hG hx.1)
        simpa [intervalIntegral.integral_const] using this
      linarith
    calc ∫⁻ t in Ioo (a + δ n) b, ENNReal.ofReal ((G t - G (t - δ n)) / δ n)
        = ENNReal.ofReal (∫ t in Ioo (a + δ n) b, (G t - G (t - δ n)) / δ n) :=
          (ofReal_integral_eq_lintegral_ofReal hintOn hnonneg).symm
      _ ≤ ENNReal.ofReal (G b - G a) := ENNReal.ofReal_le_ofReal hreal
  -- Fatou's lemma.
  calc ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun n => F n t) atTop := setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ liminf (fun n => ∫⁻ t in Ioo a b, F n t) atTop := lintegral_liminf_le hF_meas
    _ ≤ ENNReal.ofReal (G b - G a) := liminf_le_of_frequently_le' (Frequently.of_forall hbound)
/-- **Lower left density versus the lower left Dini derivative** (Simon Ch. 6, p. 158, the step
"4.9 gives 4.10").  Let `ν((a, b)) < ∞`, `G r = ν((a, b) ∩ (-∞, r])` (as a real number) and
`t ∈ (a, b)`.  Then `liminf_{h → 0+} ν([t - h, t]) / h ≤ liminf_{k → 0+} (G t - G (t - k)) / k`.
For `c > 1` and `0 < k < t - a`, `[t - k / c, t] ⊆ (a, b) ∩ (t - k, t]`, a band of mass
`G t - G (t - k)`, so the density at `h = k / c` is at most `c · (G t - G (t - k)) / k`.
Reparametrizing `h = k / c` gives `liminf ≤ c · liminf`, and `c ↓ 1` finishes. -/
theorem Submission.slicing_mb_dm_density_le_lowerLeftDini : ∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ → ∀ t ∈ Ioo a b, liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ liminf (fun k : ℝ => ENNReal.ofReal (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) := by
  intro ν a b hν t ht
  obtain ⟨hat, htb⟩ := ht
  -- Step 1: `A_r = (a, b) ∩ (-∞, r]` has finite measure, so `G r = ν(A_r).toReal` is monotone.
  have hfin : ∀ r : ℝ, ν (Ioo a b ∩ Iic r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top hν (measure_mono inter_subset_left)
  have hmono : ∀ r r' : ℝ, r ≤ r' →
      (ν (Ioo a b ∩ Iic r)).toReal ≤ (ν (Ioo a b ∩ Iic r')).toReal := fun r r' hr =>
    ENNReal.toReal_mono (hfin r') (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hr)))
  -- Step 2: for `s' ≤ s`, `A_s = A_{s'} ⊔ ((a, b) ∩ (s', s])`, so
  -- `ν((a, b) ∩ (s', s]) = G s - G s'`.
  have hincr : ∀ s' s : ℝ, s' ≤ s → ν (Ioo a b ∩ Ioc s' s) =
      ENNReal.ofReal ((ν (Ioo a b ∩ Iic s)).toReal - (ν (Ioo a b ∩ Iic s')).toReal) := by
    intro s' s hs
    have hunion : Ioo a b ∩ Iic s = (Ioo a b ∩ Iic s') ∪ (Ioo a b ∩ Ioc s' s) := by
      ext x
      simp only [mem_inter_iff, mem_union, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨hx, hxs⟩
        by_cases hxs' : x ≤ s'
        · exact Or.inl ⟨hx, hxs'⟩
        · exact Or.inr ⟨hx, lt_of_not_ge hxs', hxs⟩
      · rintro (⟨hx, hxs'⟩ | ⟨hx, -, hxs⟩)
        · exact ⟨hx, hxs'.trans hs⟩
        · exact ⟨hx, hxs⟩
    have hdisj : Disjoint (Ioo a b ∩ Iic s') (Ioo a b ∩ Ioc s' s) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx₁⟩ ⟨-, hx₂, -⟩
      exact absurd hx₁ (not_le.2 hx₂)
    have hB : ν (Ioo a b ∩ Ioc s' s) ≠ ∞ :=
      ne_top_of_le_ne_top hν (measure_mono inter_subset_left)
    have hadd : (ν (Ioo a b ∩ Iic s)).toReal =
        (ν (Ioo a b ∩ Iic s')).toReal + (ν (Ioo a b ∩ Ioc s' s)).toReal := by
      rw [hunion, measure_union hdisj (measurableSet_Ioo.inter measurableSet_Ioc),
        ENNReal.toReal_add (hfin s') hB]
    rw [← ENNReal.ofReal_toReal hB, hadd, add_sub_cancel_left]
  -- Step 3: for `c > 1` and `0 < k < t - a`, `h = k / c` gives `[t - h, t] ⊆ (a, b) ∩ (t - k, t]`,
  -- hence `ν([t - h, t]) / h ≤ c · (G t - G (t - k)) / k`.
  have hband : ∀ c : ℝ, 1 < c → ∀ᶠ k in 𝓝[>] (0 : ℝ),
      ν (Icc (t - k / c) t) / ENNReal.ofReal (k / c) ≤ ENNReal.ofReal c * ENNReal.ofReal
        (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k) := by
    intro c hc
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hat)] with k hk
    obtain ⟨hk0, hkt⟩ := hk
    have hc0 : 0 < c := zero_lt_one.trans hc
    have hhk : k / c < k := div_lt_self hk0 hc
    have hsub : Icc (t - k / c) t ⊆ Ioo a b ∩ Ioc (t - k) t := by
      rintro x ⟨hx₁, hx₂⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, hx₂⟩
    have hΔ0 : 0 ≤ ((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k :=
      div_nonneg (sub_nonneg.2 (hmono _ _ (by linarith))) hk0.le
    apply ENNReal.div_le_of_le_mul
    calc ν (Icc (t - k / c) t) ≤ ν (Ioo a b ∩ Ioc (t - k) t) := measure_mono hsub
      _ = ENNReal.ofReal (c * (((ν (Ioo a b ∩ Iic t)).toReal -
            (ν (Ioo a b ∩ Iic (t - k))).toReal) / k) * (k / c)) := by
        rw [hincr _ _ (by linarith)]
        congr 1
        field_simp
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc0.le hΔ0), ENNReal.ofReal_mul hc0.le]
  -- Steps 4–5: reparametrize `h = k / c` and factor out the constant `ofReal c`.
  have hc_bound : ∀ c : ℝ, 1 < c →
      liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤
        ENNReal.ofReal c * liminf (fun k : ℝ => ENNReal.ofReal
          (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) := by
    intro c hc
    have hc0 : 0 < c := zero_lt_one.trans hc
    have htend : Tendsto (fun k : ℝ => k / c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun k : ℝ => k / c) (𝓝 0) (𝓝 (0 / c)) := tendsto_id.div_const c
        rw [zero_div] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with k hk
        exact div_pos hk hc0
    calc liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0)
        ≤ liminf (fun k : ℝ => ν (Icc (t - k / c) t) / ENNReal.ofReal (k / c)) (𝓝[>] 0) :=
          htend.liminf_le_liminf_comp
      _ ≤ liminf (fun k : ℝ => ENNReal.ofReal c * ENNReal.ofReal
            (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) :=
          liminf_le_liminf (hband c hc)
      _ = _ := ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
  -- Step 6: let `c_n = 1 + 1 / (n + 1) ↓ 1`.
  set D := liminf (fun k : ℝ => ENNReal.ofReal
    (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0)
  rcases eq_or_ne D ∞ with hD | hD
  · rw [hD]
    exact le_top
  · have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * D) atTop (𝓝 D) := by
      simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hD)
    refine ge_of_tendsto h2 (Eventually.of_forall fun n => hc_bound _ ?_)
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The measurable majorant in Simon Ch. 6, 4.10 (`M_W(T ⌞ {f < t})` is increasing in `t`, so
it is differentiable a.e. and its derivative integrates to at most `M_W(T ⌞ {a < f < b})`), for
a Borel measure `ν` on `ℝ`: the lower left density `liminf_{h → 0+} ν([t - h, t]) / h` has a
Borel majorant on `(a, b)` whose integral over `(a, b)` is at most `ν((a, b))`.
If `ν((a, b)) = ∞` the constant `∞` works.  Otherwise the distribution function
`G(r) = ν((a, b) ∩ (-∞, r])` is nondecreasing and right-continuous, and the majorant is `D` on
`(a, b)` and `0` elsewhere, where `D(t) = liminf_{k → 0+} (G(t) - G(t - k)) / k` is the lower
left Dini derivative of `G`: `D` is Borel, it dominates the closed-band density, and by
Lebesgue's theorem for monotone functions `∫_{(a,b)} D ≤ G(b) - G(a) = ν((a, b))`. -/
theorem Submission.slicing_mb_density_majorant :
    ∀ (ν : Measure ℝ) (a b : ℝ), a < b → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧
      (∀ t ∈ Ioo a b,
        liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ g t) ∧
      ∫⁻ t in Ioo a b, g t ≤ ν (Ioo a b) := by
  intro ν a b hab
  -- If `ν((a, b)) = ∞`, take `g ≡ ∞`.
  by_cases hQ : ν (Ioo a b) = ∞
  · exact ⟨fun _ => ∞, measurable_const, fun _ _ => le_top, by rw [hQ]; exact le_top⟩
  obtain ⟨hG_mono, hG_right⟩ := Submission.slicing_mb_dm_distribution_mono_rightcont ν a b hQ
  set G : ℝ → ℝ := fun r => (ν (Ioo a b ∩ Iic r)).toReal
  set D : ℝ → ℝ≥0∞ := fun t =>
    liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0)
  refine ⟨(Ioo a b).indicator D,
    (Submission.slicing_mb_dm_lowerLeftDini_measurable G hG_mono hG_right).indicator
      measurableSet_Ioo, fun t ht => ?_, ?_⟩
  · -- On `(a, b)` the closed-band density is at most `D = g`.
    rw [Set.indicator_of_mem ht]
    exact Submission.slicing_mb_dm_density_le_lowerLeftDini ν a b hQ t ht
  · -- `∫⁻_{(a,b)} g = ∫⁻_{(a,b)} D ≤ G(b) - G(a)`, with `G(a) = 0` and `G(b) = ν((a, b))`.
    have hGa : G a = 0 := by
      have h : Ioo a b ∩ Iic a = ∅ :=
        eq_empty_of_forall_notMem fun x (hx : x ∈ Ioo a b ∩ Iic a) => not_le.2 hx.1.1 hx.2
      simp only [G, h, measure_empty, ENNReal.toReal_zero]
    have hGb : G b = (ν (Ioo a b)).toReal := by
      have h : Ioo a b ∩ Iic b = Ioo a b := inter_eq_left.2 fun x (hx : x ∈ Ioo a b) => hx.2.le
      simp only [G, h]
    rw [setLIntegral_congr_fun measurableSet_Ioo fun t ht => Set.indicator_of_mem ht D]
    calc ∫⁻ t in Ioo a b, D t ≤ ENNReal.ofReal (G b - G a) :=
          Submission.slicing_mb_dm_lintegral_lowerLeftDini_le G hG_mono a b hab.le
      _ = ν (Ioo a b) := by rw [hGa, hGb, sub_zero, ENNReal.ofReal_toReal hQ]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
