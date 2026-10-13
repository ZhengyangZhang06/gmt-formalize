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

/-- **Support of a current vanishing off a closed set (Simon Ch. 6, 2.11).**  If `Z ∈ 𝒟_q(V)`,
`V` open, kills every test form whose support misses the closed set `K`, then `spt Z ⊆ K`.  A point
`x ∈ V \ K` has a ball `B_ε(x) ⊆ V \ K`; `W = B_{ε/2}(x)` is open with compact closure
`closure W ⊆ B_ε(x) ⊆ V`, and `Z` vanishes on `W`, so `x` lies in the zero region of `Z`. -/
theorem Submission.fiw_tb_ext_support_subset : ∀ (P q : ℕ) (V K : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen V → IsClosed K → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → Z.support ⊆ K := by
  intro P q V K Z hV hK hZ x hx
  by_contra hxK
  obtain ⟨hxV, hxz⟩ := hx
  -- `V \ K` is an open neighbourhood of `x`: pick `B_ε(x) ⊆ V \ K`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hV.sdiff hK) x ⟨hxV, hxK⟩
  -- `W = B_{ε/2}(x)` is one of the open sets whose union is the zero region of `Z`.
  apply hxz
  refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (half_pos hε)⟩
  · exact (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  · exact (closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (half_lt_self hε))).trans (hball.trans sdiff_subset)
  · -- a test form supported in `W ⊆ B_ε(x)` has support disjoint from `K`
    intro ω hω
    apply hZ
    rw [Set.disjoint_left]
    intro y hy hyK
    exact (hball (ball_subset_ball (half_le_self hε.le) (hω hy))).2 hyK
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
/-- **Covector evaluation bound** (for `M(T) < ∞` in the proof of Simon Ch. 6, 6.1, p. 169).
If `|τ_j| ≤ 1` for all `j`, then `|α(τ_1, …, τ_n)| ≤ P^n |α|`, `|α|` the Euclidean coefficient
norm of Remark 2.6.  Expanding each `τ_j` in the standard basis `e_1, …, e_P` gives
`α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)` over the `P^n` maps `f : Fin n → Fin P`.  Each coefficient has
absolute value at most `1`, and `|α(e_f)| ≤ |α|`: `α(e_f) = 0` unless `f` is injective, and then
`α(e_f) = ±α(e_{f ∘ σ})` for the permutation `σ` sorting `f`, where `f ∘ σ` is strictly
increasing. -/
theorem Submission.isoperimetric_abs_covector_apply_le : ∀ (P n : ℕ) (α : Covector (Eucl P) n) (τ : Fin n → Eucl P), (∀ j, ‖τ j‖ ≤ 1) → |α τ| ≤ (P : ℝ) ^ n * covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `|α(e_f)| ≤ |α|` for every `f : Fin n → Fin P`.
  have hcoef : ∀ f : Fin n → Fin P,
      |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| ≤ covectorEuclideanNorm α := by
    intro f
    by_cases hf : Function.Injective f
    · -- Sort `f`: `f ∘ σ` is monotone and injective, hence strictly increasing.
      set σ := Tuple.sort f
      have hmono : StrictMono (f ∘ σ) :=
        (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
      have hperm : α (fun j => EuclideanSpace.basisFun (Fin P) ℝ ((f ∘ σ) j)) =
          Equiv.Perm.sign σ • α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) :=
        α.toAlternatingMap.map_perm (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) σ
      have habs : |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| =
          |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ ((f ∘ σ) j))| := by
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      -- `α(e_{f ∘ σ})²` is one of the summands of `|α|²`.
      rw [habs]
      unfold covectorEuclideanNorm
      apply Real.abs_le_sqrt
      have := Finset.single_le_sum (f := fun I : Fin n → Fin P =>
          if StrictMono I then (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ (f ∘ σ))
      simpa only [hmono, ite_true] using this
    · -- Two equal arguments: `α(e_f) = 0`.
      have hv : ¬Function.Injective fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j) :=
        fun hv => hf (Function.Injective.of_comp (f := EuclideanSpace.basisFun (Fin P) ℝ) hv)
      rw [α.map_eq_zero_of_not_injective _ hv, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  -- Step 2: multilinear expansion `α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)`.
  have hexp : α τ = ∑ f : Fin n → Fin P,
      (∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) := by
    have h1 : α τ = α (fun j => ∑ a, τ j a • EuclideanSpace.basisFun (Fin P) ℝ a) := by
      congr 1
      funext j
      simpa only [EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (τ j)).symm
    rw [h1, α.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [α.map_smul_univ, smul_eq_mul]
  -- Step 3: `|∏_j τ_j(f j)| ≤ 1`, as `|τ_j(a)| ≤ |τ_j| ≤ 1`.
  have hprod : ∀ f : Fin n → Fin P, |∏ j, τ j (f j)| ≤ 1 := by
    intro f
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ =>
      (show |τ j (f j)| ≤ ‖τ j‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (τ j) (f j)).trans (hτ j)
  -- Step 4: sum the bound `|α|` over the `P ^ n` maps `f`.
  calc |α τ| = |∑ f : Fin n → Fin P,
        (∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| := by
          rw [hexp]
    _ ≤ ∑ f : Fin n → Fin P,
        |(∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : Fin n → Fin P, covectorEuclideanNorm α := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul]
        calc |∏ j, τ j (f j)| * |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))|
            ≤ 1 * covectorEuclideanNorm α :=
              mul_le_mul (hprod f) (hcoef f) (abs_nonneg _) zero_le_one
          _ = covectorEuclideanNorm α := one_mul _
    _ = (P : ℝ) ^ n * covectorEuclideanNorm α := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

/-- Locality of currents: test forms that agree on an open neighbourhood `N` of `spt T` have the
same value, since `ψ - φ` vanishes on `N`, so its support lies in the closed set `Nᶜ`, which misses
`spt T`. -/
theorem Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ψ φ : TestFormOn U n)
      (N : Set (Eucl P)), IsOpen N → T.support ⊆ N →
      (∀ x ∈ N, (ψ : DifferentialForm (Eucl P) n) x = (φ : DifferentialForm (Eucl P) n) x) →
      T ψ = T φ := by
  intro P n U T ψ φ N hN hTN hψφ
  -- `ψ - φ` vanishes on the open set `N`, so `tsupport (ψ - φ) ⊆ Nᶜ`.
  have hsupp : tsupport ((ψ - φ : TestFormOn U n) : DifferentialForm (Eucl P) n) ⊆ Nᶜ := by
    refine closure_minimal ?_ hN.isClosed_compl
    intro x hx hxN
    apply hx
    rw [Submodule.coe_sub, Pi.sub_apply, hψφ x hxN, sub_self]
  -- `Nᶜ` misses `spt T ⊆ N`, so `T (ψ - φ) = 0`.
  have hzero : T (ψ - φ) = 0 :=
    Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U T (ψ - φ)
      (Set.disjoint_of_subset_left hsupp (Set.disjoint_compl_left_iff_subset.2 hTN))
  have hsub : T.toCurrent (ψ - φ) = T.toCurrent ψ - T.toCurrent φ := map_sub T.toCurrent ψ φ
  change T.toCurrent ψ = T.toCurrent φ
  rw [← sub_eq_zero, ← hsub]
  exact hzero
/-- Cut-off of a null sequence: if every derivative of `ψ_l` tends to `0` uniformly on
`K = tsupport ζ`, then the test forms `φ_l = ζ ψ_l` tend to `0` in `𝒟ᵏ(U)`.  By the Leibniz rule,
`D^j φ_l` is controlled on `K` by the bounded derivatives of `ζ` and the derivatives of `ψ_l` of
order `≤ j`. -/
theorem Submission.iwl_cr_ce_cutoff_converges_zero :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (ζ : Eucl P → ℝ) (ψs : ℕ → DifferentialForm (Eucl P) k)
      (φs : ℕ → TestFormOn U k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ U → (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψs l)) →
      (∀ l x, (φs l : DifferentialForm (Eucl P) k) x = ζ x • ψs l x) →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ,
        ‖iteratedFDeriv ℝ j (ψs l) x‖ ≤ ε) →
      TestFormOnConverges φs 0 := by
  intro P k U ζ ψs φs hζ hζc hζU hψ hφ hsmall
  -- Leibniz estimate, by induction on the order `j`, for a continuous bilinear `B`: if every
  -- derivative of `f` is bounded on `K = tsupport ζ` and every derivative of `g l` tends to `0`
  -- uniformly on `K`, then `D^j (B (f ·) (g l ·))` tends to `0` uniformly on `K`.
  have key : ∀ (j : ℕ) (F₁ F₂ G : Type) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
      [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : F₁ →L[ℝ] F₂ →L[ℝ] G) (f : Eucl P → F₁) (g : ℕ → Eucl P → F₂),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l)) →
      (∀ i, ∃ C, ∀ x ∈ tsupport ζ, ‖iteratedFDeriv ℝ i f x‖ ≤ C) →
      (∀ (i : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ,
        ‖iteratedFDeriv ℝ i (g l) x‖ ≤ ε) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ,
        ‖iteratedFDeriv ℝ j (fun y => B (f y) (g l y)) x‖ ≤ ε := by
    intro j
    induction j with
    | zero =>
      intro F₁ F₂ G _ _ _ _ _ _ B f g _ _ hfb hgs ε hε
      obtain ⟨C, hC⟩ := hfb 0
      have hA : 0 < ‖B‖ * |C| + 1 := by positivity
      filter_upwards [hgs 0 (ε / (‖B‖ * |C| + 1)) (div_pos hε hA)] with l hl x hx
      have h1 := hC x hx
      have h2 := hl x hx
      rw [norm_iteratedFDeriv_zero] at h1 h2 ⊢
      calc ‖B (f x) (g l x)‖ ≤ ‖B‖ * ‖f x‖ * ‖g l x‖ := B.le_opNorm₂ _ _
        _ ≤ (‖B‖ * |C| + 1) * (ε / (‖B‖ * |C| + 1)) := by
          apply mul_le_mul _ h2 (norm_nonneg _) hA.le
          nlinarith [norm_nonneg B, h1.trans (le_abs_self C), norm_nonneg (f x)]
        _ = ε := by field_simp
    | succ j ih =>
      intro F₁ F₂ G _ _ _ _ _ _ B f g hf hg hfb hgs ε hε
      have hf' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right le_rfl
      have hg' : ∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (g l)) :=
        fun l => (hg l).fderiv_right le_rfl
      -- `D (B (f ·) (g l ·)) = B (f ·) (D (g l) ·) + B (D f ·) (g l ·)`, with the bilinear maps
      -- `precompR` and `precompL` built from `B`.
      have hD : ∀ l, fderiv ℝ (fun y => B (f y) (g l y)) =
          fun y => B.precompR (Eucl P) (f y) (fderiv ℝ (g l) y) +
            B.precompL (Eucl P) (fderiv ℝ f y) (g l y) := fun l => funext fun y =>
        B.fderiv_of_bilinear (hf.differentiable (by simp)).differentiableAt
          ((hg l).differentiable (by simp)).differentiableAt
      have h1 := ih F₁ (Eucl P →L[ℝ] F₂) (Eucl P →L[ℝ] G) (B.precompR (Eucl P)) f
        (fun l => fderiv ℝ (g l)) hf hg' hfb
        (fun i ε hε => by
          filter_upwards [hgs (i + 1) ε hε] with l hl x hx
          rw [norm_iteratedFDeriv_fderiv]
          exact hl x hx) (ε / 2) (half_pos hε)
      have h2 := ih (Eucl P →L[ℝ] F₁) F₂ (Eucl P →L[ℝ] G) (B.precompL (Eucl P)) (fderiv ℝ f) g
        hf' hg (fun i => by
          obtain ⟨C, hC⟩ := hfb (i + 1)
          exact ⟨C, fun x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hC x hx⟩)
        hgs (ε / 2) (half_pos hε)
      filter_upwards [h1, h2] with l hl1 hl2 x hx
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => B.precompR (Eucl P) (f y) (fderiv ℝ (g l) y)) :=
        (B.precompR (Eucl P)).isBoundedBilinearMap.contDiff.comp (hf.prodMk (hg' l))
      have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => B.precompL (Eucl P) (fderiv ℝ f y) (g l y)) :=
        (B.precompL (Eucl P)).isBoundedBilinearMap.contDiff.comp (hf'.prodMk (hg l))
      rw [← norm_iteratedFDeriv_fderiv, hD l,
        fun_iteratedFDeriv_add_apply (hc1.contDiffAt.of_le (mod_cast le_top))
          (hc2.contDiffAt.of_le (mod_cast le_top))]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add (hl1 x hx) (hl2 x hx)
        _ = ε := add_halves ε
  -- Every derivative of the cut-off is bounded.
  have hζb : ∀ i, ∃ C, ∀ x ∈ tsupport ζ, ‖iteratedFDeriv ℝ i ζ x‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ :=
      (hζ.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
        (hζc.iteratedFDeriv i)
    exact ⟨C, fun x _ => hC x⟩
  have hfun : ∀ l, (φs l : DifferentialForm (Eucl P) k) =
      fun y => ContinuousLinearMap.lsmul ℝ ℝ (ζ y) (ψs l y) := fun l => funext fun y => by
    simp only [hφ l y, ContinuousLinearMap.lsmul_apply]
  refine ⟨tsupport ζ, hζc.isCompact, hζU, fun l => ?_, ?_, fun j => ?_⟩
  · rw [funext (hφ l)]
    exact tsupport_smul_subset_left _ _
  · simp
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [key j ℝ (Covector (Eucl P) k) (Covector (Eucl P) k)
      (ContinuousLinearMap.lsmul ℝ ℝ) ζ ψs hζ hψ hζb hsmall (ε / 2) (half_pos hε)] with l hl x hx
    rw [hfun l]
    simp only [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left]
    exact (hl x hx).trans_lt (half_lt_self hε)

/-- **The cut-off radial operator** behind the cone `h#([[(0,1)]] × T)`, `h(t, x) = t x`
(Simon Ch. 6, 2.30), with `h#` taken through a cut-off `ζ` as in 2.23.  Choose `ψ_ω` as in (H)
for each `ω ∈ 𝒟ᵐ⁺¹(ℝ^P)`; by (i), `ω ↦ ψ_ω` is linear.  For `r₀ = max r 0` and a bump `ζ` with
`ζ = 1` on `B̄_{r₀+1}(0)` and `spt ζ = B̄_{r₀+2}(0)`, `Φ(ω) = ζ ψ_ω` is a linear map
`𝒟ᵐ⁺¹(ℝ^P) → 𝒟ᵐ(ℝ^P)` agreeing with `ψ_ω` on `B_r(0)`.  If `ω_l → 0`, then for `i ≤ j`
eventually `‖Dⁱω_l‖ ≤ ε / (r₀ + 2 + j)` on all of `ℝ^P`, so (iii) gives `‖Dʲψ_{ω_l}‖ ≤ ε` on
`spt ζ`, and `iwl_cr_ce_cutoff_converges_zero` yields `Φ(ω_l) → 0`. -/
theorem Submission.iwl_cr_ce_cutoff_radial_operator : ∀ (P m : ℕ) (r : ℝ), (∀ ω : DifferentialForm (Eucl P) (m + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∃ ψ : DifferentialForm (Eucl P) m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ (x : Eucl P) (v : Fin m → Eucl P), ψ x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) ∧ ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D) → ∃ Φ : TestFormOn (univ : Set (Eucl P)) (m + 1) →ₗ[ℝ] TestFormOn (univ : Set (Eucl P)) m, (∀ ωs : ℕ → TestFormOn (univ : Set (Eucl P)) (m + 1), TestFormOnConverges ωs 0 → TestFormOnConverges (fun l => Φ (ωs l)) 0) ∧ ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P), x ∈ ball (0 : Eucl P) r → ∀ v : Fin m → Eucl P, (Φ ω : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v) := by
  intro P m r H
  -- Step 1: choose `ψ_ω` for every test form `ω` (test forms are `C^∞`).
  have hsmooth : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) (m + 1)) :=
    fun ω => ω.2.1.1
  choose ψ hψsmooth hψformula hψbound using
    fun ω : TestFormOn (univ : Set (Eucl P)) (m + 1) => H ω (hsmooth ω)
  -- Step 2: the integrands `t ↦ tᵐ ω(t x)(w)` are continuous, hence interval integrable.
  have hint : ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P)
      (w : Fin (m + 1) → Eucl P), IntervalIntegrable
        (fun t : ℝ => t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) w) volume 0 1 := by
    intro ω x w
    apply Continuous.intervalIntegrable
    exact (continuous_pow m).mul ((continuous_eval_const w).comp
      ((hsmooth ω).continuous.comp (continuous_id.smul continuous_const)))
  -- Step 3: by (i) and linearity of the integral, `ω ↦ ψ_ω` is linear.
  have hadd : ∀ ω ω' : TestFormOn (univ : Set (Eucl P)) (m + 1), ψ (ω + ω') = ψ ω + ψ ω' := by
    intro ω ω'
    funext x
    ext v
    rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, hψformula, hψformula, hψformula,
      ← intervalIntegral.integral_add (hint ω x _) (hint ω' x _)]
    congr 1
    funext t
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add]
  have hsmul : ∀ (c : ℝ) (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)),
      ψ (c • ω) = c • ψ ω := by
    intro c ω
    funext x
    ext v
    rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, hψformula, hψformula, smul_eq_mul,
      ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  -- Step 4: a bump `ζ` with `ζ = 1` on `B̄_{r₀+1}(0)` and `tsupport ζ = B̄_{r₀+2}(0)`.
  set r₀ := max r 0
  have hr₀ : 0 ≤ r₀ := le_max_right r 0
  let ζ : ContDiffBump (0 : Eucl P) := ⟨r₀ + 1, r₀ + 2, by linarith, by linarith⟩
  have hζsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ζ : Eucl P → ℝ) := ζ.contDiff
  have hζcpt : HasCompactSupport (ζ : Eucl P → ℝ) := ζ.hasCompactSupport
  -- Step 5: `Φ(ω) = ζ ψ_ω` is a test form, and `Φ` is linear by step 3.
  have hmem : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      (fun x => ζ x • ψ ω x) ∈ TestFormOn (univ : Set (Eucl P)) m := fun ω =>
    ⟨⟨hζsmooth.smul (hψsmooth ω), hζcpt.smul_right⟩, subset_univ _⟩
  let Φ : TestFormOn (univ : Set (Eucl P)) (m + 1) →ₗ[ℝ] TestFormOn (univ : Set (Eucl P)) m :=
    { toFun := fun ω => ⟨fun x => ζ x • ψ ω x, hmem ω⟩
      map_add' := by
        intro ω ω'
        apply Subtype.ext
        funext x
        simp only [hadd, Pi.add_apply, smul_add, AddMemClass.mk_add_mk]
      map_smul' := by
        intro c ω
        apply Subtype.ext
        funext x
        simp only [hsmul, Pi.smul_apply, smul_comm (ζ x) c, RingHom.id_apply,
          SetLike.mk_smul_mk] }
  refine ⟨Φ, ?_, ?_⟩
  -- Steps 7–11, property (a): `iwl_cr_ce_cutoff_converges_zero` with `ψ_l = ψ_{ω_l}`.
  · intro ωs hωs
    refine Submission.iwl_cr_ce_cutoff_converges_zero P m univ ζ (fun l => ψ (ωs l))
      (fun l => Φ (ωs l)) hζsmooth hζcpt (subset_univ _) (fun l => hψsmooth _) (fun l x => rfl) ?_
    intro j ε hε
    obtain ⟨K, -, -, hsupp, -, hconv⟩ := hωs
    have hpos : 0 < r₀ + 2 + j := by positivity
    set D := ε / (r₀ + 2 + j) with hDdef
    have hD : 0 < D := div_pos hε hpos
    -- Step 9: eventually `‖Dⁱω_l‖ ≤ D` on all of `ℝ^P` for every `i ≤ j`: on `K` by uniform
    -- convergence to `Dⁱ0 = 0`, and off `K ⊇ tsupport ω_l` because `Dⁱω_l` vanishes there.
    have hsmall : ∀ᶠ l in atTop, ∀ i ∈ Finset.range (j + 1), ∀ y,
        ‖iteratedFDeriv ℝ i (ωs l : DifferentialForm (Eucl P) (m + 1)) y‖ ≤ D := by
      rw [Filter.eventually_all_finset]
      intro i _
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconv i) D hD] with l hl y
      by_cases hy : y ∈ K
      · have h1 := hl y hy
        simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply,
          dist_zero_left] at h1
        exact h1.le
      · have h0 : iteratedFDeriv ℝ i (ωs l : DifferentialForm (Eucl P) (m + 1)) y = 0 :=
          image_eq_zero_of_notMem_tsupport fun h =>
            hy (hsupp l (tsupport_iteratedFDeriv_subset i h))
        rw [h0, norm_zero]
        exact hD.le
    -- Step 10: (iii) with `R = r₀ + 2` bounds `‖Dʲψ_{ω_l}‖` by `(r₀ + 2 + j) D = ε` on
    -- `tsupport ζ = B̄_{r₀+2}(0)`.
    filter_upwards [hsmall] with l hl x hx
    rw [ζ.tsupport_eq] at hx
    calc ‖iteratedFDeriv ℝ j (ψ (ωs l)) x‖ ≤ (r₀ + 2 + j) * D :=
          hψbound (ωs l) j (r₀ + 2) D hD.le
            (fun i hi y _ => hl i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) y) x hx
      _ = ε := by rw [hDdef]; exact mul_div_cancel₀ ε hpos.ne'
  -- Step 6, property (b): `ζ = 1` on `B_r(0) ⊆ B̄_{r₀+1}(0)`, so `Φ(ω) = ψ_ω` there; use (i).
  · intro ω x hx v
    have hx' : x ∈ closedBall (0 : Eucl P) ζ.rIn := by
      rw [mem_closedBall, dist_zero_right]
      rw [mem_ball, dist_zero_right] at hx
      change ‖x‖ ≤ r₀ + 1
      have : r ≤ r₀ := le_max_left r 0
      linarith
    change (ζ x • ψ ω x) v = _
    rw [ζ.one_of_mem_closedBall hx', one_smul, hψformula]
/-- **Radial coefficient bound** (for the cone mass estimate, Simon Ch. 6, 2.27 and 2.30,
pp. 140–141, in the proof of 8.2, p. 177).  If `|ω(y)| ≤ 1` for all `y` and
`β(v) = ∫₀¹ tᵐ ω(tx)(x, v) dt` for all `v`, then `|β| ≤ P^{2m+1} |x|`, `|·|` the Euclidean
coefficient norm of Remark 2.6.  Put `K = P^{m+1} |x|`.  If `|u_i| ≤ 1` for all `i`, then
`α(x, u) = |x| α(x/|x|, u)`, so `|α(x, u)| ≤ K |α|` by `isoperimetric_abs_covector_apply_le`.
Hence `|β(e_I)| ≤ K` for each of the `P^m` maps `I : Fin m → Fin P`, and
`|β| ≤ (P^m K²)^{1/2} ≤ P^m K = P^{2m+1} |x|`. -/
theorem Submission.iwl_cr_cest_radial_coeff_bound : ∀ (P m : ℕ) (ω : DifferentialForm (Eucl P) (m + 1)) (x : Eucl P) (β : Covector (Eucl P) m), (∀ y, covectorEuclideanNorm (ω y) ≤ 1) → (∀ v : Fin m → Eucl P, β v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) → covectorEuclideanNorm β ≤ (P : ℝ) ^ (2 * m + 1) * ‖x‖ := by
  intro P m ω x β hω hβ
  classical
  set K : ℝ := (P : ℝ) ^ (m + 1) * ‖x‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (pow_nonneg (Nat.cast_nonneg P) _) (norm_nonneg x)
  -- Step 1: `|α(x, u)| ≤ K |α|` whenever `|u_i| ≤ 1` for all `i`.
  have hcoef : ∀ (α : Covector (Eucl P) (m + 1)) (u : Fin m → Eucl P), (∀ i, ‖u i‖ ≤ 1) →
      |α (Fin.cons x u)| ≤ K * covectorEuclideanNorm α := by
    intro α u hu
    by_cases hx : x = 0
    · -- The first argument vanishes.
      have h0 : α (Fin.cons x u) = 0 := α.map_coord_zero 0 (by simp [hx])
      rw [h0, abs_zero]
      exact mul_nonneg hK0 (covectorEuclideanNorm_nonneg α)
    · -- `α(x, u) = |x| α(τ)` for `τ = (x/|x|, u)`, whose entries have norm at most `1`.
      have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set τ : Fin (m + 1) → Eucl P := Fin.cons (‖x‖⁻¹ • x) u
      have hτ : ∀ j, ‖τ j‖ ≤ 1 := by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [τ, norm_smul, inv_mul_cancel₀ hx0.ne']
        · simpa [τ] using hu i
      have hxu : (Fin.cons x u : Fin (m + 1) → Eucl P) = Function.update τ 0 (‖x‖ • τ 0) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [τ, smul_smul, mul_inv_cancel₀ hx0.ne']
        · simp [τ]
      rw [hxu, α.map_update_smul, Function.update_eq_self, smul_eq_mul, abs_mul,
        abs_of_pos hx0]
      calc ‖x‖ * |α τ| ≤ ‖x‖ * ((P : ℝ) ^ (m + 1) * covectorEuclideanNorm α) :=
            mul_le_mul_of_nonneg_left
              (Submission.isoperimetric_abs_covector_apply_le P (m + 1) α τ hτ) hx0.le
        _ = K * covectorEuclideanNorm α := by rw [hK]; ring
  -- Step 2: `|β(e_I)| ≤ K` for every `I : Fin m → Fin P`.
  have hcoord : ∀ I : Fin m → Fin P,
      |β (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ K := by
    intro I
    have he : ∀ i, ‖EuclideanSpace.basisFun (Fin P) ℝ (I i)‖ ≤ 1 := fun i =>
      ((EuclideanSpace.basisFun (Fin P) ℝ).orthonormal.1 (I i)).le
    -- On `Ι(0, 1) = (0, 1]`, `0 ≤ tᵐ ≤ 1` and `|ω(tx)(x, e_I)| ≤ K |ω(tx)| ≤ K`.
    have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖t ^ m * ω (t • x) (Fin.cons x fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))‖ ≤ K := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have htm : 0 ≤ t ^ m := pow_nonneg ht.1.le m
      have htm1 : t ^ m ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have hval := (hcoef (ω (t • x)) _ he).trans
        (mul_le_of_le_one_right hK0 (hω (t • x)))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htm]
      exact (mul_le_of_le_one_left (abs_nonneg _) htm1).trans hval
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h
    rw [hβ]
    exact h
  -- Step 3: `|β|² ≤ P^m K² ≤ (P^m K)²`, as `P^m ≤ (P^m)²`.
  unfold covectorEuclideanNorm
  refine (Real.sqrt_le_sqrt (y := ((P : ℝ) ^ m * K) ^ 2) ?_).trans_eq ?_
  · calc _ ≤ ∑ _I : Fin m → Fin P, K ^ 2 := by
          refine Finset.sum_le_sum fun I _ => ?_
          split_ifs
          · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord I) 2
          · positivity
      _ = (P : ℝ) ^ m * K ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      _ ≤ ((P : ℝ) ^ m) ^ 2 * K ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg K)
          exact_mod_cast Nat.le_self_pow two_ne_zero (P ^ m)
      _ = ((P : ℝ) ^ m * K) ^ 2 := (mul_pow _ _ 2).symm
  · rw [Real.sqrt_sq (mul_nonneg (pow_nonneg (Nat.cast_nonneg P) m) hK0), hK]
    ring

/-- **Cut-off radial form** (cone construction, Simon Ch. 6, 2.30–2.32 (pp. 141–142), as used in
the proof of 8.2).  Let `ψ₀(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt` be smooth and `0 < r < s`.  For the
bump function `ζ` equal to `1` on `B̄_r(0)` with support `B_s(0)`, `ψ = ζ ψ₀` is a test form
agreeing with `ψ₀` on `B_r(0)`.  If `|ω| ≤ 1`, then `|ψ(x)| = ζ(x) |ψ₀(x)|`, which is at most
`P^{2m+1} ‖x‖ ≤ P^{2m+1} s` for `‖x‖ < s` and `0` otherwise. -/
theorem Submission.iwl_cr_cest_cutoff_radial_form : ∀ (P m : ℕ) (ω : DifferentialForm (Eucl P) (m + 1)) (ψ₀ : DifferentialForm (Eucl P) m) (r s : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀ → (∀ (x : Eucl P) (v : Fin m → Eucl P), ψ₀ x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) → 0 < r → r < s → ∃ ψ : TestFormOn (univ : Set (Eucl P)) m, (∀ x ∈ ball (0 : Eucl P) r, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) ∧ ((∀ y, covectorEuclideanNorm (ω y) ≤ 1) → ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) m) x) ≤ (P : ℝ) ^ (2 * m + 1) * s) := by
  intro P m ω ψ₀ r s hψ₀ hrad hr hrs
  -- Step 1: the bump function `ζ = 1` on `B̄_r(0)`, `support ζ = B_s(0)`, `0 ≤ ζ ≤ 1`.
  obtain ⟨ζ, hζr, hζs⟩ : ∃ ζ : ContDiffBump (0 : Eucl P), ζ.rIn = r ∧ ζ.rOut = s :=
    ⟨⟨r, s, hr, hrs⟩, rfl, rfl⟩
  -- Step 2: `ζ ψ₀` is smooth with compact support, i.e. a test form on `ℝ^P`.
  have hmem : (ζ : Eucl P → ℝ) • ψ₀ ∈ testFormOnSubmodule (univ : Set (Eucl P)) m :=
    ⟨⟨ζ.contDiff.smul hψ₀, ζ.hasCompactSupport.smul_right⟩, subset_univ _⟩
  refine ⟨⟨(ζ : Eucl P → ℝ) • ψ₀, hmem⟩, fun x hx v => ?_, fun hω x => ?_⟩
  -- Step 3: `ζ = 1` on `B_r(0)`, so there `ψ = ψ₀` satisfies the radial formula.
  · have hζx : ζ x = 1 := ζ.one_of_mem_closedBall (by rw [hζr]; exact ball_subset_closedBall hx)
    change ((ζ : Eucl P → ℝ) • ψ₀) x v = _
    rw [Pi.smul_apply', ContinuousAlternatingMap.smul_apply, hζx, one_smul, hrad]
  -- Step 4: homogeneity `|a α| = |a| |α|` of the Euclidean coefficient norm.
  · have hsmul : ∀ (a : ℝ) (α : Covector (Eucl P) m),
        covectorEuclideanNorm (a • α) = |a| * covectorEuclideanNorm α := by
      intro a α
      unfold covectorEuclideanNorm
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    -- Step 5: `|ψ(x)| = ζ(x) |ψ₀(x)|`; bound it on `B_s(0)` and note it vanishes outside.
    change covectorEuclideanNorm (((ζ : Eucl P → ℝ) • ψ₀) x) ≤ _
    rw [Pi.smul_apply', hsmul, abs_of_nonneg ζ.nonneg]
    have hc : 0 ≤ (P : ℝ) ^ (2 * m + 1) := pow_nonneg (Nat.cast_nonneg P) _
    by_cases hxs : ‖x‖ < s
    · have hψ₀x : covectorEuclideanNorm (ψ₀ x) ≤ (P : ℝ) ^ (2 * m + 1) * ‖x‖ :=
        Submission.iwl_cr_cest_radial_coeff_bound P m ω x (ψ₀ x) hω (hrad x)
      calc ζ x * covectorEuclideanNorm (ψ₀ x) ≤ 1 * ((P : ℝ) ^ (2 * m + 1) * ‖x‖) :=
            mul_le_mul ζ.le_one hψ₀x (covectorEuclideanNorm_nonneg _) zero_le_one
        _ ≤ (P : ℝ) ^ (2 * m + 1) * s := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left hxs.le hc
    · have hζx : ζ x = 0 := by
        rw [← Function.notMem_support, ζ.support_eq, hζs, mem_ball_zero_iff]
        exact hxs
      rw [hζx, zero_mul]
      exact mul_nonneg hc (hr.trans hrs).le
/-- **Support of the cone** (the cone `0 ⨯ X` of Simon Ch. 6, 2.30, p. 141).  Suppose
`spt X ⊆ B̄_R(0)` and `C(ω) = X(ψ)` whenever `ψ` agrees on an open neighbourhood of `spt X` with
the radial form `x ↦ ∫_0^1 t^m ω(tx)(x, ·) dt`.  Then `spt C ⊆ B̄_R(0)`: for `‖p‖ > R` and
`r = (‖p‖ − R)/2`, a test form `ω` supported in `B_r(p)` vanishes at `tx` for `x ∈ B_{R+r}(0)`,
`t ∈ [0, 1]`, so `ψ = 0` is admissible and `C(ω) = X(0) = 0`; thus `C` vanishes on `B_r(p)`
and `p ∉ spt C`. -/
theorem Submission.iwl_cr_cest_cone_support : ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → C.support ⊆ closedBall 0 R := by
  intro P m R X C hX hcone p hp
  -- Suppose `‖p‖ > R` and put `r = (‖p‖ - R) / 2 > 0`.
  by_contra hpR
  rw [mem_closedBall_zero_iff, not_le] at hpR
  set r := (‖p‖ - R) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  -- `C` vanishes on `B_r(p)`: for `tsupport ω ⊆ B_r(p)`, `ψ = 0` satisfies the radial formula
  -- on `N = B_{R+r}(0) ⊇ spt X`, so `C ω = X 0 = 0`.
  have hvan : C.VanishesOn (ball p r) := by
    intro ω hω
    have hC := hcone ω 0
      ⟨ball 0 (R + r), isOpen_ball, hX.trans (closedBall_subset_ball (by linarith)), ?_⟩
    · rw [hC, map_zero]
    intro x hx v
    have hx' : ‖x‖ < R + r := mem_ball_zero_iff.mp hx
    -- For `t ∈ [0, 1]`, `‖tx‖ ≤ ‖x‖ < R + r = ‖p‖ - r`, so `tx ∉ B_r(p) ⊇ tsupport ω`.
    have hzero : EqOn (fun t : ℝ =>
        t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v))
        (fun _ => 0) (uIcc 0 1) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have htx : t • x ∉ tsupport (ω : DifferentialForm (Eucl P) (m + 1)) := by
        intro hmem
        have h1 : dist (t • x) p < r := hω hmem
        rw [dist_eq_norm] at h1
        have h2 : ‖t • x‖ ≤ ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2
        have h3 : ‖p‖ ≤ ‖t • x‖ + ‖t • x - p‖ := by
          have h4 := norm_le_insert' p (t • x)
          rwa [norm_sub_rev] at h4
        linarith
      simp only [image_eq_zero_of_notMem_tsupport htx, ContinuousAlternatingMap.coe_zero,
        Pi.zero_apply, mul_zero]
    simp only [Submodule.coe_zero, Pi.zero_apply, ContinuousAlternatingMap.coe_zero]
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
  -- Hence `B_r(p)` lies in the zero region of `C`, contradicting `p ∈ spt C`.
  exact hp.2 ⟨ball p r, ⟨isOpen_ball, by rw [closure_ball p hr.ne']; exact isCompact_closedBall p r,
    subset_univ _, hvan⟩, mem_ball_self hr⟩
/-- Mass comparison through bounded transfer forms: if for every mass-admissible `ω` and `δ > 0`
there is a test form `ψ` with `C(ω) = X(ψ)` and `|ψ(x)| ≤ c (R + δ)` everywhere, then
`M(C) ≤ c R · M(X)`. -/
theorem Submission.iwl_cr_cest_mass_le_of_forms :
    ∀ (P n k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) n)
      (C : GeometricCurrentOn (univ : Set (Eucl P)) k) (c R : ℝ), 0 ≤ c → 0 ≤ R → X.mass < ∞ →
      (∀ ω ∈ massAdmissibleOn (univ : Set (Eucl P)) k univ, ∀ δ : ℝ, 0 < δ →
        ∃ ψ : TestFormOn (univ : Set (Eucl P)) n, C ω = X ψ ∧
          ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) n) x) ≤ c * (R + δ)) →
      C.mass ≤ ENNReal.ofReal (c * R) * X.mass := by
  intro P n k X C c R hc hR hX hforms
  -- `M(X) = ofReal B` with `B = M(X).toReal ≥ 0`.
  set B := X.mass.toReal
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hXB : X.mass = ENNReal.ofReal B := (ENNReal.ofReal_toReal hX.ne).symm
  -- Every admissible `ω` has `C(ω) ≤ c R B`: use the transfer form for `δ = ε / (B c + 1)`.
  have key : ∀ ω ∈ massAdmissibleOn (univ : Set (Eucl P)) k univ, C ω ≤ c * R * B := by
    intro ω hω
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hBc : 0 ≤ B * c := mul_nonneg hB hc
    have hBc1 : 0 < B * c + 1 := by linarith
    have hδ : 0 < ε / (B * c + 1) := div_pos hε hBc1
    obtain ⟨ψ, hCψ, hψ⟩ := hforms ω hω (ε / (B * c + 1)) hδ
    have habs := Submission.cmb_abs_apply_le_of_massOn_le P n univ univ X ψ B
      (c * (R + ε / (B * c + 1))) hB hXB.le (subset_univ _) hψ
    have hBcδ : B * c * (ε / (B * c + 1)) < ε := by
      have e : B * c * (ε / (B * c + 1)) + ε / (B * c + 1) = ε := by field_simp
      linarith
    calc C ω = X ψ := hCψ
      _ ≤ |X ψ| := le_abs_self _
      _ ≤ B * (c * (R + ε / (B * c + 1))) := habs
      _ = c * R * B + B * c * (ε / (B * c + 1)) := by ring
      _ < c * R * B + ε := by linarith
  -- Take the supremum over admissible `ω`.
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (C ω) ≤ ENNReal.ofReal (c * R * B) :=
        ENNReal.ofReal_le_ofReal (key ω hω)
    _ = ENNReal.ofReal (c * R) * ENNReal.ofReal B := ENNReal.ofReal_mul (mul_nonneg hc hR)
    _ = ENNReal.ofReal (c * R) * X.mass := by rw [hXB]
/-- Smoothness of a parametric interval integral, with all derivatives under the integral sign:
for `G : ℝ × ℝ^P → V` of class `C^∞` (`V` complete), `g x = ∫_a^b G(t, x) dt` is `C^∞`, every
`x`-derivative `(t, x) ↦ ∂_x^j G(t, x)` is continuous, and `D^j g(x) = ∫_a^b ∂_x^j G(t, x) dt`.

Proof.  For smooth `H : ℝ × ℝ^P → W` the `x`-derivative `H'(t, x) = DH(t, x) ∘ inr` is smooth with
values in the complete space `ℝ^P →L W`.  Bounding `‖H'‖` on the compact set
`[[a, b]] × closedBall x₀ 1` and differentiating under the integral sign gives
`D(∫_a^b H(t, ·) dt) = ∫_a^b H'(t, ·) dt`.  Induction on `j`, over all complete codomains at once,
identifies `D^{j+1}` with `D^j ∘ D` through the currying isometry, which commutes with the
interval integral; `C^j` for every `j` is `C^∞`. -/
theorem Submission.iwl_cr_ro_intervalIntegral_contDiff :
    ∀ (P : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (G : ℝ × Eucl P → V) (a b : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl P => ∫ t in a..b, G (t, x)) ∧ (∀ j : ℕ, Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => G (p.1, z)) p.2)) ∧ ∀ (j : ℕ) (x : Eucl P), iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, G (t, y)) x = ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => G (t, z)) x := by
  intro P V _ _ _ G a b hG
  -- The partial derivative of a smooth `H` in `x` is `H'(t, x) = DH(t, x) ∘ inr` (chain rule).
  have hderiv : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (H : ℝ × Eucl P → W),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ (t : ℝ) (x : Eucl P),
      HasFDerivAt (fun z : Eucl P => H (t, z))
        ((fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x := by
    intro W _ _ H hH t x
    exact (hH.differentiable (by simp) (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- One differentiation under the integral sign: `‖H'‖ ≤ K` on `[[a, b]] × closedBall x₀ 1`.
  have hstep : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ x₀ : Eucl P,
      HasFDerivAt (fun x : Eucl P => ∫ t in a..b, H (t, x))
        (∫ t in a..b, (fderiv ℝ H (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x₀ := by
    intro W _ _ _ H hH x₀
    have hHc : Continuous H := hH.continuous
    have hH'c : Continuous fun p : ℝ × Eucl P =>
        (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) :=
      (hH.continuous_fderiv (by simp)).clm_comp continuous_const
    obtain ⟨K, hK⟩ := (isCompact_uIcc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      hH'c.continuousOn
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => H (t, x))
      (F' := fun x t => (fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)))
      (bound := fun _ => K) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x =>
        (hHc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      ((hHc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hH'c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx =>
        hK (t, x) ⟨uIoc_subset_uIcc ht, ball_subset_closedBall hx⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun t x _ => hderiv W H hH t x)
  -- Induction on `j` over all complete codomains: `C^j`, continuity of `∂_x^j H`, and
  -- `D^j (∫_a^b H(t, ·) dt) = ∫_a^b ∂_x^j H(t, ·) dt`.
  have claim : ∀ j : ℕ, ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H →
      ContDiff ℝ j (fun x : Eucl P => ∫ t in a..b, H (t, x)) ∧
      Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => H (p.1, z)) p.2) ∧
      ∀ x : Eucl P, iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, H (t, y)) x =
        ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => H (t, z)) x := by
    intro j
    induction j with
    | zero =>
      intro W _ _ _ H hH
      have hHc : Continuous H := hH.continuous
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_zero, contDiff_zero]
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun x t => H (t, x)) (hHc.comp continuous_swap) a b
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
        exact (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.continuous.comp hHc
      · intro x
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact (LinearIsometry.intervalIntegral_comp_comm
          (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.toLinearIsometry
          (fun t => H (t, x))).symm
    | succ j ih =>
      intro W _ _ _ H hH
      set H' : ℝ × Eucl P → (Eucl P →L[ℝ] W) :=
        fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) with hH'
      have hH'smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H' :=
        (hH.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_comp contDiff_const
      obtain ⟨ih1, ih2, ih3⟩ := ih (Eucl P →L[ℝ] W) H' hH'smooth
      have hg : fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) =
          fun x => ∫ t in a..b, H' (t, x) := by
        funext x
        exact (hstep W H hH x).fderiv
      have hgd : Differentiable ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) :=
        fun x => (hstep W H hH x).differentiableAt
      have hpart : ∀ t : ℝ, fderiv ℝ (fun z : Eucl P => H (t, z)) = fun z => H' (t, z) :=
        fun t => funext fun z => (hderiv W H hH t z).fderiv
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
        refine ⟨hgd, fun h => absurd h (by simp), ?_⟩
        rw [hg]
        exact ih1
      · have : (fun p : ℝ × Eucl P => iteratedFDeriv ℝ (j + 1) (fun z : Eucl P => H (p.1, z)) p.2) =
            fun p => (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm
              (iteratedFDeriv ℝ j (fun z : Eucl P => H' (p.1, z)) p.2) := by
          funext p
          rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
          congr 2
          exact hpart p.1
        rw [this]
        exact (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm.continuous.comp ih2
      · intro x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        have : (fun y => fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) y) =
            fun x => ∫ t in a..b, H' (t, x) := hg
        rw [this, ih3 x]
        have hint : IntervalIntegrable
            (fun t : ℝ => iteratedFDeriv ℝ j (fun z : Eucl P => H' (t, z)) x) volume a b :=
          (ih2.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
        have e := ContinuousLinearMap.intervalIntegral_comp_comm
          ((continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm :
            (Eucl P [×j]→L[ℝ] (Eucl P →L[ℝ] W)) →L[ℝ] (Eucl P [×(j + 1)]→L[ℝ] W)) hint
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe] at e
        rw [← e]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        congr 2
        exact (hpart t).symm
  exact ⟨contDiff_infty.2 fun n => (claim n V G hG).1,
    fun j => (claim j V G hG).2.1,
    fun j x => (claim j V G hG).2.2 x⟩
/-- Integrand of the radial homotopy operator.  For a `C^∞` `(k + 1)`-form `ω` and `a ∈ ℕ`, the map
`F(t, x) = tᵃ • (ω(t • x)).curryLeft x`, i.e. `F(t, x)(v) = tᵃ ω(tx)(x, v)`, is `C^∞` on
`ℝ × ℝ^P`, and for fixed `t` the derivative of `F(t, ·)` at `x` is
`w ↦ (v ↦ tᵃ (t Dω(tx)[w](x, v) + ω(tx)(w, v)))`, where `(y, v) = Fin.cons y v`. -/
theorem Submission.iwl_cr_ro_integrand_contDiff_fderiv :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) ∧
          ∀ (t : ℝ) (x w : Eucl P) (v : Fin k → Eucl P),
            fderiv ℝ (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x w v =
              t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v)) := by
  intro P k a ω hω
  -- The interior product `α ↦ α.curryLeft` as an (opaque) continuous linear map `B`.
  obtain ⟨B, hB⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      ∀ α, B α = α.curryLeft :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
        (n := k)).toContinuousLinearMap, fun α => rfl⟩
  refine ⟨?_, ?_⟩
  · -- `F(p) = p.1ᵃ • B (ω (p.1 • p.2)) p.2` is built from `C^∞` pieces.
    have hfun : (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) =
        fun p => p.1 ^ a • B (ω (p.1 • p.2)) p.2 := by
      funext p; rw [hB]
    rw [hfun]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    -- Naming the codomain `F` lets the normed instances on `Covector` be unified with `B`'s.
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => B (ω (p.1 • p.2))) := by
      exact (ContinuousLinearMap.contDiff (F := Eucl P →L[ℝ] Covector (Eucl P) k) B).comp
        (hω.comp hs)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × Eucl P => B (ω (p.1 • p.2)) p.2) :=
      h1.clm_apply contDiff_snd
    exact (contDiff_fst.pow a).smul h2
  · intro t x w v
    have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
        fun z => t ^ a • B (ω (t • z)) z := by
      funext z; rw [hB]
    rw [hfun]
    have hω' : HasFDerivAt ω (fderiv ℝ ω (t • x)) (t • x) :=
      (hω.differentiable (by simp) (t • x)).hasFDerivAt
    have hs : HasFDerivAt (fun z : Eucl P => t • z) (t • ContinuousLinearMap.id ℝ (Eucl P)) x :=
      (hasFDerivAt_id x).const_smul t
    -- Chain rule for `z ↦ B (ω (t • z))`.
    have hc : HasFDerivAt (fun z : Eucl P => B (ω (t • z)))
        (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))) x := by
      exact HasFDerivAt.comp (F := Covector (Eucl P) (k + 1))
        (G := Eucl P →L[ℝ] Covector (Eucl P) k) x
        (ContinuousLinearMap.hasFDerivAt (F := Eucl P →L[ℝ] Covector (Eucl P) k) B)
        (hω'.comp x hs)
    -- Product rule for `z ↦ B (ω (t • z)) z`, then scaling by `tᵃ`.
    have happ := hc.clm_apply (hasFDerivAt_id x)
    have hf : HasFDerivAt (fun z : Eucl P => t ^ a • B (ω (t • z)) z)
        (t ^ a • ((B (ω (t • x))).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
          (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))).flip x)) x :=
      happ.const_smul (t ^ a)
    -- Evaluate at `w` and `v`; `Matrix.vecCons` is definitionally `Fin.cons`.
    rw [hf.fderiv]
    simp only [_root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, hB,
      ContinuousAlternatingMap.curryLeft_apply_apply, map_smul, smul_eq_mul,
      ContinuousAlternatingMap.curryLeft_smul]
    rw [add_comm]
    rfl
/-- Bound on the `j`-th derivative of the radial-homotopy integrand: for `t ∈ [0, 1]` and
`‖x‖ ≤ R`, `‖D^j (z ↦ t^a • ι_z ω(t z))(x)‖ ≤ (R + j) D` when `‖D^i ω‖ ≤ D` on `closedBall 0 R`
for all `i ≤ j`.  Writing the integrand as `t^a • B (g z) z` with `g z = ω (t • z)` and `B` the
interior product (`‖B u v‖ ≤ ‖u‖ ‖v‖`), the Leibniz rule for `z ↦ B (g z) z`, proved below by
induction on the order, gives `‖D^j (B (g ·) ·)(x)‖ ≤ ‖x‖ ‖D^j g(x)‖ + j ‖D^(j-1) g(x)‖`, and
`‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` since `‖t x‖ ≤ R`. -/
theorem Submission.iwl_cr_ro_integrand_iteratedFDeriv_le :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
        (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R,
          ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤
            (R + j) * D := by
  intro P k a ω hω j R D hD hbound t ht x hx
  -- Leibniz bound for `z ↦ B (g z) z`.  Since `D (B (g ·) ·)(z) = B (g z) + B' (Dg z) z` with
  -- `B' A z h = B (A h) z`, again of the same shape, induction on the order gives
  -- `‖D^n (B (g ·) ·)(y)‖ ≤ ‖y‖ ‖D^n g(y)‖ + n ‖D^(n-1) g(y)‖`.
  have leibniz : ∀ (n : ℕ) (F G : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : F →L[ℝ] Eucl P →L[ℝ] G),
      (∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) →
      ∀ g : Eucl P → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ y : Eucl P,
        ‖iteratedFDeriv ℝ n (fun z => B (g z) z) y‖ ≤
          ‖y‖ * ‖iteratedFDeriv ℝ n g y‖ + n * ‖iteratedFDeriv ℝ (n - 1) g y‖ := by
    intro n
    induction n with
    | zero =>
      intro F G _ _ _ _ B hB g hg y
      rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, Nat.cast_zero, zero_mul, add_zero,
        mul_comm]
      exact hB (g y) y
    | succ n ih =>
      intro F G _ _ _ _ B hB g hg y
      obtain ⟨B', hB'apply, hB'bound⟩ :
          ∃ B' : (Eucl P →L[ℝ] F) →L[ℝ] Eucl P →L[ℝ] Eucl P →L[ℝ] G,
            (∀ A z h, B' A z h = B (A h) z) ∧ ∀ A z, ‖B' A z‖ ≤ ‖A‖ * ‖z‖ := by
        refine ⟨((ContinuousLinearMap.compL ℝ (Eucl P) F G).comp B.flip).flip,
          fun A z h => rfl, fun A z => ?_⟩
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        show ‖B (A h) z‖ ≤ ‖A‖ * ‖z‖ * ‖h‖
        calc ‖B (A h) z‖ ≤ ‖A h‖ * ‖z‖ := hB (A h) z
          _ ≤ ‖A‖ * ‖h‖ * ‖z‖ := by gcongr; exact A.le_opNorm h
          _ = ‖A‖ * ‖z‖ * ‖h‖ := by ring
      have hBnorm : ‖B‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [one_mul]
        exact hB u v
      have hgd : Differentiable ℝ g := (contDiff_infty_iff_fderiv.1 hg).1
      have hdg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
        (contDiff_infty_iff_fderiv.1 hg).2
      have hderiv : fderiv ℝ (fun z => B (g z) z) = fun z => B (g z) + B' (fderiv ℝ g z) z := by
        funext z
        have h1 : HasFDerivAt (fun z => B (g z)) (B.comp (fderiv ℝ g z)) z :=
          B.hasFDerivAt.comp z (hgd z).hasFDerivAt
        have h2 : HasFDerivAt (fun z => B (g z) z)
            ((B (g z)).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
              (B.comp (fderiv ℝ g z)).flip z) z :=
          h1.clm_apply (hasFDerivAt_id z)
        rw [h2.fderiv]
        ext h
        simp [hB'apply]
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B (g z)) := B.contDiff.comp hg
      have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B' (fderiv ℝ g z) z) :=
        B'.isBoundedBilinearMap.contDiff.comp (hdg.prodMk contDiff_id)
      have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
      have hadd : iteratedFDeriv ℝ n (fun z => B (g z) + B' (fderiv ℝ g z) z) y =
          iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y :=
        iteratedFDeriv_add_apply (hc1.contDiffAt.of_le hle) (hc2.contDiffAt.of_le hle)
      have hcomp : iteratedFDeriv ℝ n (fun z => B (g z)) y =
          B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y) :=
        B.iteratedFDeriv_comp_left hg.contDiffAt hle
      have e1 : ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ ≤ ‖iteratedFDeriv ℝ n g y‖ := by
        rw [hcomp]
        calc ‖B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y)‖
            ≤ ‖B‖ * ‖iteratedFDeriv ℝ n g y‖ := B.norm_compContinuousMultilinearMap_le _
          _ ≤ 1 * ‖iteratedFDeriv ℝ n g y‖ := by gcongr
          _ = ‖iteratedFDeriv ℝ n g y‖ := one_mul _
      have e2 := ih (Eucl P →L[ℝ] F) (Eucl P →L[ℝ] G) B' hB'bound (fderiv ℝ g) hdg y
      rw [norm_iteratedFDeriv_fderiv] at e2
      have e3 : (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) (fderiv ℝ g) y‖ =
          n * ‖iteratedFDeriv ℝ n g y‖ := by
        rcases n with _ | m
        · simp
        · rw [norm_iteratedFDeriv_fderiv, Nat.add_sub_cancel]
      rw [e3] at e2
      rw [← norm_iteratedFDeriv_fderiv, hderiv, hadd, Nat.add_sub_cancel]
      calc ‖iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖
          ≤ ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ +
            ‖iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ n g y‖ +
            (‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ + n * ‖iteratedFDeriv ℝ n g y‖) :=
              add_le_add e1 e2
        _ = ‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ +
            ((n + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ n g y‖ := by push_cast; ring
  -- The interior product `B α = α.curryLeft`, a linear isometry, so `‖B u v‖ ≤ ‖u‖ ‖v‖`.
  obtain ⟨B, hB, hBbound⟩ :
      ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] Eucl P →L[ℝ] Covector (Eucl P) k,
        (∀ α, B α = α.curryLeft) ∧ ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖ := by
    refine ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
      (n := k)).toContinuousLinearMap, fun α => rfl, fun u v => ?_⟩
    calc ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u v‖
        ≤ ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖u‖ * ‖v‖ := by
          rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hR : 0 ≤ R := (norm_nonneg x).trans hx'
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
      fun z => t ^ a • B (ω (t • z)) z := by
    funext z; rw [hB]
  rw [hfun]
  -- `g z = ω (L z)` with `L = t • id`, `‖L‖ ≤ 1`, so `‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` for `i ≤ j`.
  set L : Eucl P →L[ℝ] Eucl P := t • ContinuousLinearMap.id ℝ (Eucl P) with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖ContinuousLinearMap.id ℝ (Eucl P)‖ ≤ 1 * 1 :=
          mul_le_mul ht1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgfun : (fun z : Eucl P => ω (t • z)) = ω ∘ L := by
    funext z; simp [hL]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => ω (t • z)) := by
    rw [hgfun]; exact hω.comp L.contDiff
  have hgnorm : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ ≤ D := by
    intro i hi
    rw [hgfun, L.iteratedFDeriv_comp_right hω x (by exact_mod_cast le_top)]
    have hLx : L x ∈ closedBall (0 : Eucl P) R := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ 1 * R := mul_le_mul hLnorm hx' (norm_nonneg x) zero_le_one
        _ = R := one_mul R
    calc ‖(iteratedFDeriv ℝ i ω (L x)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ i ω (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ D * 1 := by
          apply mul_le_mul (hbound i hi _ hLx) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
      _ = D := mul_one D
  -- Pull out `t^a` (`0 ≤ t^a ≤ 1`) and apply the Leibniz bound.
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => B (ω (t • z)) z) :=
    B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)
  have hsmul : iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • B (ω (t • z)) z) x =
      t ^ a • iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x :=
    iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [hsmul, norm_smul]
  have hta : ‖t ^ a‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1
  have key := leibniz j _ _ B hBbound (fun z => ω (t • z)) hg x
  have hsum : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ +
      j * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ (R + j) * D := by
    have e1 : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ ≤ R * D :=
      mul_le_mul hx' (hgnorm j le_rfl) (norm_nonneg _) hR
    have e2 : (j : ℝ) * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ j * D :=
      mul_le_mul_of_nonneg_left (hgnorm (j - 1) (Nat.sub_le j 1)) (Nat.cast_nonneg j)
    linarith
  calc ‖t ^ a‖ * ‖iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x‖
      ≤ 1 * ((R + j) * D) := mul_le_mul hta (key.trans hsum) (norm_nonneg _) zero_le_one
    _ = (R + j) * D := one_mul _

/-- The radial homotopy operator `ψ(x) = ∫₀¹ tᵃ x ⌟ ω(t x) dt` (proof of Simon Ch. 6, 8.2,
Part I): for a smooth `(k + 1)`-form `ω`, `ψ` is a smooth `k`-form with
(i) `ψ(x)(v) = ∫₀¹ tᵃ ω(t x)(x, v) dt`,
(ii) `Dψ(x)[w](v) = ∫₀¹ tᵃ (t Dω(t x)[w](x, v) + ω(t x)(w, v)) dt`, and
(iii) `‖Dʲψ(x)‖ ≤ (R + j) D` on `B̄_R(0)` whenever `‖Dⁱω‖ ≤ D` there for all `i ≤ j`.
The integrand `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is jointly smooth, so `ψ = ∫₀¹ F(t, ·) dt`
is smooth with `Dʲψ = ∫₀¹ Dʲ_x F dt`; evaluation commutes with the integral. -/
theorem Submission.iwl_cr_radial_operator :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∃ ψ : DifferentialForm (Eucl P) k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
        (∀ (x : Eucl P) (v : Fin k → Eucl P),
          ψ x v = ∫ t in (0 : ℝ)..1, t ^ a * ω (t • x) (Fin.cons x v)) ∧
        (∀ (x w : Eucl P) (v : Fin k → Eucl P),
          fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1,
            t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v))) ∧
        ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
          (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
          ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D := by
  intro P k a ω hω
  -- `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is smooth; `ψ = ∫₀¹ F(t, ·) dt` and
  -- `Dʲψ(x) = ∫₀¹ Dʲ(F(t, ·))(x) dt`, with `(t, x) ↦ Dʲ(F(t, ·))(x)` continuous.
  obtain ⟨hGsmooth, hGderiv⟩ := Submission.iwl_cr_ro_integrand_contDiff_fderiv P k a ω hω
  obtain ⟨hψsmooth, hGcont, hψiter⟩ :=
    Submission.iwl_cr_ro_intervalIntegral_contDiff P (Covector (Eucl P) k) _ 0 1 hGsmooth
  dsimp only at hψsmooth hGcont hψiter
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, t ^ a • (ω (t • x)).curryLeft x, hψsmooth, ?_, ?_, ?_⟩
  · -- (i): evaluation at `v` is a continuous linear map, so it commutes with the integral.
    intro x v
    have hc : Continuous fun t : ℝ => t ^ a • (ω (t • x)).curryLeft x :=
      hGsmooth.continuous.comp (continuous_id.prodMk continuous_const)
    have e := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousAlternatingMap.apply_apply] at e
    beta_reduce
    rw [← e]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      smul_eq_mul]
    rfl
  · -- (ii): `Dψ(x)[w] = D¹ψ(x)(w)`; evaluate `∫₀¹ D¹(F(t, ·))(x) dt` at `w`, then at `v`.
    intro x w v
    have hc₁ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x :=
      (hGcont 1).comp (continuous_id.prodMk continuous_const)
    have hc₂ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x (fun _ => w) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
        (fun _ => w)).continuous.comp hc₁
    have e₁ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
      (fun _ => w)).intervalIntegral_comp_comm (hc₁.intervalIntegrable (μ := volume) 0 1)
    have e₂ := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc₂.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousMultilinearMap.apply_apply, ContinuousAlternatingMap.apply_apply] at e₁ e₂
    have e₀ : ∀ f : Eucl P → Covector (Eucl P) k,
        fderiv ℝ f x w = iteratedFDeriv ℝ 1 f x (fun _ => w) :=
      fun f => (iteratedFDeriv_one_apply (fun _ : Fin 1 => w)).symm
    rw [e₀, hψiter 1 x, ← e₁, ← e₂]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [iteratedFDeriv_one_apply]
    exact hGderiv t x w v
  · -- (iii): `‖Dʲψ(x)‖ ≤ ∫₀¹ ‖Dʲ(F(t, ·))(x)‖ dt ≤ (R + j) D`.
    intro j R D hD hω_le x hx
    rw [hψiter j x]
    have hle : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun z => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Submission.iwl_cr_ro_integrand_iteratedFDeriv_le P k a ω hω j R D hD hω_le t
        ⟨ht.1.le, ht.2⟩ x hx
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rwa [sub_zero, abs_one, mul_one] at h
/-- Pointwise integrand identity of the radial homotopy formula: for `L : E →L[ℝ] Λ^{k+1}(E)`,
`α ∈ Λ^{k+1}(E)`, `x ∈ E`, `u ∈ E^{k+1}`, `t ∈ ℝ` and `û_j = removeNth j u`,
`t^{k+1} Alt(L)(x, u) + ∑_j (-1)^j t^k (t L(u_j)(x, û_j) + α(u_j, û_j))
  = t^{k+1} L(x)(u) + (k + 1) t^k α(u)`.
Expanding `Alt(L)(x, u) = L(x)(u) - ∑_j (-1)^j L(u_j)(x, û_j)` cancels the `t^{k+1}` cross
terms, and `alternatizeUncurryFin (curryLeft α) = (k + 1) • α` evaluates the `α`-sum. -/
theorem Submission.iwl_cr_rh_integrand_identity :
    ∀ (P k : ℕ) (L : Eucl P →L[ℝ] Covector (Eucl P) (k + 1)) (α : Covector (Eucl P) (k + 1))
      (x : Eucl P) (u : Fin (k + 1) → Eucl P) (t : ℝ),
      t ^ (k + 1) * ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) +
          ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
            (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) +
              α (Fin.cons (u j) (Fin.removeNth j u)))) =
        t ^ (k + 1) * L x u + ((k : ℝ) + 1) * t ^ k * α u := by
  intro P k L α x u t
  -- `removeNth (j + 1) (x, u) = (x, removeNth j u)`.
  have hrem : ∀ j : Fin (k + 1),
      Fin.removeNth j.succ (Fin.cons x u : Fin (k + 2) → Eucl P) =
        Fin.cons x (Fin.removeNth j u) :=
    fun j => Fin.cons_comp_succ_succAbove x u j
  -- Split `Alt(L)(x, u)` into the index `0` and the indices `j.succ`.
  have hA : ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) =
      L x u - ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
        L (u j) (Fin.cons x (Fin.removeNth j u)) := by
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
      Fin.val_succ, Fin.cons_succ, hrem, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      pow_succ, mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  -- `∑_j (-1)^j α(u_j, û_j) = (k + 1) α(u)`: evaluate `Alt(curryLeft α) = (k + 1) • α` at `u`.
  have hB : ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * α (Fin.cons (u j) (Fin.removeNth j u)) =
      ((k : ℝ) + 1) * α u := by
    have h := congrArg (fun f => f u) (ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft α)
    simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.smul_apply,
      zsmul_eq_mul, nsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.cast_add,
      Nat.cast_one] at h
    exact h
  -- Distribute `(-1)^j t^k (t a_j + b_j) = t^{k+1} (-1)^j a_j + t^k (-1)^j b_j` over the sum.
  have hsum : ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
        (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) +
          α (Fin.cons (u j) (Fin.removeNth j u)))) =
      t ^ (k + 1) * ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
          L (u j) (Fin.cons x (Fin.removeNth j u)) +
        t ^ k * ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
          α (Fin.cons (u j) (Fin.removeNth j u)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hA, hsum, hB]
  ring

/-- Radial fundamental theorem of calculus: for a smooth form `φ`,
`∫₀¹ (t^(m+1) Dφ(t x)[x](u) + (m + 1) t^m φ(t x)(u)) dt = φ(x)(u)`, since the integrand is the
derivative of `g(t) = t^(m+1) φ(t x)(u)` and `g(1) - g(0) = φ(x)(u)`. -/
theorem Submission.iwl_cr_rh_radial_ftc :
    ∀ (P n m : ℕ) (φ : DifferentialForm (Eucl P) n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ (x : Eucl P) (u : Fin n → Eucl P),
        ∫ t in (0 : ℝ)..1, (t ^ (m + 1) * fderiv ℝ φ (t • x) x u +
          ((m : ℝ) + 1) * t ^ m * φ (t • x) u) = φ x u := by
  intro P n m φ hφ x u
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- `g(s) = s^(m+1) φ(s x)(u)` has the integrand as derivative at every `t`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s ^ (m + 1) * φ (s • x) u)
        (t ^ (m + 1) * fderiv ℝ φ (t • x) x u + ((m : ℝ) + 1) * t ^ m * φ (t • x) u) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => φ (s • x)) (fderiv ℝ φ (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun s : ℝ => φ (s • x) u) (fderiv ℝ φ (t • x) x u) t :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).hasFDerivAt.comp_hasDerivAt t h2
    refine ((hasDerivAt_pow (m + 1) t).fun_mul h3).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  -- The integrand is continuous, hence interval integrable.
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (m + 1) * fderiv ℝ φ (t • x) x u +
      ((m : ℝ) + 1) * t ^ m * φ (t • x) u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hc1 : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x u := by
      have : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x :=
        (hcont.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
      exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).continuous.comp this
    have hc2 : Continuous fun t : ℝ => φ (t • x) u :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).continuous.comp
        (hφ.continuous.comp (continuous_id.smul continuous_const))
    exact ((continuous_pow (m + 1)).mul hc1).add
      ((continuous_const.mul (continuous_pow m)).mul hc2)
  -- Fundamental theorem of calculus on `[0, 1]`: `g(1) - g(0) = φ(x)(u) - 0`.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- Radial homotopy formula in degree zero: if `χ(x)(v) = ∫₀¹ t⁰ dφ(t x)(x, v) dt` for a smooth
`0`-form `φ`, then `χ(x) = φ(x) - φ(0)` (fundamental theorem of calculus along `t ↦ t x`). -/
theorem Submission.iwl_cr_rh_degree_zero :
    ∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ (x : Eucl P) (v : Fin 0 → Eucl P),
        χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) →
      ∀ x, χ x = φ x - φ 0 := by
  intro P φ χ hφ hχ x
  ext v
  -- `dφ(t x)(x, v) = Dφ(t x)[x](v)`: the alternating sum has the single term `i = 0`.
  have hd : ∀ t : ℝ, extDeriv φ (t • x) (Fin.cons x v) = fderiv ℝ φ (t • x) x v := by
    intro t
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [hχ x v, ContinuousAlternatingMap.sub_apply]
  simp only [pow_zero, one_mul, hd]
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- `s ↦ φ(s x)(v)` has derivative `Dφ(t x)[x](v)` at every `t`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => φ (s • x) v) (fderiv ℝ φ (t • x) x v) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => φ (s • x)) (fderiv ℝ φ (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).hasFDerivAt.comp_hasDerivAt t h2
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ φ (t • x) x v) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x :=
      (hcont.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).continuous.comp this
  -- Fundamental theorem of calculus on `[0, 1]`.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **Radial homotopy formula on `ℝ^P`** (the form version of Simon Ch. 6, 2.25–2.26 and 2.31 for
the homotopy `(t, x) ↦ t x`, used by the cone construction in the proof of 8.2).
(a) If `φ` is a smooth `(k + 1)`-form, `Dψ(x)[w](v) = ∫₀¹ tᵏ (t Dφ(tx)[w](x, v) + φ(tx)(w, v)) dt`
and `χ(x)(v) = ∫₀¹ tᵏ⁺¹ dφ(tx)(x, v) dt`, then `χ + dψ = φ`, i.e. `H(dφ) + d(H′φ) = φ`.
(b) For a smooth `0`-form `φ`, `H(dφ)(x) = φ(x) − φ(0)`.

For (a), `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ)` with `ûⱼ = removeNth j u`.  All integrands are
continuous, so `χ(x)(u) + dψ(x)(u)` is a single integral over `[0, 1]`.  The cross terms cancel and
`∑ⱼ (-1)ʲ α(uⱼ, ûⱼ) = (k + 1) α(u)`, so its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`,
the derivative of `t ↦ tᵏ⁺¹ φ(tx)(u)`, whose integral over `[0, 1]` is `φ(x)(u)`. -/
theorem Submission.iwl_cr_radial_homotopy : (∀ (P k : ℕ) (φ : DifferentialForm (Eucl P) (k + 1)) (ψ : DifferentialForm (Eucl P) k) (χ : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x w : Eucl P) (v : Fin k → Eucl P), fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1, t ^ k * (t * fderiv ℝ φ (t • x) w (Fin.cons x v) + φ (t • x) (Fin.cons w v))) → (∀ (x : Eucl P) (v : Fin (k + 1) → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ (k + 1) * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x + extDeriv ψ x = φ x) ∧ (∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x : Eucl P) (v : Fin 0 → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x = φ x - φ 0) := by
  refine ⟨fun P k φ ψ χ hφ hψ hχ x => ?_, Submission.iwl_cr_rh_degree_zero⟩
  -- `φ`, `Dφ`, `dφ = alternatizeUncurryFinCLM ∘ Dφ` and `t ↦ t • x` are continuous.
  have hφc : Continuous φ := hφ.continuous
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hdφ : Continuous (extDeriv φ) :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp hDφ
  have hsx : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
  ext u
  -- The `j`-th integrand of `dψ(x)(u)` and the integrand of `χ(x)(u)` are continuous in `t`.
  have hg : ∀ j : Fin (k + 1), Continuous fun t : ℝ => t ^ k * (t * fderiv ℝ φ (t • x) (u j)
      (Fin.cons x (Fin.removeNth j u)) + φ (t • x) (Fin.cons (u j) (Fin.removeNth j u))) := by
    intro j
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (t • x) (u j) (Fin.cons x (Fin.removeNth j u)) :=
      ((hDφ.comp hsx).clm_apply continuous_const).eval_const _
    have h2 : Continuous fun t : ℝ => φ (t • x) (Fin.cons (u j) (Fin.removeNth j u)) :=
      (hφc.comp hsx).eval_const _
    exact (continuous_pow k).mul ((continuous_id.mul h1).add h2)
  have hf : Continuous fun t : ℝ => t ^ (k + 1) * extDeriv φ (t • x) (Fin.cons x u) :=
    (continuous_pow (k + 1)).mul ((hdφ.comp hsx).eval_const _)
  -- `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ) = ∑ⱼ (-1)ʲ ∫₀¹ tᵏ (t Dφ(tx)[uⱼ](x, ûⱼ) + φ(tx)(uⱼ, ûⱼ)) dt`.
  have hdψ : extDeriv ψ x u = ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
      ∫ t in (0 : ℝ)..1, t ^ k * (t * fderiv ℝ φ (t • x) (u j) (Fin.cons x (Fin.removeNth j u)) +
        φ (t • x) (Fin.cons (u j) (Fin.removeNth j u))) := by
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψ x (u j) (Fin.removeNth j u), zsmul_eq_mul]
    push_cast
    rfl
  rw [ContinuousAlternatingMap.add_apply, hχ x u, hdψ]
  -- Collect `χ(x)(u) + dψ(x)(u)` into a single integral over `[0, 1]`.
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun j _ => ((hg j).const_mul _).intervalIntegrable 0 1,
    ← intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
      ((continuous_finsetSum _ fun j _ => (hg j).const_mul _).intervalIntegrable 0 1)]
  -- Its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`, so the integral is `φ(x)(u)`.
  rw [← Submission.iwl_cr_rh_radial_ftc P (k + 1) k φ hφ x u]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact Submission.iwl_cr_rh_integrand_identity P k (fderiv ℝ φ (t • x)) (φ (t • x)) x u t

/-- Supports of boundaries, weak limits and linear combinations: `spt ∂Z ⊆ spt Z`; a weak limit of
currents supported in a closed `K` is supported in `K`; `spt Z ⊆ spt Z₁ ∪ spt Z₂` when
`Z = a Z₁ + b Z₂`.  In each case a point outside the claimed support lies in an open `W ⊂⊂ U` on
which the current vanishes, i.e. in its zero region. -/
theorem Submission.iwl_cr_support_lemmas :
    (∀ (P m : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (m + 1)),
      Z.boundary.support ⊆ Z.support) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P))
      (Zj : ℕ → GeometricCurrentOn U n) (Z : GeometricCurrentOn U n), IsClosed K →
      (∀ j, (Zj j).support ⊆ K) → WeaklyConvergesOn Zj Z → Z.support ⊆ K) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Z₁ Z₂ Z : GeometricCurrentOn U n) (a b : ℝ),
      (∀ ω : TestFormOn U n, Z ω = a * Z₁ ω + b * Z₂ ω) →
      Z.support ⊆ Z₁.support ∪ Z₂.support) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) If `Z` vanishes on an admissible `W`, so does `∂Z`: `∂Z φ = Z (dφ)` and
    -- `tsupport dφ ⊆ tsupport φ ⊆ W`.
    intro P m U Z x hx
    refine ⟨hx.1, fun hxZ => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
    refine Set.mem_sUnion.2 ⟨W, ⟨hWo, hWc, hWU, fun φ hφ => ?_⟩, hxW⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hφ)
  · -- (2) For `x ∈ spt Z \ K`, the ball `W = B(x, ε/2)` has `closure W ⊆ U \ K`.  A test form
    -- supported in `W` misses `K ⊇ spt (Zj j)`, so every `Zj j` kills it, and so does the limit.
    intro P n U hU K Zj Z hK hZj hconv x hx
    by_contra hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.sdiff hK) x ⟨hx.1, hxK⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ U \ K := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans sdiff_subset, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have h0 : ∀ j, Zj j ω = 0 := fun j =>
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U (Zj j) ω
          (Set.disjoint_left.2 fun y hy hyS => (hcl (subset_closure (hω hy))).2 (hZj j hyS))
      have hlim := hconv ω
      simp only [h0] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- (3) For `x ∈ spt Z` outside `spt Z₁ ∪ spt Z₂`, the ball `W = B(x, ε/2)` has `closure W`
    -- inside both zero regions and `U`, so `Z₁`, `Z₂` and hence `Z = a Z₁ + b Z₂` vanish on `W`.
    intro P n U hU Z₁ Z₂ Z a b hZ x hx
    by_contra hx12
    have h1 : x ∈ Z₁.zeroRegion := by
      by_contra h
      exact hx12 (Or.inl ⟨hx.1, h⟩)
    have h2 : x ∈ Z₂.zeroRegion := by
      by_contra h
      exact hx12 (Or.inr ⟨hx.1, h⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((Z₁.isOpen_zeroRegion.inter Z₂.isOpen_zeroRegion).inter hU) x ⟨⟨h1, h2⟩, hx.1⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ Z₁.zeroRegion ∩ Z₂.zeroRegion ∩ U := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans inter_subset_right, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have e1 : Z₁ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₁ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.1)
      have e2 : Z₂ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₂ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.2)
      rw [hZ ω, e1, e2]
      ring

/-- The cone `0 ⨯ X` over `X ∈ 𝒟ₘ(ℝ^P)` with `spt X ⊆ B̄_R(0)` (**Simon Ch. 6, 2.23, 2.30**):
`C(ω) := X(Φ ω)` for the cut-off radial operator `Φ ω = ζ · Hω`, which satisfies
`Hω(x)(v) = ∫₀¹ tᵐ ω(tx)(x, v) dt` on `B_r(0)`, `r = max R 0 + 1`.  `Φ` maps null sequences to
null sequences, so `C` is a current; a test form `ψ` with the `Hω`-formula on an open `N ⊇ spt X`
agrees with `Φ ω` on the open `N ∩ B_r(0) ⊇ spt X`, so `X ψ = X (Φ ω) = C ω` by locality. -/
theorem Submission.iwl_cr_cone_exists : ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m), X.support ⊆ closedBall 0 R → ∃ C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) := by
  intro P m R X hX
  -- The cut-off radial operator on `B_r(0)`, `r = max R 0 + 1`: its hypothesis is the radial
  -- operator with `k = a = m`, without the derivative formula.
  obtain ⟨Φ, hΦ, hΦH⟩ := Submission.iwl_cr_ce_cutoff_radial_operator P m (max R 0 + 1)
    fun ω hω => by
      obtain ⟨ψ, hψ, hψH, -, hψD⟩ := Submission.iwl_cr_radial_operator P m m ω hω
      exact ⟨ψ, hψ, hψH, hψD⟩
  -- `C = X ∘ Φ` is a current, since `Φ` maps null sequences to null sequences.
  refine ⟨⟨X.toCurrent ∘ₗ Φ, fun ωs hωs => X.continuous' (fun l => Φ (ωs l)) (hΦ ωs hωs)⟩, ?_⟩
  rintro ω ψ ⟨N, hN, hXN, hψN⟩
  -- `Φ ω = ψ` on the open set `N ∩ B_r(0) ⊇ spt X`, so `X (Φ ω) = X ψ` by locality.
  have hXr : X.support ⊆ ball 0 (max R 0 + 1) :=
    hX.trans (closedBall_subset_ball ((le_max_left R 0).trans_lt (lt_add_one _)))
  exact Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support P m univ X (Φ ω) ψ
    (N ∩ ball 0 (max R 0 + 1)) (hN.inter isOpen_ball) (subset_inter hXN hXr)
    fun x hx => ContinuousAlternatingMap.ext fun v =>
      (hΦH ω x hx.2 v).trans (hψN x hx.1 v).symm

/-- **Cone estimates** (items 3–4 of the cycle reduction; cf. the cone 2.30 and the mass bound
2.27 of Simon Ch. 6).  With `c = P^{2m+1}` and `R ≥ 0`: if `spt X ⊆ B̄_R(0)` and `C` is a cone
over `X`, i.e. `C(ω) = X(ψ)` whenever `ψ(x)(v) = ∫₀¹ t^m ω(tx)(x, v) dt` near `spt X`, then
`spt C ⊆ B̄_R(0)` and `M(C) ≤ c R M(X)`; and if `X_j ⇀ X` (all supported in `B̄_R(0)`), the
cones `C_j` over `X_j` converge weakly to `C`.  Each `ω` is tested through one cut-off radial
form `ψ = ζ ψ_ω`, with `ζ = 1` near `B̄_R(0)`. -/
theorem Submission.iwl_cr_cone_estimates : ∀ (P m : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 ≤ R → (∀ (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → C.support ⊆ closedBall 0 R ∧ (X.mass < ∞ → C.mass ≤ ENNReal.ofReal (c * R) * X.mass)) ∧ (∀ (Xj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) m) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (Cj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, (Xj j).support ⊆ closedBall 0 R) → X.support ⊆ closedBall 0 R → (∀ j, (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ (Xj j).support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → (Cj j) ω = (Xj j) ψ)) → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → WeaklyConvergesOn Xj X → WeaklyConvergesOn Cj C) := by
  intro P m
  -- Step 1: for `0 < r < s`, `ω` has a cut-off radial form `ψ`, satisfying the radial formula on
  -- `B_r(0)` and `|ψ| ≤ P^{2m+1} s` if `|ω| ≤ 1`.
  have hcut : ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (r s : ℝ), 0 < r → r < s →
      ∃ ψ : TestFormOn (univ : Set (Eucl P)) m,
        (∀ x ∈ ball (0 : Eucl P) r, ∀ v : Fin m → Eucl P,
          (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1,
            t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) ∧
        ((∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) (m + 1)) y) ≤ 1) →
          ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) m) x) ≤
            (P : ℝ) ^ (2 * m + 1) * s) := by
    intro ω r s hr hrs
    obtain ⟨ψ₀, hψ₀, hψ₀eq, -⟩ :=
      Submission.iwl_cr_radial_operator P m m (ω : DifferentialForm (Eucl P) (m + 1))
        ω.property.1.1
    exact Submission.iwl_cr_cest_cutoff_radial_form P m ω ψ₀ r s hψ₀ hψ₀eq hr hrs
  refine ⟨(P : ℝ) ^ (2 * m + 1), by positivity, fun R hR => ⟨?_, ?_⟩⟩
  · -- Step 2 (a): support, and mass with `ψ` cut off between `B_{R+δ/2}(0)` and `B_{R+δ}(0)`.
    intro X C hX hcone
    refine ⟨Submission.iwl_cr_cest_cone_support P m R X C hX hcone, fun hXm => ?_⟩
    refine Submission.iwl_cr_cest_mass_le_of_forms P m (m + 1) X C ((P : ℝ) ^ (2 * m + 1)) R
      (by positivity) hR hXm fun ω hω δ hδ => ?_
    obtain ⟨ψ, hψeq, hψle⟩ := hcut ω (R + δ / 2) (R + δ) (by linarith) (by linarith)
    exact ⟨ψ, hcone ω ψ ⟨ball 0 (R + δ / 2), isOpen_ball,
      hX.trans (closedBall_subset_ball (by linarith)), hψeq⟩, hψle hω.2⟩
  · -- Step 3 (b): one `ψ`, cut off between `B_{R+1}(0)` and `B_{R+2}(0)`, serves every `j`, so
    -- `C_j(ω) = X_j(ψ) → X(ψ) = C(ω)`.
    intro Xj X Cj C hXj hX hconej hcone hconv ω
    obtain ⟨ψ, hψeq, -⟩ := hcut ω (R + 1) (R + 2) (by linarith) (by linarith)
    have hj : ∀ j, Cj j ω = Xj j ψ := fun j => hconej j ω ψ ⟨ball 0 (R + 1), isOpen_ball,
      (hXj j).trans (closedBall_subset_ball (by linarith)), hψeq⟩
    rw [hcone ω ψ ⟨ball 0 (R + 1), isOpen_ball,
      hX.trans (closedBall_subset_ball (by linarith)), hψeq⟩]
    exact (hconv ψ).congr fun j => (hj j).symm
/-- Simon 2.31 for `X = ∂Y` with `spt Y` compact: the cone `C = 0 ⨯ ∂Y` (`C(ω) = ∂Y(ψ)` whenever
`ψ = H(ω)` near `spt ∂Y`) has `∂C = ∂Y`.  For `φ ∈ 𝒟ᵐ` the radial form `χ = H(dφ)` satisfies
`dχ = dφ` by the radial homotopy formula, and `ζχ`, with a cut-off `ζ = 1` near `spt Y`, is
admissible in the cone identity, so `∂C(φ) = C(dφ) = Y(d(ζχ)) = Y(dφ) = ∂Y(φ)`. -/
theorem Submission.iwl_cr_cone_boundary :
    ∀ (P m : ℕ) (R : ℝ) (Y C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
      Y.support ⊆ closedBall 0 R →
      (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m),
        (∃ N : Set (Eucl P), IsOpen N ∧ Y.boundary.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P,
          (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1,
            t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) →
        C ω = Y.boundary ψ) →
      C.boundary = Y.boundary := by
  intro P m R Y C hY hcone
  -- `dχ = dφ` for `χ = H(dφ)`: in degree `0`, `χ = φ - φ 0`; in degree `k + 1`, `χ + dψ = φ`
  -- with `ψ = Hφ`, and `d(dψ) = 0`.
  have hd : ∀ (k : ℕ) (φ χ : DifferentialForm (Eucl P) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ →
      (∀ (x : Eucl P) (v : Fin k → Eucl P),
        χ x v = ∫ t in (0 : ℝ)..1, t ^ k * extDeriv φ (t • x) (Fin.cons x v)) →
      extDeriv χ = extDeriv φ := by
    intro k
    cases k with
    | zero =>
      intro φ χ hφ _ hχ
      have hχφ : χ = fun x => φ x - φ 0 :=
        funext (Submission.iwl_cr_radial_homotopy.2 P φ χ hφ hχ)
      subst hχφ
      funext x
      rw [extDeriv, extDeriv, fderiv_sub_const]
    | succ k =>
      intro φ χ hφ hχs hχ
      obtain ⟨ψ, hψ, -, hψd, -⟩ := Submission.iwl_cr_radial_operator P k k φ hφ
      have hφχ : φ = χ + extDeriv ψ := funext fun x =>
        (Submission.iwl_cr_radial_homotopy.1 P k φ ψ χ hφ hψd hχ x).symm
      have hdψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extDeriv ψ) := by
        change ContDiff ℝ _ (fun x => ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ ψ x))
        simpa only [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, Function.comp_def]
          using (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).contDiff.comp
            (hψ.fderiv_right (by simp))
      funext x
      rw [hφχ, extDeriv_add (hχs.differentiable (by simp)).differentiableAt
        (hdψ.differentiable (by simp)).differentiableAt, extDeriv_extDeriv hψ (by simp),
        Pi.zero_apply, add_zero]
  -- A cut-off `ζ` with `ζ = 1` on the ball `B = B_{R₀+1}(0) ⊇ spt Y ⊇ spt ∂Y`.
  have hR₀ : 0 ≤ max R 0 := le_max_right R 0
  let ζ : ContDiffBump (0 : Eucl P) := ⟨max R 0 + 1, max R 0 + 2, by linarith, by linarith⟩
  have hζ : ∀ x ∈ ball (0 : Eucl P) (max R 0 + 1), ζ x = 1 := fun x hx =>
    ζ.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hYB : Y.support ⊆ ball (0 : Eucl P) (max R 0 + 1) :=
    hY.trans (closedBall_subset_ball (by linarith [le_max_left R 0]))
  refine GeometricCurrentOn.ext fun φ => ?_
  rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply]
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : DifferentialForm (Eucl P) m) := φ.property.1.1
  have hdφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extDeriv (φ : DifferentialForm (Eucl P) m)) :=
    (exteriorDerivativeTestOn univ m φ).property.1.1
  -- `χ = H(dφ)` and the test form `ζχ`.
  obtain ⟨χ, hχs, hχ, -, -⟩ := Submission.iwl_cr_radial_operator P m m _ hdφ
  let ζχ : TestFormOn (univ : Set (Eucl P)) m :=
    ⟨fun x => ζ x • χ x, ⟨⟨ζ.contDiff.smul hχs, ζ.hasCompactSupport.smul_right⟩, subset_univ _⟩⟩
  -- `ζχ` satisfies the `H(dφ)`-formula on `B ⊇ spt ∂Y`, so `C(dφ) = ∂Y(ζχ) = Y(d(ζχ))`.
  have hC : C (exteriorDerivativeTestOn univ m φ) = Y.boundary ζχ := by
    refine hcone _ _ ⟨ball 0 (max R 0 + 1), isOpen_ball,
      (Submission.iwl_cr_support_lemmas.1 P m univ Y).trans hYB, ?_⟩
    intro x hx v
    change (ζ x • χ x) v = _
    rw [ContinuousAlternatingMap.smul_apply, hζ x hx, one_smul, hχ x v]
    rfl
  rw [hC, GeometricCurrentOn.boundary_apply]
  -- `d(ζχ) = dχ = dφ` on `B`.
  have hdχ := hd m _ χ hφ hχs hχ
  have hloc : ∀ x ∈ ball (0 : Eucl P) (max R 0 + 1),
      extDeriv (ζχ : DifferentialForm (Eucl P) m) x =
        extDeriv (φ : DifferentialForm (Eucl P) m) x := by
    intro x hx
    rw [← hdχ]
    apply Filter.EventuallyEq.extDeriv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    change ζ y • χ y = χ y
    rw [hζ y hy, one_smul]
  -- So `d(ζχ) - dφ` vanishes on `B ⊇ spt Y`, and `Y` kills it.
  have hsupp : tsupport ((exteriorDerivativeTestOn univ m ζχ - exteriorDerivativeTestOn univ m φ :
      TestFormOn (univ : Set (Eucl P)) (m + 1)) : DifferentialForm (Eucl P) (m + 1)) ⊆
      (ball (0 : Eucl P) (max R 0 + 1))ᶜ := by
    refine closure_minimal ?_ isOpen_ball.isClosed_compl
    intro x hx hxB
    apply hx
    change extDeriv (ζχ : DifferentialForm (Eucl P) m) x -
      extDeriv (φ : DifferentialForm (Eucl P) m) x = 0
    rw [hloc x hxB, sub_self]
  have h0 := Submission.isoperimetric_apply_eq_zero_of_disjoint_support P (m + 1) univ Y _
    (Set.disjoint_of_subset_left hsupp hYB.disjoint_compl_left)
  rw [map_sub Y.toCurrent] at h0
  exact sub_eq_zero.1 h0

/-- Slices of a form supported off `Φ([0, 1] × B̄_R(0))`, `Φ(s, x) = (s, x) ∈ ℝ^{P+1}`, are
annihilated by `X`: for `s ∈ [0, 1]`, `tsupport (φ s)` lies in the closed set
`{x | Φ(s, x) ∈ tsupport η}`, which misses `B̄_R(0) ⊇ spt X`, so `X (φ s) = 0` and the integral
over `[0, 1]` vanishes. -/
theorem Submission.iwl_cr_ci_ps_slice_integral_eq_zero :
    ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m)
      (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1))
      (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m),
      X.support ⊆ closedBall 0 R →
      Disjoint (tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)))
        ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ''
          (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P),
        (φ s : DifferentialForm (Eucl P) m) x v =
          (η : DifferentialForm (Eucl (P + 1)) (m + 1))
            ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) →
      ∫ s in (0 : ℝ)..1, X (φ s) = 0 := by
  intro P m R X η φ hX hdisj hφ
  have hzero : ∀ s ∈ Icc (0 : ℝ) 1, X (φ s) = 0 := by
    intro s hs
    -- `C_s = {x | Φ(s, x) ∈ tsupport η}` is closed, as `x ↦ Φ(s, x)` is continuous.
    have hΦ : Continuous fun x : Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) :=
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
        (continuous_const.finCons (EuclideanSpace.equiv (Fin P) ℝ).continuous)
    have hC := (isClosed_tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1))).preimage hΦ
    -- `φ s` vanishes off `C_s` by the slice identity, so `tsupport (φ s) ⊆ C_s`.
    have hsupp : tsupport (φ s : DifferentialForm (Eucl P) m) ⊆
        (fun x : Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ⁻¹'
          tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)) := by
      refine closure_minimal ?_ hC
      intro x hx
      by_contra hxC
      have hxC' : (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) ∉
          tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)) := hxC
      refine Function.mem_support.1 hx ?_
      ext v
      rw [hφ s hs x v, image_eq_zero_of_notMem_tsupport hxC']
      rfl
    -- `spt X ⊆ B̄_R(0)` misses `C_s`: `Φ(s, x) ∈ Φ([0, 1] × B̄_R(0))` lies off `tsupport η`.
    refine Submission.isoperimetric_apply_eq_zero_of_disjoint_support P m univ X (φ s) ?_
    rw [Set.disjoint_left]
    intro x hx hxX
    exact Set.disjoint_left.1 hdisj (Set.mem_preimage.1 (hsupp hx))
      ⟨(s, x), Set.mk_mem_prod hs (hX hxX), rfl⟩
  -- The integrand vanishes on `uIcc 0 1 = [0, 1]`.
  have hcongr : EqOn (fun s => X (φ s)) (fun _ => (0 : ℝ)) (uIcc 0 1) := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact hzero s hs
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_zero]
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

/-- **Support of the product current `[[(0,1)]] × X`.**  With `Φ(s, x) = (s, x)`, the set
`L = Φ([0, 1] × B̄_R(0))` is compact as a continuous image of a compact set, hence closed.  If
`tsupport η` misses `L`, the slices `φ s = η(Φ(s, ·))(e₀, ι ·)` are annihilated by `X` (whose
support lies in `B̄_R(0)`), so `Z η = ∫₀¹ X (φ s) ds = 0`; by the support criterion, `spt Z ⊆ L`. -/
theorem Submission.iwl_cr_ci_product_support : ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), (φ s : DifferentialForm (Eucl P) m) x v = (η : DifferentialForm (Eucl (P + 1)) (m + 1)) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → IsCompact ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) ∧ Z.support ⊆ ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) := by
  intro P m R X Z hX hProd
  -- `L = Φ([0, 1] × B̄_R(0))` is compact, being a continuous image of a compact set.
  have hΦ : Continuous fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)) := by
    fun_prop
  have hL := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : Eucl P) R)).image hΦ
  -- `L` is closed, so it contains `spt Z` once `Z` kills every test form supported off `L`.
  refine ⟨hL, Submission.fiw_tb_ext_support_subset (P + 1) (m + 1) univ _ Z isOpen_univ
    hL.isClosed fun η hη => ?_⟩
  -- `Z η = ∫₀¹ X (φ s) ds` for the slices `φ s` of `η`, and that integral vanishes.
  obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm P m η
  exact (hProd η φ fun s _ x v => hφ s x v).trans
    (Submission.iwl_cr_ci_ps_slice_integral_eq_zero P m R X η φ hX hη fun s _ x v => hφ s x v)
/-- Cut-off pull-backs of smooth forms are test forms (step 5 of the proof of Simon Ch. 6, 8.2):
for smooth `f : ℝ^P → ℝ^Q`, a smooth form `ω` and a smooth compactly supported `χ`,
`η(y) = χ(y) ω(f(y)) ∘ Df(y)` is smooth (the pull-back `B ↦ (α ↦ α ∘ B)` is analytic) and has
compact support. -/
theorem Submission.iwl_cr_ci_cutoff_pullback_testForm :
    ∀ (P Q k : ℕ) (f : Eucl P → Eucl Q) (χ : Eucl P → ℝ) (ω : DifferentialForm (Eucl Q) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ →
      HasCompactSupport χ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∃ η : TestFormOn (univ : Set (Eucl P)) k, ∀ y, (η : DifferentialForm (Eucl P) k) y =
        χ y • (ω (f y)).compContinuousLinearMap (fderiv ℝ f y) := by
  intro P Q k f χ ω hf hχ hχc hω
  -- `y ↦ Df(y)` is smooth.
  have hDf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right le_rfl
  -- The pull-back operator `B ↦ (α ↦ α ∘ B)` is analytic, hence smooth.
  have hpull : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (Eucl P →L[ℝ] Eucl Q) → Covector (Eucl Q) k →L[ℝ] Covector (Eucl P) k) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- So `p(y) = ω(f(y)) ∘ Df(y)` is smooth, and `η = χ • p` is smooth with compact support.
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) :=
    (hpull.comp hDf).clm_apply (hω.comp hf)
  exact ⟨⟨fun y => χ y • (ω (f y)).compContinuousLinearMap (fderiv ℝ f y),
    ⟨hχ.smul hp, hχc.smul_right⟩, subset_univ _⟩, fun y => rfl⟩
/-- The cone map `h(y) = y₀ • π(y)`, `π(y) = (y₁, …, y_P)`, is a product of continuous linear maps,
hence smooth, and `h(Φ(s, x)) = s • x` for `Φ(s, x) = (s, x)`.  By the product rule
`Dh(y)(w) = y₀ • π(w) + w₀ • π(y)`, so `Dh(Φ(s, x))` maps `e₀ ↦ x` and `ι(w) = Φ(0, w) ↦ s • w`;
multilinearity then gives `α(x, s • v₁, …, s • vₘ) = s ^ m * α(x, v₁, …, vₘ)`. -/
theorem Submission.iwl_cr_ci_cone_map :
    ∀ (P m : ℕ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Eucl (P + 1) =>
      y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) ∧
    ∀ (s : ℝ) (x : Eucl P), (fun y : Eucl (P + 1) =>
      y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) =
      s • x ∧
    ∀ (α : Covector (Eucl P) (m + 1)) (v : Fin m → Eucl P),
      (α.compContinuousLinearMap (fderiv ℝ (fun y : Eucl (P + 1) =>
        y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))))
        (Fin.cons (EuclideanSpace.single 0 1) fun i =>
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) =
      s ^ m * α (Fin.cons x v) := by
  intro P m
  -- `p₀(y) = y₀` and `π(y) = (y₁, …, y_P)` are continuous linear maps, and `h(y) = p₀(y) • π(y)`.
  let p₀ : Eucl (P + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  let π : Eucl (P + 1) →L[ℝ] Eucl P :=
    (EuclideanSpace.equiv (Fin P) ℝ).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j : Fin P => ContinuousLinearMap.proj j.succ) ∘L
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).toContinuousLinearMap
  have hh : (fun y : Eucl (P + 1) => y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) = fun y => p₀ y • π y := rfl
  -- Values on `Φ(t, z)`: `p₀(Φ(t, z)) = t` and `π(Φ(t, z)) = z`.
  have hp₀Φ : ∀ (t : ℝ) (z : Eucl P), p₀ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons t (EuclideanSpace.equiv (Fin P) ℝ z))) = t := fun t z => rfl
  have hπΦ : ∀ (t : ℝ) (z : Eucl P), π ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons t (EuclideanSpace.equiv (Fin P) ℝ z))) = z := fun t z => rfl
  refine ⟨?_, fun s x => ⟨?_, fun α v => ?_⟩⟩
  · rw [hh]
    exact p₀.contDiff.smul π.contDiff
  · rw [hh]
    show p₀ _ • π _ = s • x
    rw [hp₀Φ, hπΦ]
  · -- Product rule: `Dh(Φ(s, x)) = s • π + p₀.smulRight x`.
    have hD : fderiv ℝ (fun y : Eucl (P + 1) => y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) = s • π + p₀.smulRight x := by
      have hd := (p₀.hasFDerivAt (x := (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))).smul π.hasFDerivAt
      rw [hp₀Φ, hπΦ] at hd
      rw [hh]
      exact hd.fderiv
    -- `Dh(Φ(s, x)) e₀ = s • 0 + 1 • x = x` and `Dh(Φ(s, x)) (ι w) = s • w + 0 • x = s • w`.
    have he₀ : (s • π + p₀.smulRight x) (EuclideanSpace.single 0 1) = x := by
      have h1 : p₀ (EuclideanSpace.single 0 1) = 1 := by simp [p₀]
      have h2 : π (EuclideanSpace.single 0 1) = 0 := by
        ext j
        simp [π, Fin.succ_ne_zero]
      rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, h1, h2, smul_zero,
        one_smul, zero_add]
    have hι : ∀ w : Eucl P, (s • π + p₀.smulRight x) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ w))) = s • w := by
      intro w
      rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hp₀Φ, hπΦ, zero_smul,
        add_zero]
    rw [hD, ContinuousAlternatingMap.compContinuousLinearMap_apply, Fin.comp_cons, he₀]
    have hcomp : (⇑(s • π + p₀.smulRight x) ∘ fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) = fun i => s • v i :=
      funext fun i => hι (v i)
    rw [hcomp]
    -- Multilinearity: `α(x, s • v₁, …, s • vₘ) = (1 * s ^ m) • α(x, v₁, …, vₘ)`.
    have key : (Fin.cons x (fun i => s • v i) : Fin (m + 1) → Eucl P) =
        fun j => (Fin.cons (1 : ℝ) (fun _ : Fin m => s) : Fin (m + 1) → ℝ) j •
          (Fin.cons x v : Fin (m + 1) → Eucl P) j := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero, one_smul]
      · simp only [Fin.cons_succ]
    rw [key, ContinuousAlternatingMap.map_smul_univ, Fin.prod_univ_succ, smul_eq_mul]
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
/-- The product `χ(y) = ϑ(y₀) ζ(π y)` of cut-offs on `ℝ` and `ℝ^P`, `π y = (y₁, …, y_P)`, is a
cut-off on `ℝ^{P+1}`: `y ↦ y₀` and `π` are linear, so `χ` is smooth, and `‖y‖ ≤ |y₀| + ‖π y‖`
puts `support χ` inside the compact ball `B̄_{a+b}(0)`, where `tsupport ϑ ⊆ B̄_a(0)` and
`tsupport ζ ⊆ B̄_b(0)`. -/
theorem Submission.iwl_cr_ci_product_cutoff :
    ∀ (P : ℕ) (ϑ : ℝ → ℝ) (ζ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑ →
      HasCompactSupport ϑ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ → HasCompactSupport ζ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Eucl (P + 1) => ϑ (y 0) *
        ζ ((EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ∧
      HasCompactSupport (fun y : Eucl (P + 1) => ϑ (y 0) *
        ζ ((EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) := by
  intro P ϑ ζ hϑ hϑc hζ hζc
  -- `π y = (y₁, …, y_P)`: the equivalences `EuclideanSpace.equiv` around `Fin.tail`.
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) π :=
    (EuclideanSpace.equiv (Fin P) ℝ).symm.contDiff.comp
      ((contDiff_pi.2 fun j : Fin P => contDiff_apply ℝ ℝ j.succ).comp
        (EuclideanSpace.equiv (Fin (P + 1)) ℝ).contDiff)
  refine ⟨(hϑ.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (P + 1))).contDiff).mul
    (hζ.comp hπ), ?_⟩
  -- `‖y‖² = y₀² + ‖π y‖²`, hence `‖y‖ ≤ |y₀| + ‖π y‖`.
  have hnorm : ∀ y : Eucl (P + 1), ‖y‖ ≤ |y 0| + ‖π y‖ := by
    intro y
    have h1 : ‖y‖ ^ 2 = y 0 ^ 2 + ‖π y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    have h2 : ‖y‖ ^ 2 ≤ (|y 0| + ‖π y‖) ^ 2 := by
      rw [h1, add_sq, sq_abs]
      nlinarith [abs_nonneg (y 0), norm_nonneg (π y)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  -- `χ y ≠ 0` forces `|y₀| ≤ a` and `‖π y‖ ≤ b`, so `support χ ⊆ B̄_{a+b}(0)`.
  obtain ⟨a, ha⟩ := hϑc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨b, hb⟩ := hζc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl (P + 1)) (a + b)) ?_
  intro y hy
  by_contra hne
  have h0 : y 0 ∈ closedBall (0 : ℝ) a := ha (subset_tsupport _ (left_ne_zero_of_mul hne))
  have hπy : π y ∈ closedBall (0 : Eucl P) b := hb (subset_tsupport _ (right_ne_zero_of_mul hne))
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at h0
  rw [mem_closedBall_zero_iff] at hπy
  exact hy (mem_closedBall_zero_iff.2 ((hnorm y).trans (add_le_add h0 hπy)))
/-- **`Hⁿ(M ∩ K) < ∞` for integer multiplicity triples (Simon Ch. 6, 3.1).**  If
`(M, θ, ξ)` is a rectifiable triple in `U` and `θ` is integer-valued on `M`, then `θ ≥ 1` on `M`
(`θ > 0`), so for compact `K ⊆ U`:
`Hⁿ(M ∩ K) = ∫⁻_{M ∩ K} 1 dHⁿ ≤ ∫⁻_{M ∩ K} |θ| dHⁿ < ∞` (`θ` is `Hⁿ`-integrable on `M ∩ K`). -/
theorem Submission.iwl_cr_ci_ie_measure_inter_compact_lt_top : ∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (K : Set (Eucl P)), IsRectifiableTriple U n M θ ξ → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → IsCompact K → K ⊆ U → (μHE[n] : Measure (Eucl P)) (M ∩ K) < ∞ := by
  intro P n U M θ ξ K hT hint hK hKU
  -- `θ = k ∈ ℕ` and `θ > 0` force `θ ≥ 1` on `M`.
  have h1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hint x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    have hk0 : k ≠ 0 := by rintro rfl; simp at hpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hθ : IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) := hT.integrableOn K hK hKU
  have hnm : NullMeasurableSet (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
  -- `‖θ‖ₑ ≥ 1` a.e. on `M ∩ K`.
  have hae : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)), (1 : ℝ≥0∞) ≤ ‖θ x‖ₑ := by
    filter_upwards [ae_restrict_mem₀ hnm] with x hx
    have h := h1 x hx.1
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by linarith)]
    exact ENNReal.one_le_ofReal.mpr h
  -- `Hⁿ(M ∩ K) = ∫⁻_{M ∩ K} 1 ≤ ∫⁻_{M ∩ K} ‖θ‖ₑ < ∞`.
  calc (μHE[n] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, (1 : ℝ≥0∞) ∂(μHE[n] : Measure (Eucl P)) := (setLIntegral_one _).symm
    _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hae
    _ < ∞ := hθ.hasFiniteIntegral
/-- **Product formula in measure form (Federer 3.2.23; Simon Ch. 6, 3.2(2)).**  Write
`π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`.  If `Hᵐ(A ∩ K) < ∞` for every
compact `K ⊆ ℝ^P` and `∫⁻_{π⁻¹(A)} g dH^{m+1} = ∫⁻_ℝ ∫⁻_A g(Φ(s, x)) dHᵐ(x) ds` for every Borel
`g ≥ 0`, then `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ × Hᵐ⌞A)`.  Testing the formula with `g = 1_B` gives
`(H^{m+1}⌞π⁻¹(A))(B) = ∫⁻_ℝ (Hᵐ⌞A){x : Φ(s, x) ∈ B} ds = (L¹ × Hᵐ⌞A)(Φ⁻¹(B))` for Borel `B`;
`Hᵐ⌞A` is finite on compact sets, hence σ-finite, so the product measure is given by sections. -/
theorem Submission.iwl_cr_ip_restrict_preimage_eq_map : ∀ (P m : ℕ) (A : Set (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A)) := by
  intro P m A hfin hPF
  -- Step 1: `ν := Hᵐ⌞A` is finite on compact sets (compact sets are closed, hence Borel), so it
  -- is σ-finite on the σ-compact space `ℝ^P`; in particular `Measure.prod_apply` applies to `L¹ × ν`.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hfin K hK⟩
  -- Step 2: `Φ(s, x) = (s, x)` is continuous, hence Borel measurable.
  have hΦ : Measurable (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := by
    refine ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_).measurable
    exact Continuous.finCons continuous_fst
      ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
  -- Steps 3-7: the two measures agree on every Borel set `B`.  The left side is
  -- `∫⁻_{π⁻¹(A)} 1_B dH^{m+1} = ∫⁻_ℝ ∫⁻_A 1_B(Φ(s, x)) dHᵐ(x) ds` (the hypothesis with `g = 1_B`),
  -- the right side is `∫⁻_ℝ ν({x : Φ(s, x) ∈ B}) ds` (`Measure.map_apply`, `Measure.prod_apply`),
  -- and `1_B(Φ(s, x)) = 1_{{x : Φ(s, x) ∈ B}}(x)`.
  ext B hB
  rw [Measure.map_apply hΦ hB, Measure.prod_apply (hΦ hB), ← lintegral_indicator_one hB,
    hPF (B.indicator 1) (measurable_one.indicator hB)]
  refine lintegral_congr fun s => ?_
  rw [← lintegral_indicator_one (measurable_prodMk_left (hΦ hB))]
  rfl
/-- Measure identity on the slab over `A` (fact (D2) in the proof of the product triple): for
`Φ(s, x) = (s, x₁, …, x_P)` and `π(y) = (y₁, …, y_P)`, the cylinder identity
`Hᵐ⁺¹ ⌞ {π ∈ A} = Φ_#(L¹ × Hᵐ ⌞ A)` restricts to the slab `{π ∈ A, 0 < y₀ < 1}`.  Restricting
both sides to the Borel set `{0 < y₀ < 1}`, whose `Φ`-preimage is `(0, 1) × ℝ^P`, gives
`Φ_#((L¹ ⌞ (0, 1)) × Hᵐ ⌞ A)`; `Hᵐ ⌞ A` is finite on compact sets, hence s-finite. -/
theorem Submission.iwl_cr_ip_pt_slab_restrict_eq_map :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) →
      CountablyRectifiable m A →
      (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) →
      (μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} =
        Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
          ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) →
    ∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) →
      CountablyRectifiable m A →
      (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) →
      (μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧
            EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
        Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
          (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
            ((μHE[m] : Measure (Eucl P)).restrict A)) := by
  intro P m hMP A hA hArect hAfin
  -- `Hᵐ ⌞ A` is finite on compact sets, hence σ-finite (`ℝ^P` is σ-compact).
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hAfin K hK⟩
  -- `Φ` is continuous and `O = {0 < y₀ < 1}` is open, so both are Borel.
  have hΦ : Measurable (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) :=
    ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp (Continuous.finCons
      continuous_fst ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))).measurable
  have hO : MeasurableSet
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage
      ((continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous).measurable
  -- `Φ(s, x)₀ = s`, so `Φ⁻¹(O) = (0, 1) × ℝ^P`.
  have hpre : (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ⁻¹'
        {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      Ioo (0 : ℝ) 1 ×ˢ univ := by
    ext ⟨s, x⟩
    simp only [mem_preimage, mem_ofPred_eq, ContinuousLinearEquiv.apply_symm_apply,
      Fin.cons_zero, mem_prod, mem_univ, and_true]
  -- The slab is `O ∩ {π ∈ A}`.
  have hslab : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} ∩
        {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} := by
    ext y
    exact and_comm
  rw [hslab, ← Measure.restrict_restrict hO, hMP A hA hArect hAfin, Measure.restrict_map hΦ hO,
    hpre, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Integrability and a.e. strong measurability pass from `A ⊆ ℝ^P` to the slab
`S_A = {y | π y ∈ A ∧ y₀ ∈ (0, 1)}`, `π y = (y₁, …, y_P)`.  By `slab_restrict_eq_map`,
`H^{m+1} ⌞ S_A = Φ'_# ((L¹ ⌞ (0, 1)) ⊗ (Hᵐ ⌞ A))` for `Φ'(s, x) = (s, x₁, …, x_P)`, a
homeomorphism (hence a measurable embedding) with `π ∘ Φ' = Prod.snd`.  So (a) is integrability
of `f ∘ Prod.snd` for the product of the finite measure `L¹ ⌞ (0, 1)` with `Hᵐ ⌞ A`, and (b) is
a.e. strong measurability of `g ∘ Prod.snd`, `Prod.snd` being quasi-measure-preserving onto
`Hᵐ ⌞ A`. -/
theorem Submission.iwl_cr_ip_pt_slab_transfer : ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (∀ f : Eucl P → ℝ, IntegrableOn f A (μHE[m] : Measure (Eucl P)) → IntegrableOn (fun y : Eucl (P + 1) => f ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (μHE[m + 1] : Measure (Eucl (P + 1)))) ∧ ∀ g : Eucl P → NVector (Eucl P) m, AEStronglyMeasurable g ((μHE[m] : Measure (Eucl P)).restrict A) → AEStronglyMeasurable (fun y : Eucl (P + 1) => g ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ((μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}) := by
  intro P m hMP A hA hArect hAfin
  -- `H^{m+1} ⌞ S_A = Φ'_# ((L¹ ⌞ (0, 1)) ⊗ (Hᵐ ⌞ A))`.
  have hD := Submission.iwl_cr_ip_pt_slab_restrict_eq_map P m hMP A hA hArect hAfin
  -- `Hᵐ ⌞ A` is finite on compact sets, hence σ-finite, as `Integrable.comp_snd` needs.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hAfin K hK⟩
  -- `Φ'` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}` with inverse `y ↦ (y₀, π y)`.
  let Φh : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0,
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      left_inv := fun p => by
        rcases p with ⟨s, x⟩
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
          ContinuousLinearEquiv.symm_apply_apply]
      continuous_toFun := by
        refine (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_
        exact Continuous.finCons continuous_fst
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ ?_
        · exact (continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
        · refine (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_
          exact continuous_pi fun i =>
            (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous }
  have hΦ : MeasurableEmbedding (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := Φh.measurableEmbedding
  -- `π ∘ Φ' = Prod.snd`.
  have hπΦ : ∀ p : ℝ × Eucl P, (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))))) = p.2 := by
    intro p
    simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · -- (a) `f ∘ Prod.snd` is integrable for the product, `L¹ ⌞ (0, 1)` being finite.
    rw [IntegrableOn, hD, hΦ.integrable_map_iff]
    refine (Integrable.comp_snd hf ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hπΦ]
  · -- (b) `Prod.snd` is quasi-measure-preserving from the product onto `Hᵐ ⌞ A`.
    rw [hD, hΦ.aestronglyMeasurable_map_iff]
    refine (hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hπΦ]
/-- **Slice formula for the product `[[(0, 1)]] × τ(M, θ, ξ)` (Simon Ch. 6, 2.17 and 3.2(2),
pp. 138, 146).**  Write `Φ(s, x) = (s, x) ∈ ℝ^{P+1}` and `π(y) = (y₁, …, y_P)`, and assume the
product formula `H^{m+1}⌞{π ∈ A} = Φ_#(L¹ × Hᵐ⌞A)` for every `Hᵐ`-measurable, countably
`m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for all compact `K`.  Let `(M, θ, ξ)` be a
rectifiable triple in `ℝ^P` with `θ ≥ 1` on `M`, and let `⟨α, ξ'(s, x)⟩ = ⟨β, ξ(x)⟩` whenever
`β(v) = α(e₀, (0, v₁), …, (0, vₘ))`.  If `θ(π y) ⟨η(y), ξ'(y)⟩` is `H^{m+1}`-integrable on
`M̃ = {y : π y ∈ M, y₀ ∈ (0, 1)}` and `φ(s)(x)(v) = η(s, x)(e₀, (0, v₁), …, (0, vₘ))` for
`s ∈ [0, 1]`, then `τ(M̃, θ ∘ π, ξ')(η) = ∫₀¹ τ(M, θ, ξ)(φ(s)) ds`.  As `θ ≥ 1`, `M` has locally
finite `Hᵐ`-measure, so `H^{m+1}⌞M̃ = Φ_#(L¹⌞(0, 1) × Hᵐ⌞M)` and Fubini applies. -/
theorem Submission.iwl_cr_ip_slice_formula : ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m) (ξ' : Eucl (P + 1) → NVector (Eucl (P + 1)) (m + 1)), IsRectifiableTriple (univ : Set (Eucl P)) m M θ ξ → (∀ x ∈ M, 1 ≤ θ x) → (∀ (s : ℝ) (x : Eucl P) (α : Covector (Eucl (P + 1)) (m + 1)) (β : Covector (Eucl P) m), (∀ v : Fin m → Eucl P, β v = α (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → ξ' ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) α = ξ x β) → ∀ (η : DifferentialForm (Eucl (P + 1)) (m + 1)) (φ : ℝ → DifferentialForm (Eucl P) m), IntegrableOn (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) * ξ' y (η y)) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (μHE[m + 1] : Measure (Eucl (P + 1))) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), φ s x v = η ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → tauAction (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ξ' η = ∫ s in (0 : ℝ)..1, tauAction m M θ ξ (φ s) := by
  intro P m hMP M θ ξ ξ' hT hθ1 hchar η φ hint hφ
  -- Step 1: `Hᵐ(M ∩ K) ≤ ∫_{M ∩ K} |θ| dHᵐ < ∞` for every compact `K`, since `θ ≥ 1` on `M`.
  have hlf : ∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞ := by
    intro K hK
    have hI := hT.integrableOn K hK (subset_univ K)
    have hnm : NullMeasurableSet (M ∩ K) (μHE[m] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet
    calc (μHE[m] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, 1 ∂(μHE[m] : Measure (Eucl P)) := by
          rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[m] : Measure (Eucl P)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hnm] with x hx
          rw [← ofReal_norm, ENNReal.one_le_ofReal, Real.norm_eq_abs]
          exact (hθ1 x hx.1).trans (le_abs_self _)
      _ < ∞ := hI.2
  -- So the product formula applies to `M`, and `Hᵐ⌞M` is finite on compacts, hence σ-finite.
  have hS := hMP M hT.nullMeasurableSet hT.countablyRectifiable hlf
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hlf K hK⟩
  -- `Φ(s, x) = (s, x)` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}` with inverse `y ↦ (y₀, π y)`,
  -- hence a measurable embedding.
  let Φh : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0,
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      left_inv := fun p => by
        rcases p with ⟨s, x⟩
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
          ContinuousLinearEquiv.symm_apply_apply]
      continuous_toFun := by
        refine (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_
        exact Continuous.finCons continuous_fst
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ ?_
        · exact (continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
        · refine (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_
          exact continuous_pi fun i =>
            (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous }
  have hΦm : MeasurableEmbedding (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := Φh.measurableEmbedding
  -- Step 2: `H^{m+1}⌞M̃ = Φ_#(L¹⌞(0, 1) × Hᵐ⌞M)`, restricting the product formula for `M` to the
  -- open slab `{y₀ ∈ (0, 1)}`, whose preimage under `Φ` is `(0, 1) × ℝ^P`.
  have hOm : MeasurableSet {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage
      ((continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous).measurable
  have hpre : (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ⁻¹'
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} = Ioo (0 : ℝ) 1 ×ˢ univ := by
    ext ⟨s, x⟩
    simp only [mem_preimage, Set.mem_ofPred_eq, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero,
      mem_prod, mem_univ, and_true]
  have hset : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
      EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} ∩
        {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M} := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_inter_iff]
    exact and_comm
  have hMt : (μHE[m + 1] : Measure (Eucl (P + 1))).restrict
      {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
        (((volume : Measure ℝ).restrict (Ioo 0 1)).prod ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    rw [hset, ← Measure.restrict_restrict hOm, hS, Measure.restrict_map hΦm.measurable hOm, hpre,
      ← Measure.prod_restrict, Measure.restrict_univ]
  -- Step 4: the integrand composed with `Φ` is integrable for `L¹⌞(0, 1) × Hᵐ⌞M`.
  have hint' := hint
  rw [IntegrableOn, hMt, hΦm.integrable_map_iff] at hint'
  -- Steps 3, 5 and 7: transport the integral along `Φ`, apply Fubini, and write `∫₀¹` as the
  -- set integral over `(0, 1]`, equivalently over `(0, 1)`.
  simp only [tauAction]
  rw [hMt, hΦm.integral_map, integral_prod, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  · -- Step 6: for `s ∈ (0, 1)`, `π(Φ(s, x)) = x` and `⟨η(Φ(s, x)), ξ'(Φ(s, x))⟩ = ⟨φ(s)(x), ξ(x)⟩`.
    refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [hchar s x _ _ (fun v => hφ s (Ioo_subset_Icc_self hs) x v)]
  · exact hint'
/-- Cylinders over null-measurable sets: let `π(y) = (y_1, …, y_P)` for `y ∈ ℝ^{P+1}`.  If
`π⁻¹(N)` is `H^{m+1}`-null for every `Hᵐ`-null `N ⊆ ℝ^P`, then `π⁻¹(M)` is `H^{m+1}`-null-measurable
for every `Hᵐ`-null-measurable `M ⊆ ℝ^P`.  `π` is continuous, hence Borel, and the hypothesis makes
it quasi-measure-preserving from `H^{m+1}` to `Hᵐ`. -/
theorem Submission.iwl_cr_ip_pt_cylinder_nullMeasurableSet :
    ∀ (P m : ℕ), (∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) →
      ∀ M : Set (Eucl P), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) →
        NullMeasurableSet {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M}
          (μHE[m + 1] : Measure (Eucl (P + 1))) := by
  intro P m hNT M hM
  -- `π = equiv_P⁻¹ ∘ Fin.tail ∘ equiv_{P+1}` is continuous, hence measurable.
  have hπm : Measurable (fun y : Eucl (P + 1) =>
      (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) := by
    refine ((EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_).measurable
    exact continuous_pi fun i =>
      (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
  -- The hypothesis on measurable null sets gives `π_* H^{m+1} ≪ Hᵐ`.
  have hq : Measure.QuasiMeasurePreserving (fun y : Eucl (P + 1) =>
      (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      (μHE[m + 1] : Measure (Eucl (P + 1))) (μHE[m] : Measure (Eucl P)) := by
    refine ⟨hπm, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
    rw [Measure.map_apply hπm hs]
    exact hNT s hs0
  exact hM.preimage hq
/-- Cylinders over countably `m`-rectifiable sets: if `π(y) = (y_1, …, y_P)` pulls
`Hᵐ`-null sets of `ℝ^P` back to `H^{m+1}`-null sets of `ℝ^{P+1}`, then for countably
`m`-rectifiable `M ⊆ ℝ^P` the cylinder `{y : π(y) ∈ M}` is countably `(m+1)`-rectifiable,
parametrized by `G_j(u) = (u_0, F_j(u_1, …, u_m))`. -/
theorem Submission.iwl_cr_ip_pt_cylinder_countablyRectifiable : ∀ (P m : ℕ), (∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) → ∀ M : Set (Eucl P), CountablyRectifiable m M → CountablyRectifiable (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M} := by
  intro P m hNT M hM
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 1: the continuous linear maps `hd u = u_0`, `tl u = (u_1, …, u_m)` and
  -- `Ψ (a, x) = (a, x_1, …, x_P)`.
  let hd : Eucl (m + 1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) 0).comp
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  let tl : Eucl (m + 1) →L[ℝ] Eucl m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.pi fun i : Fin m =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i.succ).comp
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap)
  let Ψ : ℝ × Eucl P →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun p => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))
      map_add' := by
        intro p q
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearEquiv.apply_symm_apply]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := by
        intro c p
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearEquiv.apply_symm_apply,
          RingHom.id_apply]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  -- Step 2: the exceptional set is the cylinder over `M₀` (null by `hNT`) and
  -- `G_j = Ψ ∘ (hd, F_j ∘ tl)` is Lipschitz.
  refine ⟨{y | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M₀},
    hNT M₀ hM₀, fun j u => Ψ (hd u, F j (tl u)), fun j => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hF j
    exact ⟨_, Ψ.lipschitzWith.comp (hd.lipschitzWith.prodMk (hK.comp tl.lipschitzWith))⟩
  -- Step 3: if `π(y) = F_j(w)` then `G_j(y_0, w) = (y_0, π(y)) = y`.
  · intro y hy
    rcases hcover hy with h0 | h1
    · exact Or.inl h0
    · right
      obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
      refine mem_iUnion.mpr ⟨j, (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0) (EuclideanSpace.equiv (Fin m) ℝ w)), ?_⟩
      have h1' : hd ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0) (EuclideanSpace.equiv (Fin m) ℝ w))) =
          EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 := by
        simp [hd]
      have h2' : tl ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0) (EuclideanSpace.equiv (Fin m) ℝ w))) = w := by
        apply (EuclideanSpace.equiv (Fin m) ℝ).injective
        ext i
        simp [tl]
      show Ψ (hd _, F j (tl _)) = y
      rw [h1', h2', hw]
      show (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
        (EuclideanSpace.equiv (Fin P) ℝ ((EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))))) = y
      simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
        ContinuousLinearEquiv.symm_apply_apply]
/-- Orienting frame of the product triple `(0, 1) × M` (Simon Ch. 6, 3.2(2), used in the proof
of 8.2): if `τ₁, …, τₘ` is orthonormal in `ℝ^P`, then `(e₀, ιτ₁, …, ιτₘ)` is orthonormal in
`ℝ^{P+1}`, `ι v = (0, v)`.  In coordinates `⟨(a, u), (b, w)⟩ = a b + ⟨u, w⟩` and `e₀ = (1, 0)`. -/
theorem Submission.iwl_cr_ip_pt_frame_orthonormal :
    ∀ (P m : ℕ) (τ : Fin m → Eucl P), Orthonormal ℝ τ →
      Orthonormal ℝ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1))
        (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) := by
  intro P m τ hτ
  rw [orthonormal_iff_ite] at hτ ⊢
  -- `⟨(a, u), (b, w)⟩ = a b + ⟨u, w⟩`: split off the coordinate `0` of the sum.
  have hinner : ∀ (a b : ℝ) (u w : Eucl P),
      inner ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons a (EuclideanSpace.equiv (Fin P) ℝ u)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons b (EuclideanSpace.equiv (Fin P) ℝ w))) = a * b + inner ℝ u w := by
    intro a b u w
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  -- `e₀ = (1, 0)`, compared coordinatewise.
  have he : (EuclideanSpace.single 0 1 : Eucl (P + 1)) =
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 1 (EuclideanSpace.equiv (Fin P) ℝ 0)) := by
    apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, he, hinner]
    simp
  · simp only [Fin.cons_zero, Fin.cons_succ, he, hinner]
    simp [(Fin.succ_ne_zero j).symm]
  · simp only [Fin.cons_zero, Fin.cons_succ, he, hinner]
    simp [Fin.succ_ne_zero i]
  · -- `⟨ιτᵢ, ιτⱼ⟩ = ⟨τᵢ, τⱼ⟩` and `i.succ = j.succ ↔ i = j`.
    simp only [Fin.cons_succ, hinner, zero_mul, zero_add, Fin.succ_inj]
    exact hτ i j
/-- The product frame of `(0, 1) × M` (Simon Ch. 6, Remark 3.2(2), for `[[(0, 1)]] × τ(M, θ, ξ)`).
Write `ℝ^{P+1} = ℝ × ℝ^P` with `Φ(s, u) = (s, u₁, …, u_P)` and `π(z) = (z₁, …, z_P)`.  If `τ` is an
orthonormal family in `ℝ^P`, then `τ̃ = (e₀, Φ(0, τ₁), …, Φ(0, τ_m))` is orthonormal, its span `Q`
has dimension `m + 1`, and `Q = π⁻¹(span τ)` as sets.  In coordinates
`⟨Φ(a, u), Φ(b, w)⟩ = ab + ⟨u, w⟩` and `e₀ = Φ(1, 0)`; the generators of `Q` project into `span τ`,
and conversely `z = z₀ e₀ + ∑ᵢ cᵢ Φ(0, τᵢ)` whenever `π z = ∑ᵢ cᵢ τᵢ`. -/
theorem Submission.iwl_cr_ip_wt_product_plane :
    ∀ (P m : ℕ) (τ : Fin m → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) ∧ Module.finrank ℝ (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)))) = m + 1 ∧ ((Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1))) : Submodule ℝ (Eucl (P + 1))) : Set (Eucl (P + 1))) = {z : Eucl (P + 1) | ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z))) ∈ Submodule.span ℝ (range τ)} := by
  intro P m τ hτ
  -- Coordinates: `Φ(s, u) = (s, u₁, …, u_P)`, `e₀ = Φ(1, 0)`, `⟨Φ(a, u), Φ(b, w)⟩ = ab + ⟨u, w⟩`.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  have he₀ : (EuclideanSpace.single 0 1 : Eucl (P + 1)) = Φ 1 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Φ]
    · simp [Φ, Fin.succ_ne_zero]
  have hinner : ∀ (a b : ℝ) (u w : Eucl P), inner ℝ (Φ a u) (Φ b w) = a * b + inner ℝ u w := by
    intro a b u w
    simp only [Φ, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  set v : Fin (m + 1) → Eucl (P + 1) := (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1))
    (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) with hv
  have hv0 : v 0 = Φ 1 0 := by rw [hv, Fin.cons_zero, he₀]
  have hvs : ∀ i : Fin m, v i.succ = Φ 0 (τ i) := fun i => by rw [hv, Fin.cons_succ]
  -- `τ̃ = (Φ(1, 0), Φ(0, τ₁), …, Φ(0, τ_m))` is orthonormal, hence linearly independent.
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · rw [hv0, hinner]; simp
    · rw [hv0, hvs, hinner]; simp [(Fin.succ_ne_zero j').symm]
    · rw [hv0, hvs, hinner]; simp [Fin.succ_ne_zero i']
    · rw [hvs, hvs, hinner, (orthonormal_iff_ite.1 hτ) i' j']
      simp [Fin.succ_inj]
  refine ⟨hon, ?_, ?_⟩
  · rw [finrank_span_eq_card hon.linearIndependent, Fintype.card_fin]
  · -- The projection `π` as a linear map; `span τ̃ = π⁻¹(span τ)`.
    let πₗ : Eucl (P + 1) →ₗ[ℝ] Eucl P :=
      (EuclideanSpace.equiv (Fin P) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.funLeft ℝ ℝ Fin.succ ∘ₗ (EuclideanSpace.equiv (Fin (P + 1)) ℝ).toLinearMap)
    have hπ : ∀ z, πₗ z = (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z)) := fun z => rfl
    have hπΦ : ∀ s u, πₗ (Φ s u) = u := by
      intro s u
      rw [hπ]
      simp only [Φ, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
        ContinuousLinearEquiv.symm_apply_apply]
    have hspan : Submodule.span ℝ (range v) = (Submodule.span ℝ (range τ)).comap πₗ := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [SetLike.mem_coe, Submodule.mem_comap, hv0, hπΦ]
          exact Submodule.zero_mem _
        · simp only [SetLike.mem_coe, Submodule.mem_comap, hvs, hπΦ]
          exact Submodule.subset_span ⟨i', rfl⟩
      · intro z hz
        rw [Submodule.mem_comap, Submodule.mem_span_range_iff_exists_fun] at hz
        obtain ⟨c, hc⟩ := hz
        -- `z = Φ(z₀, π z)` and `Φ` is linear, so `z = z₀ e₀ + ∑ᵢ cᵢ Φ(0, τᵢ)`.
        have hz' : z = (EuclideanSpace.equiv (Fin (P + 1)) ℝ z 0) • v 0 +
            ∑ i, c i • v i.succ := by
          have hdecomp : z = Φ (EuclideanSpace.equiv (Fin (P + 1)) ℝ z 0) (πₗ z) := by
            apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
            simp only [Φ, hπ, ContinuousLinearEquiv.apply_symm_apply]
            exact (Fin.cons_self_tail _).symm
          have hlin : ∀ (a b : ℝ) (u w : Eucl P), Φ a u + Φ b w = Φ (a + b) (u + w) := by
            intro a b u w
            simp only [Φ, ← map_add]
            congr 1
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsmul : ∀ (c : ℝ) (a : ℝ) (u : Eucl P), c • Φ a u = Φ (c * a) (c • u) := by
            intro c a u
            simp only [Φ, ← map_smul]
            congr 1
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsum : ∀ (s : Finset (Fin m)) (a : Fin m → ℝ) (u : Fin m → Eucl P),
              ∑ i ∈ s, Φ (a i) (u i) = Φ (∑ i ∈ s, a i) (∑ i ∈ s, u i) := by
            intro s a u
            induction s using Finset.induction_on with
            | empty =>
              have h00 : Φ 0 0 = 0 := by
                apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
                simp only [Φ, ContinuousLinearEquiv.apply_symm_apply, map_zero]
                ext i
                refine Fin.cases ?_ (fun j => ?_) i <;> simp
              simp [h00]
            | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj,
                Finset.sum_insert hj, ih, hlin]
          rw [hv0]
          simp_rw [hvs, hsmul, hsum, hlin, mul_zero, Finset.sum_const_zero, mul_one, smul_zero,
            zero_add, add_zero, hc]
          exact hdecomp
        rw [hz']
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, rfl⟩))
    rw [hspan]
    rfl
/-- Fubini on the product plane `π⁻¹(T)`, `T = span τ`, for compactly supported continuous `f`
(Simon Ch. 6, 3.2(2), product with an interval).  Write `Φ′(s, u) = (s, u) ∈ ℝ^{P+1}` and
`π(y) = (y₁, …, y_P)`, and assume the product formula (MP) `H^{m+1} ⌞ π⁻¹(A) = Φ′_#(L¹ × Hᵐ ⌞ A)`
for every `Hᵐ`-measurable, countably `m`-rectifiable, locally `Hᵐ`-finite `A ⊆ ℝ^P`.  Then for an
orthonormal `τ`, `∫_{π⁻¹(T)} f dH^{m+1} = ∫_ℝ ∫_T f(Φ′(σ, w)) dHᵐ(w) dσ`.
`T` is closed, has dimension `m`, is the range of the Lipschitz map `u ↦ ∑ uᵢ τᵢ`, and `Hᵐ ⌞ T` is
regular, so (MP) applies to `A = T`.  Change variables along the homeomorphism
`Φ′ : ℝ × ℝ^P ≃ ℝ^{P+1}` and apply Fubini to the compactly supported continuous `f ∘ Φ′`. -/
theorem Submission.iwl_cr_ip_wt_plane_fubini :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ τ : Fin m → Eucl P, Orthonormal ℝ τ → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∫ z in {z : Eucl (P + 1) | ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z))) ∈ Submodule.span ℝ (range τ)}, f z ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫ σ : ℝ, ∫ w in (Submodule.span ℝ (range τ) : Set (Eucl P)), f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) ∂(μHE[m] : Measure (Eucl P)) := by
  intro P m hMP τ hτ f hfc hfcs
  -- Coordinates `Φ(s, u) = (s, u)` and `π(y) = (y₁, …, y_P)`.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- `Φ′ = Φ.uncurry` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}` with inverse `y ↦ (y₀, π y)`.
  let e : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => Φ p.1 p.2
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0, π y)
      left_inv := fun p => by
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply]
        exact Fin.cons_self_tail _
      continuous_toFun := hΦc
      continuous_invFun := by
        refine Continuous.prodMk ((continuous_apply 0).comp
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) ?_
        exact (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp
          (continuous_pi fun i : Fin P => (continuous_apply i.succ).comp
            (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) }
  have hemb : MeasurableEmbedding (fun p : ℝ × Eucl P => Φ p.1 p.2) := e.measurableEmbedding
  -- The plane `T = span τ` is `Hᵐ`-measurable, countably `m`-rectifiable and locally `Hᵐ`-finite.
  set T : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ) with hT
  have hfinT : Module.finrank ℝ T = m := by
    rw [hT, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  have hTmeas : MeasurableSet (T : Set (Eucl P)) := T.closed_of_finiteDimensional.measurableSet
  have hTrect : CountablyRectifiable m (T : Set (Eucl P)) := by
    let Λₗ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Eucl P :=
      Fintype.linearCombination ℝ τ ∘ₗ (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap
    let Λ : EuclideanSpace ℝ (Fin m) →L[ℝ] Eucl P := LinearMap.toContinuousLinearMap Λₗ
    have hrange : range Λ = (T : Set (Eucl P)) := by
      ext v
      simp only [Λ, LinearMap.coe_toContinuousLinearMap', mem_range, SetLike.mem_coe, hT,
        Submodule.mem_span_range_iff_exists_fun]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨fun i => u i, by simp [Λₗ, Fintype.linearCombination_apply]⟩
      · rintro ⟨c, rfl⟩
        exact ⟨(EuclideanSpace.equiv (Fin m) ℝ).symm c, by
          simp [Λₗ, Fintype.linearCombination_apply]⟩
    rw [← hrange]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range Λ.lipschitzWith
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Eucl P) hfinT
  have hTfin : ∀ K : Set (Eucl P), IsCompact K →
      (μHE[m] : Measure (Eucl P)) ((T : Set (Eucl P)) ∩ K) < ∞ := by
    intro K hK
    rw [inter_comm, ← Measure.restrict_apply hK.measurableSet]
    exact hK.measure_lt_top
  -- (MP) for `A = T`.
  have hMPT : (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {z | π z ∈ T} =
      Measure.map (fun p : ℝ × Eucl P => Φ p.1 p.2)
        ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict (T : Set (Eucl P)))) :=
    hMP (T : Set (Eucl P)) hTmeas.nullMeasurableSet hTrect hTfin
  -- Change of variables along `Φ′`, then Fubini for the integrable `f ∘ Φ′`.
  have hint : Integrable (fun p : ℝ × Eucl P => f (Φ p.1 p.2))
      ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict (T : Set (Eucl P)))) :=
    (hfc.comp e.continuous).integrable_of_hasCompactSupport (hfcs.comp_homeomorph e)
  show ∫ z, f z ∂((μHE[m + 1] : Measure (Eucl (P + 1))).restrict {z | π z ∈ T}) = _
  rw [hMPT, hemb.integral_map, integral_prod _ hint]
/-- Simon Ch. 6, 3.2(2) (product with an interval), Hausdorff measure on `(0,1) × M`.  Write
`Φ(s, u) = (s, u)`, `π(y) = (y₁, …, y_P)` and assume `(MP)`: `H^{m+1} ⌞ π⁻¹(A) = Φ_# (L¹ ⊗ Hᵐ ⌞ A)`
for every `Hᵐ`-measurable, countably `m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for compact
`K`.  Then every such `M` has `H^{m+1} ⌞ {π(y) ∈ M, y₀ ∈ (0,1)} = Φ_# ((L¹ ⌞ (0,1)) ⊗ Hᵐ ⌞ M)`:
restrict `(MP)` for `A = M` to the open slab `O = {y₀ ∈ (0,1)}`, use `Φ⁻¹(O) = (0,1) × ℝ^P`, and
split the restricted product, `Hᵐ ⌞ M` being finite on compact sets, hence σ-finite. -/
theorem Submission.iwl_cr_ip_wt_product_measure :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ M : Set (Eucl P), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} = Measure.map (fun p : ℝ × Eucl P => ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))) (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod ((μHE[m] : Measure (Eucl P)).restrict M)) := by
  intro P m hMP M hMmeas hMrect hMfin
  -- `Φ′(s, u) = (s, u)` is continuous, hence measurable.
  have hΦc : Continuous fun p : ℝ × Eucl P =>
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)) :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- The open slab `O = {y₀ ∈ (0,1)}`: `M̃ = O ∩ π⁻¹(M)` and `Φ′⁻¹(O) = (0,1) × ℝ^P`.
  let O : Set (Eucl (P + 1)) := {y | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}
  have hO : MeasurableSet O :=
    (isOpen_Ioo.preimage ((continuous_apply 0).comp
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous)).measurableSet
  have hset : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      O ∩ {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M} := by
    ext y
    exact and_comm
  have hpre : (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ⁻¹' O =
      Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Eucl P)) := by
    ext p
    simp [O]
  -- `Hᵐ ⌞ M` is finite on compact sets, hence σ-finite.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hMfin K hK⟩
  -- Restrict `(MP)` for `A = M` to `O`, pull back along `Φ′` and split the restricted product.
  rw [hset, ← Measure.restrict_restrict hO, hMP M hMmeas hMrect hMfin,
    Measure.restrict_map hΦc.measurable hO, hpre, ← Measure.prod_restrict, Measure.restrict_univ]
/-- Change of variables under Simon's blow-up `η = η_{x,r}`, `η(z) = r⁻¹(z − x)` (Ch. 3, §1, p. 71),
as used for the locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)): for
`r > 0`, every set `S` and every real function `g`, `∫_{η(S)} g dHⁿ = r⁻ⁿ ∫_S g ∘ η dHⁿ`.
`η` is a homeomorphism (inverse `w ↦ x + r w`) and `η⁻¹(F) = x + r F`, so `Hⁿ(η⁻¹ F) = rⁿ Hⁿ(F)`
by translation invariance and `n`-homogeneity of `Hⁿ`.  Hence `η_# Hⁿ = rⁿ Hⁿ`, and the change of
variables along the measurable embedding `η` needs no integrability. -/
theorem Submission.fiw_tl_blowup_setIntegral :
    ∀ (P n : ℕ) (x : Eucl P) (r : ℝ) (S : Set (Eucl P)) (g : Eucl P → ℝ), 0 < r → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, g y ∂(μHE[n] : Measure (Eucl P)) = (r ^ n)⁻¹ * ∫ z in S, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n x r S g hr
  set η : Eucl P → Eucl P := Poincare.SimonGMT.Chapter03.blowUpMap x r
  have hηapp : ∀ z, η z = r⁻¹ • (z - x) := fun _ => rfl
  -- `η` is a homeomorphism with inverse `w ↦ x + r • w`.
  let e : Eucl P ≃ₜ Eucl P :=
    { toFun := η
      invFun := fun w => x + r • w
      left_inv := fun z => by simp [hηapp, smul_smul, hr.ne']
      right_inv := fun w => by simp [hηapp, smul_smul, hr.ne']
      continuous_toFun := by
        show Continuous fun z : Eucl P => r⁻¹ • (z - x)
        fun_prop
      continuous_invFun := by fun_prop }
  have hemb : MeasurableEmbedding η := e.measurableEmbedding
  have hinj : Function.Injective η := e.injective
  -- `η⁻¹(F) = x + r • F`, so `Hⁿ(η⁻¹ F) = ‖r‖₊ⁿ Hⁿ(F)` for every set `F`.
  have hpre : ∀ F : Set (Eucl P), (μHE[n] : Measure (Eucl P)) (η ⁻¹' F) =
      ‖r‖₊ ^ n • (μHE[n] : Measure (Eucl P)) F := by
    intro F
    have hF : η ⁻¹' F = (fun z => z + -x) ⁻¹' ((fun w => r⁻¹ • w) ⁻¹' F) := by
      ext z
      simp only [mem_preimage, hηapp, sub_eq_add_neg]
    rw [hF, measure_preimage_add_right, preimage_smul_inv₀ hr.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne']
  -- Push-forward: `η_# Hⁿ = ‖r‖₊ⁿ Hⁿ`.
  have hmap : Measure.map η (μHE[n] : Measure (Eucl P)) =
      (‖r‖₊ ^ n) • (μHE[n] : Measure (Eucl P)) := by
    ext F hF
    rw [Measure.map_apply hemb.measurable hF, Measure.smul_apply, hpre]
  -- Change of variables along the measurable embedding `η` (no integrability needed).
  have h := hemb.setIntegral_map (μ := (μHE[n] : Measure (Eucl P))) g (η '' S)
  rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure, preimage_image_eq S hinj,
    NNReal.smul_def, smul_eq_mul] at h
  have hc : ((‖r‖₊ ^ n : ℝ≥0) : ℝ) = r ^ n := by
    rw [NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg hr.le]
  rw [hc] at h
  rw [← h, inv_mul_cancel_left₀ (pow_ne_zero n hr.ne')]

/-- Uniform mass bound for the blow-ups `η_r(M)`, `η_r = η_{x,r}` (Ch. 3, §1, p. 71), at a point `x`
with a weighted approximate tangent plane `T` (Ch. 3, 1.7), as used for the product with an interval
(Ch. 6, 3.2(2)): for every `R` there is `B` such that for all small `r > 0`, every `g` with `|g| ≤ C`
vanishing off `B̄(0, R)` satisfies `|∫_{η_r(M)} g(w) θ(x + r w) dHᵐ(w)| ≤ C B`.  Compare with the
cut-off `g₀ = max(0, min(1, R + 1 − ‖w‖)) ∈ C_c`: `|g| ≤ C g₀`, `θ ≥ 0` on `M`, and by the change of
variables `fiw_tl_blowup_setIntegral` the `g₀`-integral tends to `θ(x) ∫_T g₀ dHᵐ < B`. -/
theorem Submission.iwl_cr_ip_wt_blowup_mass_bound :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (T : Submodule ℝ (Eucl P)), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → HasWeightedApproximateTangentSpaceAt m M θ x T → ∀ R : ℝ, ∃ B : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (C : ℝ) (g : Eucl P → ℝ), (∀ w, |g w| ≤ C) → (∀ w, R < ‖w‖ → g w = 0) → |∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, g w * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))| ≤ C * B := by
  intro P m M θ x T hMmeas hθnn hθint hTan R
  -- The cut-off `g₀ = max 0 (min 1 (R + 1 - ‖w‖))`.
  let g₀ : Eucl P → ℝ := fun w => max 0 (min 1 (R + 1 - ‖w‖))
  have hg₀c : Continuous g₀ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hg₀0 : ∀ w, R + 1 < ‖w‖ → g₀ w = 0 := by
    intro w hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  have hg₀cs : HasCompactSupport g₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) (R + 1)) (fun w hw => ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hw
    exact hg₀0 w hw
  have hg₀nn : ∀ w, 0 ≤ g₀ w := fun w => le_max_left _ _
  have hg₀le : ∀ w, g₀ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hg₀1 : ∀ w, ‖w‖ ≤ R → g₀ w = 1 := by
    intro w hw
    show max 0 (min 1 (R + 1 - ‖w‖)) = 1
    rw [min_eq_left (by linarith)]
    exact max_eq_right zero_le_one
  let G₀ : CompactlySupportedContinuousMap (Eucl P) ℝ := ⟨⟨g₀, hg₀c⟩, hg₀cs⟩
  have hlim := hTan.2 G₀
  refine ⟨θ x * ∫ y in (T : Set (Eucl P)), g₀ y ∂(μHE[m] : Measure (Eucl P)) + 1, ?_⟩
  filter_upwards [hlim.eventually_lt_const (lt_add_one _), self_mem_nhdsWithin] with r hrB hr C g hgC hg0
  have hr0 : (0 : ℝ) < r := hr
  -- `θ` is a.e. strongly measurable and a.e. nonnegative for `Hᵐ ⌞ M`.
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  have hθpos : ∀ᵐ u ∂((μHE[m] : Measure (Eucl P)).restrict M), 0 ≤ θ u :=
    (ae_restrict_mem₀ hMmeas).mono fun u hu => hθnn u hu
  -- Undo the blow-up for any integrand.
  have hcov : ∀ h : Eucl P → ℝ, ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      h w * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)) = (r ^ m)⁻¹ * ∫ u in M,
        h (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u ∂(μHE[m] : Measure (Eucl P)) := by
    intro h
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => h w * θ (x + r • w)) hr0]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul,
      add_sub_cancel]
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  have hηnorm : ∀ u, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r u‖ = r⁻¹ * ‖u - x‖ := by
    intro u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr0]
  -- Integrability of `u ↦ g₀(η u) θ(u)` on `M`.
  have hint₀ : Integrable (fun u => g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u)
      ((μHE[m] : Measure (Eucl P)).restrict M) := by
    refine Integrable.mono' (g := (closedBall x (r * (R + 1))).indicator fun u => |θ u|) ?_
      ((hg₀c.comp hηc).aestronglyMeasurable.mul hθae) (Filter.Eventually.of_forall fun u => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact (hθint _ (isCompact_closedBall x (r * (R + 1)))).norm.congr
        (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
    · by_cases hu : u ∈ closedBall x (r * (R + 1))
      · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ u), Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _)
          ((abs_of_nonneg (hg₀nn _)).trans_le (hg₀le _))
      · rw [indicator_of_notMem hu, hg₀0, zero_mul, norm_zero]
        rw [mem_closedBall, dist_eq_norm, not_le] at hu
        rw [hηnorm, lt_inv_mul_iff₀ hr0]
        exact hu
  -- `C ≥ 0`, and `|g(η u)| θ(u) ≤ C g₀(η u) θ(u)` on `M`.
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have hpt : ∀ w, |g w| ≤ C * g₀ w := by
    intro w
    by_cases hw : ‖w‖ ≤ R
    · rw [hg₀1 w hw, mul_one]
      exact hgC w
    · rw [hg0 w (not_le.1 hw), abs_zero]
      exact mul_nonneg hC (hg₀nn w)
  have hkey : |∫ u in M, g (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
      ∂(μHE[m] : Measure (Eucl P))| ≤
      C * ∫ u in M, g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P)) := by
    rw [← integral_const_mul]
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
      (hint₀.const_mul C) ?_
    filter_upwards [hθpos] with u hu
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hpt _) hu
  rw [hcov g, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr0 m))]
  have hb := hcov g₀
  calc (r ^ m)⁻¹ * |∫ u in M, g (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P))|
      ≤ (r ^ m)⁻¹ * (C * ∫ u in M, g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P))) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 (pow_nonneg hr0.le m))
    _ = C * ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, g₀ w * θ (x + r • w)
        ∂(μHE[m] : Measure (Eucl P)) := by rw [hb]; ring
    _ ≤ C * (θ x * ∫ y in (T : Set (Eucl P)), g₀ y ∂(μHE[m] : Measure (Eucl P)) + 1) :=
        mul_le_mul_of_nonneg_left hrB.le hC
/-- Blow-ups of the product `(0, 1) × M ⊆ ℝ^{P+1}` slice into blow-ups of `M` (Simon Ch. 6, 3.2(2)).
With `Φ(s, u) = (s, u)`, `π(y) = (y₁, …, y_P)`, `y* = Φ(s₀, x)` and `r > 0`, and assuming the
product formula `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)` for countably `m`-rectifiable `A`:
`∫_{η_{y*,r}((0,1) × M)} f(z) θ(π(y* + r z)) dH^{m+1}(z)
  = ∫_{(−s₀/r, (1−s₀)/r]} ∫_{η_{x,r}(M)} f(Φ(σ, w)) θ(x + r w) dHᵐ(w) dσ`.
Undo both blow-ups (`fiw_tl_blowup_setIntegral`), pass to `(L¹⌞(0,1)) ⊗ Hᵐ⌞M`
(`iwl_cr_ip_wt_product_measure`), apply Fubini and substitute `s = s₀ + r σ`. -/
theorem Submission.iwl_cr_ip_wt_slice_identity :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (s₀ : ℝ), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) r '' {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}, f z * θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ (((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) + r • z)))) ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫ σ : ℝ, (Ioc (-s₀ / r) ((1 - s₀) / r)).indicator (fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))) σ := by
  intro P m hMP M θ x s₀ hMmeas hMrect hMfin hθint f hfc hfcs r hr
  -- Coordinates.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hπΦ : ∀ s u, π (Φ s u) = u := by
    intro s u
    simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  have hΦsub : ∀ s u s' u', Φ s u - Φ s' u' = Φ (s - s') (u - u') := by
    intro s u s' u'
    simp only [Φ, ← map_sub]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hΦsmul : ∀ (c s : ℝ) (u : Eucl P), c • Φ s u = Φ (c * s) (c • u) := by
    intro c s u
    simp only [Φ, ← map_smul]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hnorm : ∀ (s : ℝ) (u : Eucl P), ‖u‖ ≤ ‖Φ s u‖ := by
    intro s u
    have h : ‖Φ s u‖ ^ 2 = s ^ 2 + ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    exact le_of_sq_le_sq (by rw [h]; nlinarith [sq_nonneg s]) (norm_nonneg _)
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  let e : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => Φ p.1 p.2
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0, π y)
      left_inv := fun p => by
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply]
        exact Fin.cons_self_tail _
      continuous_toFun := hΦc
      continuous_invFun := by
        refine Continuous.prodMk ((continuous_apply 0).comp
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) ?_
        exact (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp
          (continuous_pi fun i : Fin P => (continuous_apply i.succ).comp
            (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) }
  have hemb : MeasurableEmbedding (fun p : ℝ × Eucl P => Φ p.1 p.2) := e.measurableEmbedding
  -- Support radius and sup bound of `f`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : Eucl (P + 1), f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz => ?_⟩
    simpa using hR (subset_tsupport _ hz)
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C := hfc.bounded_above_of_compact_support hfcs
  -- `ν = Hᵐ ⌞ M` is finite on compacts (so σ-finite) and `θ` is a.e. strongly measurable for it.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hMfin K hK⟩
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  -- Blow-up maps.
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  have hηnorm : ∀ u, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r u‖ = r⁻¹ * ‖u - x‖ := by
    intro u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr]
  -- Blow-ups of the product are products of blow-ups.
  have hprod : ∀ s u, Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ s u) =
      Φ (r⁻¹ * (s - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r u) := by
    intro s u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, hΦsub, hΦsmul]
  -- The integrand on the product and its integrability.
  let G : ℝ × Eucl P → ℝ := fun p =>
    f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) * θ p.2
  have hGint : Integrable G (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
      ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    have hbint : Integrable ((closedBall x (r * R)).indicator fun u => Cf * |θ u|)
        ((μHE[m] : Measure (Eucl P)).restrict M) := by
      rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact ((hθint _ (isCompact_closedBall x (r * R))).norm.const_mul Cf).congr
        (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
    refine Integrable.mono' (hbint.comp_snd _) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul ?_ hθae.comp_snd
      refine Continuous.aestronglyMeasurable ?_
      exact hfc.comp (hΦc.comp
        ((continuous_const.mul (continuous_fst.sub continuous_const)).prodMk
          (hηc.comp continuous_snd)))
    · show ‖G p‖ ≤ (closedBall x (r * R)).indicator (fun u => Cf * |θ u|) p.2
      by_cases hu : p.2 ∈ closedBall x (r * R)
      · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ p.2)]
        exact mul_le_mul_of_nonneg_right (hCf _) (abs_nonneg _)
      · rw [indicator_of_notMem hu]
        have hf0 :
            f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) = 0 := by
          by_contra h
          apply hu
          have h1 := (hnorm _ _).trans (hR _ h)
          rw [hηnorm, inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          exact h1
        show ‖f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) * θ p.2‖ ≤ 0
        rw [hf0, zero_mul, norm_zero]
  -- Undo the blow-up in `ℝ^{P+1}` and pass to the product measure.
  have hL1 : ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r ''
        {y : Eucl (P + 1) | π y ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1},
        f z * θ (π (Φ s₀ x + r • z)) ∂(μHE[m + 1] : Measure (Eucl (P + 1))) =
      (r ^ (m + 1))⁻¹ * ∫ p, G p ∂(((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
        ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    rw [Submission.fiw_tl_blowup_setIntegral (P + 1) (m + 1) (Φ s₀ x) r _
      (fun z => f z * θ (π (Φ s₀ x + r • z))) hr]
    congr 1
    have hmeas := Submission.iwl_cr_ip_wt_product_measure P m hMP M hMmeas hMrect hMfin
    show ∫ w, f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w) *
        θ (π (Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w))
        ∂((μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y : Eucl (P + 1) | π y ∈ M ∧
            EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}) = _
    rw [hmeas, hemb.integral_map]
    have hback : ∀ w, Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w = w := by
      intro w
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
        one_smul, add_sub_cancel]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ p.1 p.2)) *
      θ (π (Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ p.1 p.2))) = G p
    rw [hback, hπΦ, hprod]
  -- Fubini and the interval.
  let H : ℝ → ℝ := fun s => ∫ u in M, G (s, u) ∂(μHE[m] : Measure (Eucl P))
  have hL2 : ∫ p, G p ∂(((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
        ((μHE[m] : Measure (Eucl P)).restrict M)) = ∫ s in (0 : ℝ)..1, H s := by
    rw [integral_prod _ hGint, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  -- Substitution `s = r σ + s₀`.
  have hsub : ∫ σ in (-s₀ / r)..((1 - s₀) / r), H (r * σ + s₀) = r⁻¹ * ∫ s in (0 : ℝ)..1, H s := by
    rw [intervalIntegral.integral_comp_mul_add H hr.ne' s₀, smul_eq_mul]
    congr 3
    · field_simp
      ring
    · field_simp
      ring
  -- The slices: `H (r σ + s₀) = rᵐ · a σ`.
  have hslice : ∀ σ : ℝ, H (r * σ + s₀) =
      r ^ m * ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
        f (Φ σ w) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)) := by
    intro σ
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => f (Φ σ w) * θ (x + r • w)) hr,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hr.ne'), one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hσ : r⁻¹ * (r * σ + s₀ - s₀) = σ := by
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    simp only [G, hσ, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
      one_smul, add_sub_cancel]
  -- Assemble.
  have hab : -s₀ / r ≤ (1 - s₀) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  rw [hL1, hL2, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hab]
  have hsub' := hsub
  simp only [hslice, intervalIntegral.integral_const_mul] at hsub'
  -- `hsub' : r ^ m * ∫ a = r⁻¹ * ∫₀¹ H`
  have hrm : (r ^ (m + 1))⁻¹ = (r ^ m)⁻¹ * r⁻¹ := by rw [pow_succ, mul_inv]
  rw [hrm, mul_assoc, ← hsub', ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hr.ne'), one_mul]
/-- Continuity in `σ` of the blown-up slice integrals (Simon Ch. 6, 3.2(2), product with an
interval): if `θ` is `Hᵐ`-integrable on `M ∩ K` for every compact `K`, `f ∈ C_c(ℝ^{P+1})` and
`r > 0`, then `σ ↦ ∫_{η(M)} f(σ, w) θ(x + r w) dHᵐ(w)` is continuous, `η = η_{x,r}`.  Undoing the
blow-up (`fiw_tl_blowup_setIntegral`) gives `r⁻ᵐ ∫_M f(σ, η u) θ(u) dHᵐ(u)`, continuous by dominated
convergence with the `σ`-independent bound `sup |f| · |θ| · 1_{B̄(x, r R)}`, `spt f ⊆ B̄(0, R)`. -/
theorem Submission.iwl_cr_ip_wt_slice_continuous :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P), (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))) := by
  intro P m M θ x hθint f hfc hfcs r hr
  -- Coordinates `Φ(s, u) = (s, u₁, …, u_P)`, with `‖u‖ ≤ ‖Φ(s, u)‖`.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  have hnorm : ∀ (s : ℝ) (u : Eucl P), ‖u‖ ≤ ‖Φ s u‖ := by
    intro s u
    have h : ‖Φ s u‖ ^ 2 = s ^ 2 + ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    exact le_of_sq_le_sq (by rw [h]; nlinarith [sq_nonneg s]) (norm_nonneg _)
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- Support radius and sup bound of `f`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : Eucl (P + 1), f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz => ?_⟩
    simpa using hR (subset_tsupport _ hz)
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C := hfc.bounded_above_of_compact_support hfcs
  -- `θ` is a.e. strongly measurable for `Hᵐ ⌞ M` (exhaust `M` by the compact balls `B̄(0, n)`).
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  -- Undo the blow-up: the slice integral is `r⁻ᵐ ∫_M f(Φ(σ, η u)) θ(u) dHᵐ(u)`.
  have hcov : ∀ σ : ℝ, ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f (Φ σ w) * θ (x + r • w)
      ∂(μHE[m] : Measure (Eucl P)) = (r ^ m)⁻¹ * ∫ u in M,
        f (Φ σ (Poincare.SimonGMT.Chapter03.blowUpMap x r u)) * θ u ∂(μHE[m] : Measure (Eucl P)) := by
    intro σ
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => f (Φ σ w) * θ (x + r • w)) hr]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
      add_sub_cancel]
  show Continuous fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
    f (Φ σ w) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))
  simp_rw [hcov]
  refine continuous_const.mul ?_
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  -- Dominated convergence with the `σ`-independent bound `1_{B̄(x, r R)} · Cf · |θ|`.
  refine continuous_of_dominated
    (bound := (closedBall x (r * R)).indicator fun u => Cf * |θ u|) (fun σ => ?_) (fun σ => ?_) ?_ ?_
  · exact ((hfc.comp (hΦc.comp (continuous_const.prodMk hηc))).aestronglyMeasurable).mul hθae
  · refine Filter.Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ closedBall x (r * R)
    · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ u)]
      exact mul_le_mul_of_nonneg_right (hCf _) (abs_nonneg _)
    · rw [indicator_of_notMem hu]
      have hf0 : f (Φ σ (Poincare.SimonGMT.Chapter03.blowUpMap x r u)) = 0 := by
        by_contra h
        apply hu
        have h1 := (hnorm σ _).trans (hR _ h)
        rw [mem_closedBall, dist_eq_norm]
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hr] at h1
        rw [inv_mul_le_iff₀ hr] at h1
        exact h1
      rw [hf0, zero_mul, norm_zero]
  · rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact ((hθint _ (isCompact_closedBall x (r * R))).norm.const_mul Cf).congr
      (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (hfc.comp (hΦc.comp (continuous_id.prodMk continuous_const))).mul continuous_const

/-- Simon Ch. 3, 1.7 for the product of the unit interval with `(M, θ)`: if `span τ` is a weighted
approximate tangent space of `(M, θ)` at `x`, then `span (e₀, ιτ)` is one of
`(M̃, θ ∘ π)`, `M̃ = {y : π y ∈ M, y₀ ∈ (0, 1)}`, at `Φ(s₀, x)` for `0 < s₀ < 1`.
By the slice identity the blow-up integrals at `Φ(s₀, x)` are
`∫_ℝ 1_{(-s₀/r, (1-s₀)/r]}(σ) a_r(σ) dσ`, where `a_r(σ)` is the blow-up integral of `(M, θ)` at `x`
against `f(Φ(σ, ·))`.  Dominated convergence in `σ` (uniform blow-up mass bound, continuity in
`σ`) and Fubini on the plane `π⁻¹(span τ) = span (e₀, ιτ)` give the limit
`θ(x) ∫_{span (e₀, ιτ)} f dH^{m+1}`. -/
theorem Submission.iwl_cr_ip_product_weighted_tangent :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (τ : Fin m → Eucl P) (s₀ : ℝ), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → Orthonormal ℝ τ → HasWeightedApproximateTangentSpaceAt m M θ x (Submodule.span ℝ (range τ)) → s₀ ∈ Ioo (0 : ℝ) 1 → HasWeightedApproximateTangentSpaceAt (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)))) := by
  have h_plane := Submission.iwl_cr_ip_wt_product_plane
  have h_fubini := Submission.iwl_cr_ip_wt_plane_fubini
  have h_bound := Submission.iwl_cr_ip_wt_blowup_mass_bound
  have h_slice := Submission.iwl_cr_ip_wt_slice_identity
  have h_cont := Submission.iwl_cr_ip_wt_slice_continuous
  intro P m hMP M θ x τ s₀ hMmeas hMrect hMfin hθnn hθint hτ hT hs₀
  -- Steps 1–2 (`product_plane`): `finrank Q = m + 1` and `Q = π⁻¹(span τ)` as sets.
  obtain ⟨-, hQrank, hQset⟩ := h_plane P m τ hτ
  refine And.intro hQrank (fun f => ?_)
  have hfc : Continuous f := f.continuous
  have hfs : HasCompactSupport f := f.hasCompactSupport
  -- Coordinates: `‖Φ(σ, w)‖² = σ² + ‖w‖²`, hence `|σ| ≤ ‖Φ(σ, w)‖` and `‖w‖ ≤ ‖Φ(σ, w)‖`.
  have hnsq : ∀ (σ : ℝ) (w : Eucl P), ‖(EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))‖ ^ 2 = σ ^ 2 + ‖w‖ ^ 2 := by
    intro σ w
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp
  have hN0 : ∀ (σ : ℝ) (w : Eucl P), |σ| ≤ ‖(EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))‖ := fun σ w =>
    le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
      (by rw [hnsq, sq_abs]; nlinarith [sq_nonneg ‖w‖])
  have hN1 : ∀ (σ : ℝ) (w : Eucl P), ‖w‖ ≤ ‖(EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))‖ := fun σ w =>
    le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (by rw [hnsq]; nlinarith [sq_nonneg σ])
  -- Step 5: `f` vanishes outside `B̄(0, R)` and `|f| ≤ C`.
  obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall (0 : Eucl (P + 1))
  have hfz : ∀ z : Eucl (P + 1), R < ‖z‖ → f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => (not_le.2 hz) (mem_closedBall_zero_iff.1 (hR h))
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfs
  -- Step 15: the limit is `θ(x) ∫_ℝ ∫_{span τ} f(Φ(σ, w)) dHᵐ(w) dσ`, since
  -- `θ̃(Φ(s₀, x)) = θ(x)`, `Q = π⁻¹(span τ)` and by `plane_fubini`.
  have hθc : θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ
      ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x)))))) = θ x := by
    rw [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  beta_reduce
  rw [hθc, hQset, h_fubini P m hMP τ hτ f hfc hfs, ← integral_const_mul]
  -- Steps 7–10 (`slice_identity`): for `r > 0` the blow-up integral equals
  -- `∫_ℝ 1_{(-s₀/r, (1-s₀)/r]}(σ) a_r(σ) dσ`.
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun r : ℝ => ∫ σ : ℝ,
    (Ioc (-s₀ / r) ((1 - s₀) / r)).indicator (fun σ : ℝ =>
      ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
        f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) *
          θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))) σ) (𝓝[>] 0) _)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (h_slice P m hMP M θ x s₀ hMmeas hMrect hMfin hθint f hfc hfs r hr).symm
  -- Step 14: dominated convergence in the interval variable.
  obtain ⟨B, hB⟩ := h_bound P m M θ x (Submodule.span ℝ (range τ)) hMmeas hθnn hθint hT R
  refine tendsto_integral_filter_of_dominated_convergence
    (fun σ => (Icc (-R) R).indicator (fun _ => C * B) σ) ?_ ?_ ?_ ?_
  · -- Step 13 (`slice_continuous`): measurability in `σ`.
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (h_cont P m M θ x hθint f hfc hfs r hr).aestronglyMeasurable.indicator measurableSet_Ioc
  · -- Step 12 (`blowup_mass_bound`): `|a_r(σ)| ≤ C B`, and `a_r(σ) = 0` for `|σ| > R`.
    filter_upwards [hB] with r hr
    refine ae_of_all _ fun σ => (norm_indicator_le_norm_self _ _).trans ?_
    rw [Real.norm_eq_abs]
    by_cases hσ : σ ∈ Icc (-R) R
    · rw [indicator_of_mem hσ]
      exact hr C (fun w => f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))))
        (fun w => by rw [← Real.norm_eq_abs]; exact hC _)
        (fun w hw => hfz _ (hw.trans_le (hN1 σ w)))
    · rw [indicator_of_notMem hσ]
      have hRσ : R < |σ| := not_le.1 fun h => hσ (abs_le.1 h)
      have h0 : ∀ w : Eucl P, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) = 0 :=
        fun w => hfz _ (hRσ.trans_le (hN0 σ w))
      simpa using hr 0 (fun w => f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))))
        (fun w => by rw [h0]; simp) (fun w _ => h0 w)
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · -- Step 11: pointwise convergence from the tangent hypothesis for `f(Φ(σ, ·))`.
    refine ae_of_all _ fun σ => ?_
    have hmem : ∀ᶠ r in 𝓝[>] (0 : ℝ), σ ∈ Ioc (-s₀ / r) ((1 - s₀) / r) := by
      have hε : 0 < min s₀ (1 - s₀) / (|σ| + 1) :=
        div_pos (lt_min hs₀.1 (sub_pos.2 hs₀.2)) (by positivity)
      filter_upwards [Ioo_mem_nhdsGT hε] with r hr
      obtain ⟨hr0, hrε⟩ := hr
      have h1 : r * (|σ| + 1) < min s₀ (1 - s₀) := (lt_div_iff₀ (by positivity)).1 hrε
      have h2 := min_le_left s₀ (1 - s₀)
      have h3 := min_le_right s₀ (1 - s₀)
      constructor
      · rw [div_lt_iff₀ hr0]
        nlinarith [neg_abs_le σ, abs_nonneg σ]
      · rw [le_div_iff₀ hr0]
        nlinarith [le_abs_self σ, abs_nonneg σ]
    let fσ : CompactlySupportedContinuousMap (Eucl P) ℝ :=
      ⟨⟨fun w => f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))), by fun_prop⟩,
        HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) R) fun w hw =>
          hfz _ ((not_le.1 fun h => hw (mem_closedBall_zero_iff.2 h)).trans_le (hN1 σ w))⟩
    refine (hT.2 fσ).congr' ?_
    filter_upwards [hmem] with r hr
    refine Eq.symm ?_
    exact indicator_of_mem hr _

/-- **The product triple `(0, 1) × (M, θ, ξ)` (Simon Ch. 6, 3.2(2)).**  Write
`Φ(s, x) = (s, x)`, `π(y) = (y₁, …, y_P)`, `e₀ = (1, 0)` and `ι(v) = Φ(0, v)`, and assume the
product formula (MP) `H^{m+1}⌞{π ∈ A} = Φ_*(L¹ ⊗ Hᵐ⌞A)` for every `Hᵐ`-measurable countably
`m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for compact `K`.  If `(M, θ, ξ)` is a rectifiable
`m`-triple in `ℝ^P` with `θ ≥ 1` on `M`, then `((0, 1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` is a rectifiable
`(m + 1)`-triple in `ℝ^{P+1}`; here `e₀ ∧ ξ ∘ π` is characterized by
`⟨α, ξ′(Φ(s, x))⟩ = ⟨β, ξ(x)⟩` whenever `β(v) = α(e₀, ιv₁, …, ιvₘ)`. -/
theorem Submission.iwl_cr_ip_product_triple : ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m), IsRectifiableTriple (univ : Set (Eucl P)) m M θ ξ → (∀ x ∈ M, 1 ≤ θ x) → ∃ ξ' : Eucl (P + 1) → NVector (Eucl (P + 1)) (m + 1), IsRectifiableTriple (univ : Set (Eucl (P + 1))) (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ξ' ∧ ∀ (s : ℝ) (x : Eucl P) (α : Covector (Eucl (P + 1)) (m + 1)) (β : Covector (Eucl P) m), (∀ v : Fin m → Eucl P, β v = α (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → ξ' ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) α = ξ x β := by
  intro P m hMP M θ ξ hT hθ1
  -- (D1): cylinders over `Hᵐ`-null sets are `H^{m+1}`-null ((MP) with `Hᵐ⌞N = 0`).
  have hNT : ∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1)))
        {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 := by
    intro N hN
    have h := hMP N (NullMeasurableSet.of_null hN)
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hN)
      (fun K _ => (measure_mono_null inter_subset_left hN).trans_lt ENNReal.zero_lt_top)
    rw [Measure.restrict_eq_zero.mpr hN, Measure.prod_zero, Measure.map_zero] at h
    exact Measure.restrict_eq_zero.mp h
  -- Step 1: `Hᵐ(M ∩ K) ≤ ∫_{M ∩ K} |θ| dHᵐ < ∞` for compact `K`, since `θ ≥ 1` on `M`.
  have hlf : ∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞ := by
    intro K hK
    have hI := hT.integrableOn K hK (subset_univ K)
    have hnm : NullMeasurableSet (M ∩ K) (μHE[m] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet
    calc (μHE[m] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, 1 ∂(μHE[m] : Measure (Eucl P)) := by
          rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[m] : Measure (Eucl P)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hnm] with x hx
          rw [← ofReal_norm, ENNReal.one_le_ofReal, Real.norm_eq_abs]
          exact (hθ1 x hx.1).trans (le_abs_self _)
      _ < ∞ := hI.2
  -- Step 2: the contraction `ℒ α = α(e₀, ι ·)`, a continuous linear map `Λ^{m+1} → Λ^m`.
  obtain ⟨L, hL⟩ : ∃ L : Covector (Eucl (P + 1)) (m + 1) →L[ℝ] Covector (Eucl P) m,
      ∀ (α : Covector (Eucl (P + 1)) (m + 1)) (v : Fin m → Eucl P),
        L α v = α (Fin.cons (EuclideanSpace.single 0 1) fun i =>
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) := by
    let ι : Eucl P →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
      { toFun := fun v => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ v))
        map_add' := by
          intro v w
          apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
          simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := by
          intro c v
          apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
          simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    exact ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM ι).comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single 0 1 : Eucl (P + 1))).comp
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl (P + 1)) (F := ℝ)
          (n := m)).toContinuousLinearMap), fun α v => rfl⟩
  -- `ξ′(y) := ξ(π y) ∘ ℒ`, i.e. `⟨α, ξ′(y)⟩ = ⟨ℒ α, ξ(π y)⟩`.
  refine ⟨fun y => (ξ ((EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))).comp L, ?_, ?_⟩
  swap
  · -- Step 3: `ξ′(Φ(s, x))(α) = ξ(x)(ℒ α) = ξ(x)(β)`, as `π(Φ(s, x)) = x` and `ℒ α = β`.
    intro s x α β hβ
    have hLβ : L α = β := by
      ext v
      rw [hL α v, hβ v]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
      Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply, hLβ]
  -- The slab `O = {y₀ ∈ (0, 1)}` is Borel, `π` is continuous, and `M̃ = {π ∈ M} ∩ O` is
  -- `H^{m+1}`-null-measurable (Step 5, child `cylinder_null_measurable`).
  have hOm : MeasurableSet
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage
      ((continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous).measurable
  have hπc : Continuous (fun y : Eucl (P + 1) => (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) := by
    refine (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_
    exact continuous_pi fun i =>
      (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
  have hMt_nm : NullMeasurableSet {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}
      (μHE[m + 1] : Measure (Eucl (P + 1))) :=
    (Submission.iwl_cr_ip_pt_cylinder_nullMeasurableSet P m hNT M hT.nullMeasurableSet).inter
      hOm.nullMeasurableSet
  -- Step 4 (`subset`) and Step 5 (`nullMeasurableSet`).
  refine ⟨subset_univ _, hMt_nm, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 6: `M̃ ⊆ {π ∈ M}`, countably `(m + 1)`-rectifiable (child `cylinder_rectifiable`).
    exact (Submission.iwl_cr_ip_pt_cylinder_countablyRectifiable P m hNT M
      hT.countablyRectifiable).mono (fun y hy => hy.1)
  · -- Step 7: `θ̃(y) = θ(π y) > 0` on `M̃`.
    exact fun y hy => hT.pos _ hy.1
  · -- Step 8: `M̃ ∩ K′` lies in the slab over `M ∩ π(K′)`, on which `θ ∘ π` is integrable
    -- (child `slab_transfer` (a); `π(K′)` is compact).
    intro K' hK' _
    have hK : IsCompact ((fun y : Eucl (P + 1) => (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) '' K') := hK'.image hπc
    have hA := (Submission.iwl_cr_ip_pt_slab_transfer P m hMP (M ∩ _)
      (hT.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet)
      (hT.countablyRectifiable.mono inter_subset_left)
      (fun K'' hK'' => (measure_mono (inter_subset_inter_left _ inter_subset_left)).trans_lt
        (hlf K'' hK''))).1 θ (hT.integrableOn _ hK (subset_univ _))
    refine hA.mono_set ?_
    rintro y ⟨⟨hyM, hy0⟩, hyK'⟩
    exact ⟨⟨hyM, ⟨y, hyK', rfl⟩⟩, hy0⟩
  · -- Step 9: `ξ ∘ π` is a.e. strongly measurable on `M̃` (child `slab_transfer` (b)), and
    -- `T ↦ T ∘ ℒ` is continuous.
    have hξ := (Submission.iwl_cr_ip_pt_slab_transfer P m hMP M hT.nullMeasurableSet
      hT.countablyRectifiable hlf).2 ξ hT.aestronglyMeasurable
    exact (continuous_id.clm_comp continuous_const).comp_aestronglyMeasurable hξ
  · -- Step 10: the orientation fails at most on the cylinder over the `Hᵐ`-null set `N` of bad
    -- points of `M`, which is `H^{m+1}`-null by (D1).
    have hgood := hT.orients
    rw [ae_iff, Measure.restrict_apply₀' hT.nullMeasurableSet] at hgood
    have hNπ := hNT _ hgood
    rw [ae_iff, Measure.restrict_apply₀' hMt_nm]
    refine measure_mono_null ?_ hNπ
    rintro y ⟨hyQ, hyM, hy0⟩
    refine ⟨fun hgx => hyQ ?_, hyM⟩
    obtain ⟨τ, hτ, htan, hsign⟩ := hgx
    -- `y = Φ(y₀, π y)` with `y₀ ∈ (0, 1)`; the frame `τ̃ = (e₀, ιτ₁, …, ιτₘ)` is orthonormal
    -- (child `frame_orthonormal`) and spans the weighted tangent plane of `(M̃, θ̃)` at `y`
    -- (sibling `product_tangent`).
    have hy : (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin P) ℝ ((EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))))) = y := by
      simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
        ContinuousLinearEquiv.symm_apply_apply]
    have htan' := Submission.iwl_cr_ip_product_weighted_tangent P m hMP M θ _ τ _
      hT.nullMeasurableSet hT.countablyRectifiable hlf (fun z hz => (hT.pos z hz).le)
      (fun K hK => hT.integrableOn K hK (subset_univ K)) hτ htan hy0
    rw [hy] at htan'
    -- `(τ₁ ∧ ⋯ ∧ τₘ) ∘ ℒ = e₀ ∧ ιτ₁ ∧ ⋯ ∧ ιτₘ`, so `ξ′(y) = ±τ̃₀ ∧ ⋯ ∧ τ̃ₘ`.
    have hsimple : (simpleNVector τ).comp L = simpleNVector
        (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i =>
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) := by
      ext α
      simp only [ContinuousLinearMap.comp_apply, simpleNVector_apply]
      exact hL α τ
    refine ⟨_, Submission.iwl_cr_ip_pt_frame_orthonormal P m τ hτ, htan', ?_⟩
    rcases hsign with h | h
    · left
      rw [h, hsimple]
    · right
      rw [h, ContinuousLinearMap.neg_comp, hsimple]
/-- **Integrability of the integrands of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  For a
rectifiable triple `(M, θ, ξ)` in `U`: (a) `x ↦ θ(x) ⟨b, ξ(x)⟩` is `Hᵏ`-integrable on `M ∩ K` for
every compact `K ⊆ U` and `k`-covector `b`; (b) `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hᵏ`-integrable on `M`
for every continuous compactly supported `ω` with `spt ω ⊆ U`.  Since `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ`
orthonormal, `|⟨α, ξ⟩| ≤ ‖α‖` `Hᵏ⌞M`-a.e.; `θ` is integrable on `M ∩ K`, and the integrand of
(b) vanishes on `M \ spt ω`. -/
theorem Submission.ltg_tau_integrable : ∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ → (∀ (K : Set (Eucl P)) (b : Covector (Eucl P) k), IsCompact K → K ⊆ U → IntegrableOn (fun x => θ x * ξ x b) (M ∩ K) (μHE[k] : Measure (Eucl P))) ∧ ∀ ω : Eucl P → Covector (Eucl P) k, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U → IntegrableOn (fun x => θ x * ξ x (ω x)) M (μHE[k] : Measure (Eucl P)) := by
  intro P k U M θ ξ hT
  -- Step 1: for `Hᵏ⌞M`-a.e. `x`, `|ξ(x)(α)| ≤ ‖α‖` for every covector `α`
  -- (`|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`; the empty product for `k = 0`).
  have hunit : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) k, ‖ξ x α‖ ≤ ‖α‖ := by
    filter_upwards [hT.orients] with x hx α
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hs : ‖simpleNVector τ α‖ ≤ ‖α‖ :=
      calc ‖simpleNVector τ α‖ = ‖α τ‖ := rfl
        _ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h | h
    · rw [h]; exact hs
    · rw [h, neg_apply, norm_neg]; exact hs
  -- Step 2: `x ↦ ξ(x)(ω(x))` is a.e.-strongly measurable for `Hᵏ⌞M` whenever `ω` is
  -- (continuous evaluation `(w, α) ↦ w(α)` composed with `(ξ, ω)`).
  have hmeas : ∀ ω : Eucl P → Covector (Eucl P) k,
      AEStronglyMeasurable ω ((μHE[k] : Measure (Eucl P)).restrict M) →
      AEStronglyMeasurable (fun x => ξ x (ω x)) ((μHE[k] : Measure (Eucl P)).restrict M) := by
    intro ω hω
    have hev : Continuous fun p : NVector (Eucl P) k × Covector (Eucl P) k => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hev.comp_aestronglyMeasurable (hT.aestronglyMeasurable.prodMk hω)
  -- Steps 3–4: for compact `K ⊆ U` and `‖ω‖ ≤ C`, `θ` is integrable on `M ∩ K` and
  -- `ξ(·)(ω(·))` is measurable and a.e. bounded by `C` there, so the product is integrable.
  have hK : ∀ (K : Set (Eucl P)) (ω : Eucl P → Covector (Eucl P) k) (C : ℝ), IsCompact K →
      K ⊆ U → AEStronglyMeasurable ω ((μHE[k] : Measure (Eucl P)).restrict M) →
      (∀ x, ‖ω x‖ ≤ C) →
      IntegrableOn (fun x => θ x * ξ x (ω x)) (M ∩ K) (μHE[k] : Measure (Eucl P)) := by
    intro K ω C hKc hKU hω hC
    have hle : (μHE[k] : Measure (Eucl P)).restrict (M ∩ K) ≤
        (μHE[k] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono Set.inter_subset_left le_rfl
    have hθ : Integrable θ ((μHE[k] : Measure (Eucl P)).restrict (M ∩ K)) :=
      hT.integrableOn K hKc hKU
    refine hθ.mul_bdd (c := C) ((hmeas ω hω).mono_measure hle) ?_
    filter_upwards [ae_mono hle hunit] with x hx
    exact (hx (ω x)).trans (hC x)
  -- Part (a): the constant field `b`, bounded by `‖b‖`.
  refine ⟨fun K b hKc hKU => hK K (fun _ => b) ‖b‖ hKc hKU aestronglyMeasurable_const
    (fun _ => le_rfl), ?_⟩
  -- Part (b): integrable on `M ∩ spt ω` (Step 4) and zero on `M \ spt ω` (Step 5), with `M`
  -- null-measurable.
  intro ω hωc hωs hωU
  obtain ⟨C, hC⟩ := hωc.bounded_above_of_compact_support hωs
  refine (hK (tsupport ω) ω C hωs hωU hωc.aestronglyMeasurable hC).of_ae_sdiff_eq_zero
    hT.nullMeasurableSet (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∉ tsupport ω := fun h => hx.2 ⟨hx.1, h⟩
  rw [image_eq_zero_of_notMem_tsupport hx', map_zero, mul_zero]
/-- **Unit bound for the orientation `±τ₁ ∧ ⋯ ∧ τₙ` (Simon Ch. 6, 3.1).**  If `τ` is an
orthonormal family in `ℝ^P` and `w = ±simpleNVector τ`, then `|w(α)| ≤ ‖α‖` for every
`n`-covector `α`: `simpleNVector τ α = α(τ₁, …, τₙ)` and `‖α(τ)‖ ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
(`ContinuousAlternatingMap.le_opNorm`, each `τᵢ` a unit vector). -/
theorem Submission.fiw_ims_tt_unit_bound : ∀ (P n : ℕ) (τ : Fin n → Eucl P) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → ∀ α : Covector (Eucl P) n, |w α| ≤ ‖α‖ := by
  intro P n τ w hτ hw α
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`.
  have h1 : |simpleNVector τ α| ≤ ‖α‖ := by
    rw [simpleNVector_apply, ← Real.norm_eq_abs]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
      _ = ‖α‖ := by simp [hτ.1]
  -- `w = ±simpleNVector τ`, and `|-a| = |a|`.
  rcases hw with rfl | rfl
  · exact h1
  · simpa [abs_neg] using h1
/-- **An `n`-vector commutes with the interval integral of a continuous covector family.**  If
`f : ℝ → Λᵐ(ℝ^P)` is continuous and `c(v) = ∫_a^b f(s)(v) ds` for every `v`, then
`∫_a^b w(f(s)) ds = w(c)` for every `w ∈ Λₘ(ℝ^P)`: evaluation at `v` is a continuous linear
functional, so `(∫_a^b f)(v) = ∫_a^b f(s)(v) ds = c(v)` and `∫_a^b f = c`; then `w` commutes with
the integral (`ContinuousLinearMap.intervalIntegral_comp_comm`). -/
theorem Submission.iwl_cr_ci_ie_nvector_intervalIntegral : ∀ (P m : ℕ) (a b : ℝ) (f : ℝ → Covector (Eucl P) m) (c : Covector (Eucl P) m) (w : NVector (Eucl P) m), Continuous f → (∀ v : Fin m → Eucl P, c v = ∫ s in a..b, f s v) → ∫ s in a..b, w (f s) = w c := by
  intro P m a b f c w hf hc
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  -- `∫_a^b f = c`: both agree at every `v`, via the evaluation functional `α ↦ α v`.
  have hI : (∫ s in a..b, f s) = c := by
    ext v
    rw [hc v]
    let L : Covector (Eucl P) m →L[ℝ] ℝ :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Eucl P) ℝ v).comp
        (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
    have hL : ∀ α : Covector (Eucl P) m, L α = α v := fun α => rfl
    have h := L.intervalIntegral_comp_comm hfi
    simp only [hL] at h
    exact h.symm
  -- `w` commutes with the integral.
  rw [w.intervalIntegral_comp_comm hfi, hI]

/-- **Fubini for `∫ θ ⟨Φ(s), ξ⟩ dμ` over `s ∈ [0, 1]`.**  Let `μ` be s-finite, `θ ∈ L¹(μ)` and
`|ξ(x)(α)| ≤ ‖α‖` for `μ`-a.e. `x`, let `(s, x) ↦ Φ(s)(x)` be continuous with `‖Φ(s)(x)‖ ≤ B` on
`[0, 1] × ℝ^P`, and `Ψ(x) = ∫₀¹ Φ(s)(x) ds`.  Then `∫₀¹ ∫ θ ξ(Φ(s)) dμ ds = ∫ θ ξ(Ψ) dμ`: the
integrand is dominated by `B |θ(x)|` for `𝓛¹ ⌞ (0, 1] × μ`-a.e. `(s, x)`, so Fubini applies
(`integral_integral_swap`), and the inner integral is
`θ(x) ∫₀¹ ξ(x)(Φ(s)(x)) ds = θ(x) ξ(x)(Ψ(x))` (`iwl_cr_ci_ie_nvector_intervalIntegral`). -/
theorem Submission.iwl_cr_ci_ie_param_fubini : ∀ (P m : ℕ) (μ : Measure (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m) (Φ : ℝ → Eucl P → Covector (Eucl P) m) (Ψ : Eucl P → Covector (Eucl P) m) (B : ℝ), SFinite μ → Integrable θ μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖) → Continuous (fun p : ℝ × Eucl P => Φ p.1 p.2) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, ‖Φ s x‖ ≤ B) → (∀ (x : Eucl P) (v : Fin m → Eucl P), Ψ x v = ∫ s in (0 : ℝ)..1, Φ s x v) → ∫ s in (0 : ℝ)..1, ∫ x, θ x * ξ x (Φ s x) ∂μ = ∫ x, θ x * ξ x (Ψ x) ∂μ := by
  intro P m μ θ ξ Φ Ψ B hμ hθ hξ hbd hΦ hB hΨ
  -- `ν = 𝓛¹ ⌞ (0, 1]` is finite, and `F(s, x) = θ(x) ξ(x)(Φ(s)(x))` on `ℝ × ℝ^P`.
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have _instν : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  set F : ℝ → Eucl P → ℝ := fun s x => θ x * ξ x (Φ s x) with hF
  -- `F` is a.e. strongly measurable for `ν × μ`: `θ`, `ξ` only depend on `x`, `Φ` is jointly
  -- continuous and the evaluation `(w, α) ↦ w(α)` is continuous.
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (ν.prod μ) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × Eucl P => θ p.2) (ν.prod μ) :=
      hθ.aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × Eucl P => ξ p.2) (ν.prod μ) := hξ.comp_snd
    have h3 : AEStronglyMeasurable (fun p : ℝ × Eucl P => Φ p.1 p.2) (ν.prod μ) :=
      hΦ.aestronglyMeasurable
    exact h1.mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ h2 h3)
  -- `ν × μ`-a.e. `s ∈ (0, 1]` and `|ξ(x)(α)| ≤ ‖α‖`, so `|F(s, x)| ≤ |θ(x)| ‖Φ(s)(x)‖ ≤ B |θ(x)|`.
  have hbound : ∀ᵐ p ∂(ν.prod μ), ‖Function.uncurry F p‖ ≤ B * ‖θ p.2‖ := by
    have hs : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ Ioc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hx : ∀ᵐ p ∂(ν.prod μ), ∀ α : Covector (Eucl P) m, |ξ p.2 α| ≤ ‖α‖ :=
      Measure.quasiMeasurePreserving_snd.ae hbd
    filter_upwards [hs, hx] with p hp1 hp2
    simp only [Function.uncurry, hF, norm_mul, Real.norm_eq_abs]
    calc |θ p.2| * |ξ p.2 (Φ p.1 p.2)| ≤ |θ p.2| * B := by
          gcongr
          exact (hp2 _).trans (hB p.1 (Ioc_subset_Icc_self hp1) p.2)
      _ = B * |θ p.2| := mul_comm _ _
  -- `B |θ|` is `ν × μ`-integrable (`ν` finite), hence so is `F`.
  have hG : Integrable (fun p : ℝ × Eucl P => B * ‖θ p.2‖) (ν.prod μ) :=
    (integrable_const B).mul_prod hθ.norm
  have hint : Integrable (Function.uncurry F) (ν.prod μ) := hG.mono' hmeas hbound
  -- Fubini, with `∫₀¹ = ∫ dν` since `0 ≤ 1`.
  rw [intervalIntegral.integral_of_le zero_le_one]
  change ∫ s, ∫ x, F s x ∂μ ∂ν = _
  rw [integral_integral_swap hint]
  congr 1
  funext x
  -- The inner integral: `∫₀¹ θ(x) ξ(x)(Φ(s)(x)) ds = θ(x) ξ(x)(Ψ(x))`.
  change ∫ s in Ioc (0 : ℝ) 1, θ x * ξ x (Φ s x) = _
  rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul]
  congr 1
  exact Submission.iwl_cr_ci_ie_nvector_intervalIntegral P m 0 1 (fun s => Φ s x) (Ψ x) (ξ x)
    (hΦ.comp (continuous_id.prodMk continuous_const)) (hΨ x)

/-- **Exchange of an integer multiplicity current with `∫₀¹ ds` (Simon Ch. 6, 8.2, cone
construction).**  Let `X = τ(M, θ, ξ)` be integer multiplicity, `(s, x) ↦ φ(s)(x)` continuous with
`spt φ(s) ⊆ K` (`K` compact) for `s ∈ [0, 1]`, and `ψ(x)(v) = ∫₀¹ φ(s)(x)(v) ds`.  Then
`∫₀¹ X(φ(s)) ds = X(ψ)`: `μ_K := Hᵐ⌞(M ∩ K)` is finite (`θ ≥ 1` on `M`), every `φ(s)` and `ψ`
vanish off `K`, so `X(φ(s))` and `X(ψ)` are `μ_K`-integrals, and Fubini applies to
`θ(x) ξ(x)(φ(s)(x))`, dominated by `B |θ(x)|` with `B = sup_{[0,1] × K} ‖φ‖` and `|ξ(x)(α)| ≤ ‖α‖`. -/
theorem Submission.iwl_cr_ci_integral_exchange : ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (K : Set (Eucl P)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m) (ψ : TestFormOn (univ : Set (Eucl P)) m), IsIntegerMultiplicity X → IsCompact K → Continuous (fun p : ℝ × Eucl P => (φ p.1 : DifferentialForm (Eucl P) m) p.2) → (∀ s ∈ Icc (0 : ℝ) 1, tsupport (φ s : DifferentialForm (Eucl P) m) ⊆ K) → (∀ (x : Eucl P) (v : Fin m → Eucl P), (ψ : DifferentialForm (Eucl P) m) x v = ∫ s in (0 : ℝ)..1, (φ s : DifferentialForm (Eucl P) m) x v) → ∫ s in (0 : ℝ)..1, X (φ s) = X ψ := by
  intro P m X K φ ψ hX hK hφc hsupp hψ
  -- `X = τ(M, θ, ξ)` with `θ` integer valued on `M`.
  obtain ⟨M, θ, ξ, hT, hint, hXτ⟩ := hX
  -- `μ_K := Hᵐ⌞(M ∩ K)` is finite; `θ` is `μ_K`-integrable and `ξ` is `μ_K`-measurable.
  have hfin : (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞ :=
    Submission.iwl_cr_ci_ie_measure_inter_compact_lt_top P m univ M θ ξ K hT hint hK
      (subset_univ K)
  have _instK : IsFiniteMeasure ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hθ : Integrable θ ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) :=
    hT.integrableOn K hK (subset_univ K)
  have hξ : AEStronglyMeasurable ξ ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) :=
    hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  -- `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₘ` for an orthonormal `τ`, so `|ξ(x)(α)| ≤ ‖α‖` `μ_K`-a.e.
  have hbd : ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)),
      ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖ := by
    have h : ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict M),
        ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖ :=
      hT.orients.mono fun x ⟨τ, hτ, _, hξx⟩ => Submission.fiw_ims_tt_unit_bound P m τ (ξ x) hτ hξx
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left h
  -- Every `φ(s)`, `s ∈ [0, 1]`, and `ψ` vanish off `K`.
  have hφ0 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∉ K, (φ s : DifferentialForm (Eucl P) m) x = 0 :=
    fun s hs x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp s hs h)
  have hψ0 : ∀ x ∉ K, (ψ : DifferentialForm (Eucl P) m) x = 0 := by
    intro x hx
    ext v
    rw [hψ x v]
    have h : ∫ s in (0 : ℝ)..1, (φ s : DifferentialForm (Eucl P) m) x v
        = ∫ s in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      simp [hφ0 s hs x hx]
    rw [h]
    simp
  -- `‖φ(s)(x)‖ ≤ B` on the compact set `[0, 1] × K`, hence for all `x` when `s ∈ [0, 1]`.
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖(φ s : DifferentialForm (Eucl P) m) x‖ ≤ B := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hφc.continuousOn
    refine ⟨max C 0, fun s hs x => ?_⟩
    by_cases hx : x ∈ K
    · exact (hC (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)
    · rw [hφ0 s hs x hx, norm_zero]
      exact le_max_right _ _
  -- For `ω` vanishing off `K`, `X(ω) = ∫ θ ξ(ω) dμ_K`.
  have hXK : ∀ ω : TestFormOn (univ : Set (Eucl P)) m,
      (∀ x ∉ K, (ω : DifferentialForm (Eucl P) m) x = 0) →
      X ω = ∫ x, θ x * ξ x ((ω : DifferentialForm (Eucl P) m) x)
        ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) := by
    intro ω hω
    rw [hXτ ω, tauAction, ← setIntegral_indicator hK.isClosed.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hω x hx]
  -- Fubini on `[0, 1] × (M ∩ K)`: `∫₀¹ ∫ θ ξ(φ(s)) dμ_K ds = ∫ θ ξ(ψ) dμ_K`.
  have hmain := Submission.iwl_cr_ci_ie_param_fubini P m
    ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) θ ξ
    (fun s => (φ s : DifferentialForm (Eucl P) m)) ψ B inferInstance hθ hξ hbd hφc hBd hψ
  rw [hXK ψ hψ0, ← hmain]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  exact hXK (φ s) (hφ0 s hs)
/-- Smoothness of a parametric interval integral, with all derivatives under the integral sign:
for `G : ℝ × ℝ^P → V` of class `C^∞` (`V` complete), `g x = ∫_a^b G(t, x) dt` is `C^∞`, every
`x`-derivative `(t, x) ↦ ∂_x^j G(t, x)` is continuous, and `D^j g(x) = ∫_a^b ∂_x^j G(t, x) dt`.

Proof.  For smooth `H : ℝ × ℝ^P → W` the `x`-derivative `H'(t, x) = DH(t, x) ∘ inr` is smooth with
values in the complete space `ℝ^P →L W`.  Bounding `‖H'‖` on the compact set
`[[a, b]] × closedBall x₀ 1` and differentiating under the integral sign gives
`D(∫_a^b H(t, ·) dt) = ∫_a^b H'(t, ·) dt`.  Induction on `j`, over all complete codomains at once,
identifies `D^{j+1}` with `D^j ∘ D` through the currying isometry, which commutes with the
interval integral; `C^j` for every `j` is `C^∞`. -/
theorem Submission.iwl_cr_ro_intervalIntegral_contDiff :
    ∀ (P : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (G : ℝ × Eucl P → V) (a b : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl P => ∫ t in a..b, G (t, x)) ∧ (∀ j : ℕ, Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => G (p.1, z)) p.2)) ∧ ∀ (j : ℕ) (x : Eucl P), iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, G (t, y)) x = ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => G (t, z)) x := by
  intro P V _ _ _ G a b hG
  -- The partial derivative of a smooth `H` in `x` is `H'(t, x) = DH(t, x) ∘ inr` (chain rule).
  have hderiv : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (H : ℝ × Eucl P → W),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ (t : ℝ) (x : Eucl P),
      HasFDerivAt (fun z : Eucl P => H (t, z))
        ((fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x := by
    intro W _ _ H hH t x
    exact (hH.differentiable (by simp) (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- One differentiation under the integral sign: `‖H'‖ ≤ K` on `[[a, b]] × closedBall x₀ 1`.
  have hstep : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ x₀ : Eucl P,
      HasFDerivAt (fun x : Eucl P => ∫ t in a..b, H (t, x))
        (∫ t in a..b, (fderiv ℝ H (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x₀ := by
    intro W _ _ _ H hH x₀
    have hHc : Continuous H := hH.continuous
    have hH'c : Continuous fun p : ℝ × Eucl P =>
        (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) :=
      (hH.continuous_fderiv (by simp)).clm_comp continuous_const
    obtain ⟨K, hK⟩ := (isCompact_uIcc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      hH'c.continuousOn
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => H (t, x))
      (F' := fun x t => (fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)))
      (bound := fun _ => K) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x =>
        (hHc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      ((hHc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hH'c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx =>
        hK (t, x) ⟨uIoc_subset_uIcc ht, ball_subset_closedBall hx⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun t x _ => hderiv W H hH t x)
  -- Induction on `j` over all complete codomains: `C^j`, continuity of `∂_x^j H`, and
  -- `D^j (∫_a^b H(t, ·) dt) = ∫_a^b ∂_x^j H(t, ·) dt`.
  have claim : ∀ j : ℕ, ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H →
      ContDiff ℝ j (fun x : Eucl P => ∫ t in a..b, H (t, x)) ∧
      Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => H (p.1, z)) p.2) ∧
      ∀ x : Eucl P, iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, H (t, y)) x =
        ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => H (t, z)) x := by
    intro j
    induction j with
    | zero =>
      intro W _ _ _ H hH
      have hHc : Continuous H := hH.continuous
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_zero, contDiff_zero]
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun x t => H (t, x)) (hHc.comp continuous_swap) a b
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
        exact (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.continuous.comp hHc
      · intro x
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact (LinearIsometry.intervalIntegral_comp_comm
          (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.toLinearIsometry
          (fun t => H (t, x))).symm
    | succ j ih =>
      intro W _ _ _ H hH
      set H' : ℝ × Eucl P → (Eucl P →L[ℝ] W) :=
        fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) with hH'
      have hH'smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H' :=
        (hH.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_comp contDiff_const
      obtain ⟨ih1, ih2, ih3⟩ := ih (Eucl P →L[ℝ] W) H' hH'smooth
      have hg : fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) =
          fun x => ∫ t in a..b, H' (t, x) := by
        funext x
        exact (hstep W H hH x).fderiv
      have hgd : Differentiable ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) :=
        fun x => (hstep W H hH x).differentiableAt
      have hpart : ∀ t : ℝ, fderiv ℝ (fun z : Eucl P => H (t, z)) = fun z => H' (t, z) :=
        fun t => funext fun z => (hderiv W H hH t z).fderiv
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
        refine ⟨hgd, fun h => absurd h (by simp), ?_⟩
        rw [hg]
        exact ih1
      · have : (fun p : ℝ × Eucl P => iteratedFDeriv ℝ (j + 1) (fun z : Eucl P => H (p.1, z)) p.2) =
            fun p => (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm
              (iteratedFDeriv ℝ j (fun z : Eucl P => H' (p.1, z)) p.2) := by
          funext p
          rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
          congr 2
          exact hpart p.1
        rw [this]
        exact (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm.continuous.comp ih2
      · intro x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        have : (fun y => fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) y) =
            fun x => ∫ t in a..b, H' (t, x) := hg
        rw [this, ih3 x]
        have hint : IntervalIntegrable
            (fun t : ℝ => iteratedFDeriv ℝ j (fun z : Eucl P => H' (t, z)) x) volume a b :=
          (ih2.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
        have e := ContinuousLinearMap.intervalIntegral_comp_comm
          ((continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm :
            (Eucl P [×j]→L[ℝ] (Eucl P →L[ℝ] W)) →L[ℝ] (Eucl P [×(j + 1)]→L[ℝ] W)) hint
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe] at e
        rw [← e]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        congr 2
        exact (hpart t).symm
  exact ⟨contDiff_infty.2 fun n => (claim n V G hG).1,
    fun j => (claim j V G hG).2.1,
    fun j x => (claim j V G hG).2.2 x⟩
/-- Integrand of the radial homotopy operator.  For a `C^∞` `(k + 1)`-form `ω` and `a ∈ ℕ`, the map
`F(t, x) = tᵃ • (ω(t • x)).curryLeft x`, i.e. `F(t, x)(v) = tᵃ ω(tx)(x, v)`, is `C^∞` on
`ℝ × ℝ^P`, and for fixed `t` the derivative of `F(t, ·)` at `x` is
`w ↦ (v ↦ tᵃ (t Dω(tx)[w](x, v) + ω(tx)(w, v)))`, where `(y, v) = Fin.cons y v`. -/
theorem Submission.iwl_cr_ro_integrand_contDiff_fderiv :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) ∧
          ∀ (t : ℝ) (x w : Eucl P) (v : Fin k → Eucl P),
            fderiv ℝ (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x w v =
              t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v)) := by
  intro P k a ω hω
  -- The interior product `α ↦ α.curryLeft` as an (opaque) continuous linear map `B`.
  obtain ⟨B, hB⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      ∀ α, B α = α.curryLeft :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
        (n := k)).toContinuousLinearMap, fun α => rfl⟩
  refine ⟨?_, ?_⟩
  · -- `F(p) = p.1ᵃ • B (ω (p.1 • p.2)) p.2` is built from `C^∞` pieces.
    have hfun : (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) =
        fun p => p.1 ^ a • B (ω (p.1 • p.2)) p.2 := by
      funext p; rw [hB]
    rw [hfun]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    -- Naming the codomain `F` lets the normed instances on `Covector` be unified with `B`'s.
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => B (ω (p.1 • p.2))) := by
      exact (ContinuousLinearMap.contDiff (F := Eucl P →L[ℝ] Covector (Eucl P) k) B).comp
        (hω.comp hs)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × Eucl P => B (ω (p.1 • p.2)) p.2) :=
      h1.clm_apply contDiff_snd
    exact (contDiff_fst.pow a).smul h2
  · intro t x w v
    have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
        fun z => t ^ a • B (ω (t • z)) z := by
      funext z; rw [hB]
    rw [hfun]
    have hω' : HasFDerivAt ω (fderiv ℝ ω (t • x)) (t • x) :=
      (hω.differentiable (by simp) (t • x)).hasFDerivAt
    have hs : HasFDerivAt (fun z : Eucl P => t • z) (t • ContinuousLinearMap.id ℝ (Eucl P)) x :=
      (hasFDerivAt_id x).const_smul t
    -- Chain rule for `z ↦ B (ω (t • z))`.
    have hc : HasFDerivAt (fun z : Eucl P => B (ω (t • z)))
        (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))) x := by
      exact HasFDerivAt.comp (F := Covector (Eucl P) (k + 1))
        (G := Eucl P →L[ℝ] Covector (Eucl P) k) x
        (ContinuousLinearMap.hasFDerivAt (F := Eucl P →L[ℝ] Covector (Eucl P) k) B)
        (hω'.comp x hs)
    -- Product rule for `z ↦ B (ω (t • z)) z`, then scaling by `tᵃ`.
    have happ := hc.clm_apply (hasFDerivAt_id x)
    have hf : HasFDerivAt (fun z : Eucl P => t ^ a • B (ω (t • z)) z)
        (t ^ a • ((B (ω (t • x))).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
          (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))).flip x)) x :=
      happ.const_smul (t ^ a)
    -- Evaluate at `w` and `v`; `Matrix.vecCons` is definitionally `Fin.cons`.
    rw [hf.fderiv]
    simp only [_root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, hB,
      ContinuousAlternatingMap.curryLeft_apply_apply, map_smul, smul_eq_mul,
      ContinuousAlternatingMap.curryLeft_smul]
    rw [add_comm]
    rfl
/-- Bound on the `j`-th derivative of the radial-homotopy integrand: for `t ∈ [0, 1]` and
`‖x‖ ≤ R`, `‖D^j (z ↦ t^a • ι_z ω(t z))(x)‖ ≤ (R + j) D` when `‖D^i ω‖ ≤ D` on `closedBall 0 R`
for all `i ≤ j`.  Writing the integrand as `t^a • B (g z) z` with `g z = ω (t • z)` and `B` the
interior product (`‖B u v‖ ≤ ‖u‖ ‖v‖`), the Leibniz rule for `z ↦ B (g z) z`, proved below by
induction on the order, gives `‖D^j (B (g ·) ·)(x)‖ ≤ ‖x‖ ‖D^j g(x)‖ + j ‖D^(j-1) g(x)‖`, and
`‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` since `‖t x‖ ≤ R`. -/
theorem Submission.iwl_cr_ro_integrand_iteratedFDeriv_le :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
        (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R,
          ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤
            (R + j) * D := by
  intro P k a ω hω j R D hD hbound t ht x hx
  -- Leibniz bound for `z ↦ B (g z) z`.  Since `D (B (g ·) ·)(z) = B (g z) + B' (Dg z) z` with
  -- `B' A z h = B (A h) z`, again of the same shape, induction on the order gives
  -- `‖D^n (B (g ·) ·)(y)‖ ≤ ‖y‖ ‖D^n g(y)‖ + n ‖D^(n-1) g(y)‖`.
  have leibniz : ∀ (n : ℕ) (F G : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : F →L[ℝ] Eucl P →L[ℝ] G),
      (∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) →
      ∀ g : Eucl P → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ y : Eucl P,
        ‖iteratedFDeriv ℝ n (fun z => B (g z) z) y‖ ≤
          ‖y‖ * ‖iteratedFDeriv ℝ n g y‖ + n * ‖iteratedFDeriv ℝ (n - 1) g y‖ := by
    intro n
    induction n with
    | zero =>
      intro F G _ _ _ _ B hB g hg y
      rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, Nat.cast_zero, zero_mul, add_zero,
        mul_comm]
      exact hB (g y) y
    | succ n ih =>
      intro F G _ _ _ _ B hB g hg y
      obtain ⟨B', hB'apply, hB'bound⟩ :
          ∃ B' : (Eucl P →L[ℝ] F) →L[ℝ] Eucl P →L[ℝ] Eucl P →L[ℝ] G,
            (∀ A z h, B' A z h = B (A h) z) ∧ ∀ A z, ‖B' A z‖ ≤ ‖A‖ * ‖z‖ := by
        refine ⟨((ContinuousLinearMap.compL ℝ (Eucl P) F G).comp B.flip).flip,
          fun A z h => rfl, fun A z => ?_⟩
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        show ‖B (A h) z‖ ≤ ‖A‖ * ‖z‖ * ‖h‖
        calc ‖B (A h) z‖ ≤ ‖A h‖ * ‖z‖ := hB (A h) z
          _ ≤ ‖A‖ * ‖h‖ * ‖z‖ := by gcongr; exact A.le_opNorm h
          _ = ‖A‖ * ‖z‖ * ‖h‖ := by ring
      have hBnorm : ‖B‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [one_mul]
        exact hB u v
      have hgd : Differentiable ℝ g := (contDiff_infty_iff_fderiv.1 hg).1
      have hdg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
        (contDiff_infty_iff_fderiv.1 hg).2
      have hderiv : fderiv ℝ (fun z => B (g z) z) = fun z => B (g z) + B' (fderiv ℝ g z) z := by
        funext z
        have h1 : HasFDerivAt (fun z => B (g z)) (B.comp (fderiv ℝ g z)) z :=
          B.hasFDerivAt.comp z (hgd z).hasFDerivAt
        have h2 : HasFDerivAt (fun z => B (g z) z)
            ((B (g z)).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
              (B.comp (fderiv ℝ g z)).flip z) z :=
          h1.clm_apply (hasFDerivAt_id z)
        rw [h2.fderiv]
        ext h
        simp [hB'apply]
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B (g z)) := B.contDiff.comp hg
      have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B' (fderiv ℝ g z) z) :=
        B'.isBoundedBilinearMap.contDiff.comp (hdg.prodMk contDiff_id)
      have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
      have hadd : iteratedFDeriv ℝ n (fun z => B (g z) + B' (fderiv ℝ g z) z) y =
          iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y :=
        iteratedFDeriv_add_apply (hc1.contDiffAt.of_le hle) (hc2.contDiffAt.of_le hle)
      have hcomp : iteratedFDeriv ℝ n (fun z => B (g z)) y =
          B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y) :=
        B.iteratedFDeriv_comp_left hg.contDiffAt hle
      have e1 : ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ ≤ ‖iteratedFDeriv ℝ n g y‖ := by
        rw [hcomp]
        calc ‖B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y)‖
            ≤ ‖B‖ * ‖iteratedFDeriv ℝ n g y‖ := B.norm_compContinuousMultilinearMap_le _
          _ ≤ 1 * ‖iteratedFDeriv ℝ n g y‖ := by gcongr
          _ = ‖iteratedFDeriv ℝ n g y‖ := one_mul _
      have e2 := ih (Eucl P →L[ℝ] F) (Eucl P →L[ℝ] G) B' hB'bound (fderiv ℝ g) hdg y
      rw [norm_iteratedFDeriv_fderiv] at e2
      have e3 : (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) (fderiv ℝ g) y‖ =
          n * ‖iteratedFDeriv ℝ n g y‖ := by
        rcases n with _ | m
        · simp
        · rw [norm_iteratedFDeriv_fderiv, Nat.add_sub_cancel]
      rw [e3] at e2
      rw [← norm_iteratedFDeriv_fderiv, hderiv, hadd, Nat.add_sub_cancel]
      calc ‖iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖
          ≤ ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ +
            ‖iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ n g y‖ +
            (‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ + n * ‖iteratedFDeriv ℝ n g y‖) :=
              add_le_add e1 e2
        _ = ‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ +
            ((n + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ n g y‖ := by push_cast; ring
  -- The interior product `B α = α.curryLeft`, a linear isometry, so `‖B u v‖ ≤ ‖u‖ ‖v‖`.
  obtain ⟨B, hB, hBbound⟩ :
      ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] Eucl P →L[ℝ] Covector (Eucl P) k,
        (∀ α, B α = α.curryLeft) ∧ ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖ := by
    refine ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
      (n := k)).toContinuousLinearMap, fun α => rfl, fun u v => ?_⟩
    calc ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u v‖
        ≤ ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖u‖ * ‖v‖ := by
          rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hR : 0 ≤ R := (norm_nonneg x).trans hx'
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
      fun z => t ^ a • B (ω (t • z)) z := by
    funext z; rw [hB]
  rw [hfun]
  -- `g z = ω (L z)` with `L = t • id`, `‖L‖ ≤ 1`, so `‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` for `i ≤ j`.
  set L : Eucl P →L[ℝ] Eucl P := t • ContinuousLinearMap.id ℝ (Eucl P) with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖ContinuousLinearMap.id ℝ (Eucl P)‖ ≤ 1 * 1 :=
          mul_le_mul ht1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgfun : (fun z : Eucl P => ω (t • z)) = ω ∘ L := by
    funext z; simp [hL]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => ω (t • z)) := by
    rw [hgfun]; exact hω.comp L.contDiff
  have hgnorm : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ ≤ D := by
    intro i hi
    rw [hgfun, L.iteratedFDeriv_comp_right hω x (by exact_mod_cast le_top)]
    have hLx : L x ∈ closedBall (0 : Eucl P) R := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ 1 * R := mul_le_mul hLnorm hx' (norm_nonneg x) zero_le_one
        _ = R := one_mul R
    calc ‖(iteratedFDeriv ℝ i ω (L x)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ i ω (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ D * 1 := by
          apply mul_le_mul (hbound i hi _ hLx) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
      _ = D := mul_one D
  -- Pull out `t^a` (`0 ≤ t^a ≤ 1`) and apply the Leibniz bound.
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => B (ω (t • z)) z) :=
    B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)
  have hsmul : iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • B (ω (t • z)) z) x =
      t ^ a • iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x :=
    iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [hsmul, norm_smul]
  have hta : ‖t ^ a‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1
  have key := leibniz j _ _ B hBbound (fun z => ω (t • z)) hg x
  have hsum : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ +
      j * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ (R + j) * D := by
    have e1 : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ ≤ R * D :=
      mul_le_mul hx' (hgnorm j le_rfl) (norm_nonneg _) hR
    have e2 : (j : ℝ) * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ j * D :=
      mul_le_mul_of_nonneg_left (hgnorm (j - 1) (Nat.sub_le j 1)) (Nat.cast_nonneg j)
    linarith
  calc ‖t ^ a‖ * ‖iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x‖
      ≤ 1 * ((R + j) * D) := mul_le_mul hta (key.trans hsum) (norm_nonneg _) zero_le_one
    _ = (R + j) * D := one_mul _

/-- The radial homotopy operator `ψ(x) = ∫₀¹ tᵃ x ⌟ ω(t x) dt` (proof of Simon Ch. 6, 8.2,
Part I): for a smooth `(k + 1)`-form `ω`, `ψ` is a smooth `k`-form with
(i) `ψ(x)(v) = ∫₀¹ tᵃ ω(t x)(x, v) dt`,
(ii) `Dψ(x)[w](v) = ∫₀¹ tᵃ (t Dω(t x)[w](x, v) + ω(t x)(w, v)) dt`, and
(iii) `‖Dʲψ(x)‖ ≤ (R + j) D` on `B̄_R(0)` whenever `‖Dⁱω‖ ≤ D` there for all `i ≤ j`.
The integrand `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is jointly smooth, so `ψ = ∫₀¹ F(t, ·) dt`
is smooth with `Dʲψ = ∫₀¹ Dʲ_x F dt`; evaluation commutes with the integral. -/
theorem Submission.iwl_cr_radial_operator :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∃ ψ : DifferentialForm (Eucl P) k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
        (∀ (x : Eucl P) (v : Fin k → Eucl P),
          ψ x v = ∫ t in (0 : ℝ)..1, t ^ a * ω (t • x) (Fin.cons x v)) ∧
        (∀ (x w : Eucl P) (v : Fin k → Eucl P),
          fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1,
            t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v))) ∧
        ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
          (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
          ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D := by
  intro P k a ω hω
  -- `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is smooth; `ψ = ∫₀¹ F(t, ·) dt` and
  -- `Dʲψ(x) = ∫₀¹ Dʲ(F(t, ·))(x) dt`, with `(t, x) ↦ Dʲ(F(t, ·))(x)` continuous.
  obtain ⟨hGsmooth, hGderiv⟩ := Submission.iwl_cr_ro_integrand_contDiff_fderiv P k a ω hω
  obtain ⟨hψsmooth, hGcont, hψiter⟩ :=
    Submission.iwl_cr_ro_intervalIntegral_contDiff P (Covector (Eucl P) k) _ 0 1 hGsmooth
  dsimp only at hψsmooth hGcont hψiter
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, t ^ a • (ω (t • x)).curryLeft x, hψsmooth, ?_, ?_, ?_⟩
  · -- (i): evaluation at `v` is a continuous linear map, so it commutes with the integral.
    intro x v
    have hc : Continuous fun t : ℝ => t ^ a • (ω (t • x)).curryLeft x :=
      hGsmooth.continuous.comp (continuous_id.prodMk continuous_const)
    have e := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousAlternatingMap.apply_apply] at e
    beta_reduce
    rw [← e]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      smul_eq_mul]
    rfl
  · -- (ii): `Dψ(x)[w] = D¹ψ(x)(w)`; evaluate `∫₀¹ D¹(F(t, ·))(x) dt` at `w`, then at `v`.
    intro x w v
    have hc₁ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x :=
      (hGcont 1).comp (continuous_id.prodMk continuous_const)
    have hc₂ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x (fun _ => w) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
        (fun _ => w)).continuous.comp hc₁
    have e₁ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
      (fun _ => w)).intervalIntegral_comp_comm (hc₁.intervalIntegrable (μ := volume) 0 1)
    have e₂ := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc₂.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousMultilinearMap.apply_apply, ContinuousAlternatingMap.apply_apply] at e₁ e₂
    have e₀ : ∀ f : Eucl P → Covector (Eucl P) k,
        fderiv ℝ f x w = iteratedFDeriv ℝ 1 f x (fun _ => w) :=
      fun f => (iteratedFDeriv_one_apply (fun _ : Fin 1 => w)).symm
    rw [e₀, hψiter 1 x, ← e₁, ← e₂]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [iteratedFDeriv_one_apply]
    exact hGderiv t x w v
  · -- (iii): `‖Dʲψ(x)‖ ≤ ∫₀¹ ‖Dʲ(F(t, ·))(x)‖ dt ≤ (R + j) D`.
    intro j R D hD hω_le x hx
    rw [hψiter j x]
    have hle : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun z => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Submission.iwl_cr_ro_integrand_iteratedFDeriv_le P k a ω hω j R D hD hω_le t
        ⟨ht.1.le, ht.2⟩ x hx
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rwa [sub_zero, abs_one, mul_one] at h

/-- **`τ(M, θ, ξ)` is a current (Simon Ch. 6, 3.1, p. 146).**  For a rectifiable triple `(M, θ, ξ)`
in `V` (`V` need not be open), `ω ↦ τ(M, θ, ξ)(ω) = ∫_M θ(x) ⟨ω(x), ξ(x)⟩ dHⁿ(x)` is a current
`X ∈ 𝒟ₙ(V)`.  It is linear since the integrands are `Hⁿ`-integrable on `M` (`ltg_tau_integrable`).
It is sequentially continuous: if `ω_j → 0` in `𝒟ⁿ(V)`, all supports lie in one compact `K ⊆ V`
and `sup_K ‖ω_j‖ → 0`; as `|⟨α, ξ(x)⟩| ≤ ‖α‖` for `Hⁿ⌞M`-a.e. `x` (`fiw_ims_tt_unit_bound`) and
`θ > 0` on `M`, `|τ(ω_j)| ≤ (sup_K ‖ω_j‖) ∫_{M ∩ K} θ dHⁿ → 0`. -/
theorem Submission.br_loc_tauAction_current : ∀ (P n : ℕ) (V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple V n M θ ξ → ∃ X : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, X ω = tauAction n M θ ξ ω := by
  intro P n V M θ ξ hTr
  -- Step 1: for every test form `ω` (smooth, hence continuous, with compact support in `V`),
  -- `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hⁿ`-integrable on `M`.
  have hint : ∀ ω : TestFormOn V n, IntegrableOn
      (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)) M (μHE[n] : Measure (Eucl P)) :=
    fun ω => (Submission.ltg_tau_integrable P n V M θ ξ hTr).2 _
      ω.property.1.1.continuous ω.property.1.2 ω.property.2
  -- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨α, ξ(x)⟩| ≤ ‖α‖` for every
  -- covector `α`, for `Hⁿ⌞M`-a.e. `x`.
  have hub : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) n, |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hTr.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    exact Submission.fiw_ims_tt_unit_bound P n τ (ξ x) hτ hξ
  -- Step 3: `ω ↦ τ(M, θ, ξ)(ω)` is linear (additivity of the integral of integrable functions;
  -- constants factor out of the integral).
  let L : CurrentOn V n :=
    { toFun := fun ω => tauAction n M θ ξ ω
      map_add' := by
        intro ω η
        simp only [tauAction]
        rw [← integral_add (hint ω) (hint η)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add]
      map_smul' := by
        intro c ω
        simp only [tauAction, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- Sequential continuity: let `ω_j → 0` in `𝒟ⁿ(V)`, all supported in the compact `K ⊆ V`.
  intro ωs hconv
  obtain ⟨K, hK, hKV, hsupp, -, hderiv⟩ := hconv
  -- Step 4: `sup_K ‖ω_j‖ → 0` (uniform convergence of order `0`, `‖D⁰ω(x)‖ = ‖ω(x)‖`).
  have hsmall : ∀ δ > 0, ∀ᶠ j in atTop, ∀ x ∈ K,
      ‖(ωs j : DifferentialForm (Eucl P) n) x‖ < δ := by
    intro δ hδ
    have h0 := (Metric.tendstoUniformlyOn_iff.mp (hderiv 0)) δ hδ
    filter_upwards [h0] with j hj x hx
    have := hj x hx
    rw [dist_comm, dist_eq_norm] at this
    simpa [norm_iteratedFDeriv_zero] using this
  -- Step 5: the majorant `1_K θ` is `Hⁿ⌞M`-integrable, with integral `C = ∫_{M ∩ K} θ dHⁿ`.
  have hIK : IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    hTr.integrableOn K hK hKV
  set C : ℝ := ∫ x in M ∩ K, θ x ∂(μHE[n] : Measure (Eucl P))
  have hgint : Integrable (K.indicator θ) ((μHE[n] : Measure (Eucl P)).restrict M) := by
    rw [integrable_indicator_iff hK.measurableSet, IntegrableOn,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact hIK
  have hgC : ∫ x, K.indicator θ x ∂((μHE[n] : Measure (Eucl P)).restrict M) = C := by
    rw [integral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_comm]
  -- Step 6: with `δ = ε / (|C| + 1)` and `j` large, `|θ ⟨ω_j, ξ⟩| ≤ δ 1_K θ` `Hⁿ⌞M`-a.e. (on `K`
  -- by Steps 2 and 4 and `θ > 0` on `M`; off `K` since `ω_j = 0` there), so
  -- `|τ(ω_j)| ≤ δ C ≤ δ |C| < ε`.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (|C| + 1) := by positivity
  filter_upwards [hsmall _ hδ] with j hj
  rw [Real.dist_eq, sub_zero]
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      ‖θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
        (ε / (|C| + 1)) * K.indicator θ x := by
    filter_upwards [hub, ae_restrict_mem₀ hTr.nullMeasurableSet] with x hx hxM
    have hθ := hTr.pos x hxM
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs, abs_mul, abs_of_pos hθ]
      calc θ x * |ξ x ((ωs j : DifferentialForm (Eucl P) n) x)|
          ≤ θ x * ‖(ωs j : DifferentialForm (Eucl P) n) x‖ :=
            mul_le_mul_of_nonneg_left (hx _) hθ.le
        _ ≤ θ x * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left (hj x hxK).le hθ.le
        _ = ε / (|C| + 1) * θ x := mul_comm _ _
    · have hz : (ωs j : DifferentialForm (Eucl P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      rw [indicator_of_notMem hxK, hz, map_zero, mul_zero, norm_zero, mul_zero]
  have hle := norm_integral_le_of_norm_le (hgint.const_mul (ε / (|C| + 1))) hbound
  rw [integral_const_mul, hgC, Real.norm_eq_abs] at hle
  change |∫ x in M, θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)
    ∂(μHE[n] : Measure (Eucl P))| < ε
  calc _ ≤ ε / (|C| + 1) * C := hle
    _ ≤ ε / (|C| + 1) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hδ.le
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]
/-- Cylinders over `Hᵐ`-null sets are `Hᵐ⁺¹`-null: if `N ⊆ ℝ^P` has `μHE[m] N = 0`, then the
cylinder `{y ∈ ℝ^{P+1} | π y ∈ N} = ℝ × N`, `π y = (y₁, …, y_P)`, has `μHE[m + 1]`-measure zero.
For `m = 0` the set `N` is empty.  For `m ≥ 1`, each strip `{y | π y ∈ N, a ≤ y₀ ≤ a + 1}`
(`a ∈ ℤ`) is covered by the boxes `{y | π y ∈ C i, a + j dᵢ ≤ y₀ ≤ a + (j + 1) dᵢ}`,
`j ≤ ⌊1 / dᵢ⌋₊`, where the `C i` cover `N` with `∑ ediam (C i) ^ m` small and
`dᵢ ≥ ediam (C i)` is slightly inflated.  The boxes have diameter `≤ 2 dᵢ`, so the sum of
`ediam ^ (m + 1)` over them is at most `2 ^ (m + 2) ∑ dᵢ ^ m`, which is arbitrarily small. -/
theorem Submission.iwl_cr_hp_cylinder_null : ∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 := by
  intro P m N hN
  have hE : ∀ (k : ℕ) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      [MeasurableSpace X] [BorelSpace X] (S : Set X), (μHE[k] : Measure X) S =
        (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k))) μH[k] : ℝ≥0∞) *
          μH[k] S := by
    intro k X _ _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: a `μH[0]`-null set is empty
    have hNe : N = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have h1 : μH[0] ({x} : Set (Eucl P)) ≤ μH[0] N := measure_mono (singleton_subset_iff.mpr hx)
      rw [Measure.hausdorffMeasure_zero_singleton] at h1
      rw [Measure.euclideanHausdorffMeasure_zero] at hN
      rw [hN] at h1
      exact absurd h1 (by simp)
    subst hNe
    simp
  · have hcm : (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin m)))
        μH[m] : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero m
    have hNm : μH[(m : ℝ)] N = 0 := by
      rw [hE m N] at hN
      exact (mul_eq_zero.mp hN).resolve_left hcm
    rw [hE (m + 1)]
    suffices h : μH[((m + 1 : ℕ) : ℝ)] {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 by rw [h, mul_zero]
    have hsub : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} ⊆ ⋃ a : ℤ, {y : Eucl (P + 1) |
          (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N ∧
          (a : ℝ) ≤ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∧
          EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ≤ a + 1} := by
      intro y hy
      exact mem_iUnion.2 ⟨⌊EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0⌋, hy, Int.floor_le _,
        (Int.lt_floor_add_one _).le⟩
    have hstrip : ∀ a : ℤ, μH[((m + 1 : ℕ) : ℝ)] {y : Eucl (P + 1) |
        (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N ∧
        (a : ℝ) ≤ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ≤ a + 1} = 0 := by
      intro a
      set π : Eucl (P + 1) → Eucl P := fun y =>
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
        with hπdef
      set y0 : Eucl (P + 1) → ℝ := fun y => EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 with hy0def
      have hdist : ∀ y y' : Eucl (P + 1),
          dist y y' ^ 2 = (y0 y - y0 y') ^ 2 + dist (π y) (π y') ^ 2 := by
        intro y y'
        rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity),
          Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
        simp [hπdef, hy0def, Fin.tail, Real.dist_eq, sq_abs]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      apply le_antisymm _ zero_le
      rw [Measure.hausdorffMeasure_apply]
      refine iSup₂_le fun r hr => ?_
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      rw [zero_add]
      -- the radius
      obtain ⟨δ, hδ0, hδ1, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ENNReal.ofReal δ ≤ r := by
        rcases eq_or_ne r ⊤ with rfl | hrt
        · exact ⟨1 / 2, by norm_num, le_rfl, le_top⟩
        · have hr' : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrt
          refine ⟨min (1 / 2) (r.toReal / 2), by positivity, min_le_left _ _, ?_⟩
          calc ENNReal.ofReal (min (1 / 2) (r.toReal / 2)) ≤ ENNReal.ofReal r.toReal :=
                ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (by linarith))
            _ = r := ENNReal.ofReal_toReal hrt
      -- the smallness parameter
      have hη0 : (0 : ℝ) < η := hη
      set ε : ℝ := min ((δ / 2) ^ m / 2) (η / 2 ^ (m + 3)) with hεdef
      have hε0 : 0 < ε := by positivity
      have hεδ : ε < (δ / 2) ^ m := by
        have : 0 < (δ / 2) ^ m := by positivity
        exact (min_le_left _ _).trans_lt (by linarith)
      have hεη : 2 ^ (m + 3) * ε ≤ η := by
        have h := min_le_right ((δ / 2) ^ m / 2) (η / 2 ^ (m + 3))
        rw [← hεdef] at h
        have h2 : (0 : ℝ) < 2 ^ (m + 3) := by positivity
        calc 2 ^ (m + 3) * ε ≤ 2 ^ (m + 3) * (η / 2 ^ (m + 3)) := by gcongr
          _ = η := by field_simp
      -- a cover of `N`
      have hNa := hNm
      rw [Measure.hausdorffMeasure_apply] at hNa
      have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (by positivity)
      have hF := (iSup₂_eq_bot.mp hNa) (ENNReal.ofReal (δ / 2)) hδ2
      have hlt : (⨅ (t : ℕ → Set (Eucl P)) (_ : N ⊆ ⋃ n, t n)
          (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal (δ / 2)),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ)) < ENNReal.ofReal ε := by
        rw [hF]; exact ENNReal.ofReal_pos.mpr hε0
      obtain ⟨C, hC⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hCcov, hC⟩ := iInf_lt_iff.mp hC
      obtain ⟨hCdiam, hCsum⟩ := iInf_lt_iff.mp hC
      have hCsum' : ∑' i, ediam (C i) ^ m < ENNReal.ofReal ε := by
        refine lt_of_le_of_lt (le_of_eq ?_) hCsum
        refine tsum_congr fun i => ?_
        rcases (C i).eq_empty_or_nonempty with he | hne
        · have : ¬ (C i).Nonempty := by rw [he]; exact not_nonempty_empty
          rw [iSup_neg this, he, ediam_empty, zero_pow (by omega)]
          rfl
        · rw [iSup_pos hne, ENNReal.rpow_natCast]
      -- real diameters
      set D : ℕ → ℝ := fun i => (ediam (C i)).toReal with hDdef
      have hCfin : ∀ i, ediam (C i) ≠ ⊤ := fun i =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCdiam i)
      have hCeq : ∀ i, ediam (C i) = ENNReal.ofReal (D i) := fun i =>
        (ENNReal.ofReal_toReal (hCfin i)).symm
      have hD0 : ∀ i, 0 ≤ D i := fun i => ENNReal.toReal_nonneg
      have hDδ : ∀ i, D i ≤ δ / 2 := fun i =>
        ENNReal.toReal_le_of_le_ofReal (by positivity) (hCdiam i)
      have hCdist : ∀ i, ∀ x ∈ C i, ∀ x' ∈ C i, dist x x' ≤ D i := by
        intro i x hx x' hx'
        have h := edist_le_ediam_of_mem hx hx'
        rw [hCeq i, edist_dist] at h
        exact (ENNReal.ofReal_le_ofReal_iff (hD0 i)).mp h
      -- inflated diameters
      set lam : ℕ → ℝ := fun i => ε / 2 / 2 ^ i / (δ / 2) ^ m with hlamdef
      have hδm : 0 < (δ / 2) ^ m := by positivity
      have hlam0 : ∀ i, 0 < lam i := fun i => by positivity
      have hlam1 : ∀ i, lam i ≤ 1 := by
        intro i
        rw [hlamdef, div_le_one hδm]
        have h1 : ε / 2 / 2 ^ i ≤ ε := by
          rw [div_div]
          exact div_le_self hε0.le (by
            have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
            linarith)
        linarith
      set ρ : ℕ → ℝ := fun i => δ / 2 * lam i with hρdef
      have hρ0 : ∀ i, 0 < ρ i := fun i => mul_pos (by positivity) (hlam0 i)
      have hρδ : ∀ i, ρ i ≤ δ / 2 := fun i => by
        have := hlam1 i
        have h2 : 0 < δ / 2 := by positivity
        calc ρ i = δ / 2 * lam i := rfl
          _ ≤ δ / 2 * 1 := by gcongr
          _ = δ / 2 := mul_one _
      have hρm : ∀ i, ρ i ^ m ≤ ε / 2 / 2 ^ i := by
        intro i
        have hl := pow_le_of_le_one (hlam0 i).le (hlam1 i) (by omega : m ≠ 0)
        calc ρ i ^ m = (δ / 2) ^ m * lam i ^ m := by rw [hρdef, mul_pow]
          _ ≤ (δ / 2) ^ m * lam i := by gcongr
          _ = ε / 2 / 2 ^ i := by rw [hlamdef]; field_simp
      set d : ℕ → ℝ := fun i => max (D i) (ρ i) with hddef
      have hd0 : ∀ i, 0 < d i := fun i => lt_max_of_lt_right (hρ0 i)
      have hdδ : ∀ i, d i ≤ δ / 2 := fun i => max_le (hDδ i) (hρδ i)
      have hd1 : ∀ i, d i ≤ 1 := fun i => (hdδ i).trans (by linarith)
      have hDd : ∀ i, D i ≤ d i := fun i => le_max_left _ _
      have hdm : ∀ i, d i ^ m ≤ D i ^ m + ε / 2 / 2 ^ i := by
        intro i
        rcases le_total (D i) (ρ i) with h | h
        · rw [hddef]; simp only [max_eq_right h]
          have := hρm i
          have : 0 ≤ D i ^ m := pow_nonneg (hD0 i) m
          linarith
        · rw [hddef]; simp only [max_eq_left h]
          have : 0 ≤ ε / 2 / 2 ^ i := by positivity
          linarith
      -- number of intervals
      set k : ℕ → ℕ := fun i => ⌊1 / d i⌋₊ + 1 with hkdef
      have hk : ∀ i, (k i : ℝ) ≤ 2 / d i := by
        intro i
        have h1 : (⌊1 / d i⌋₊ : ℝ) ≤ 1 / d i := Nat.floor_le (by have := hd0 i; positivity)
        have h2 : (1 : ℝ) ≤ 1 / d i := by rw [le_div_iff₀ (hd0 i)]; linarith [hd1 i]
        simp only [hkdef, Nat.cast_add, Nat.cast_one]
        calc (⌊1 / d i⌋₊ : ℝ) + 1 ≤ 1 / d i + 1 / d i := by linarith
          _ = 2 / d i := by ring
      -- the boxes
      set Q : ℕ → ℕ → Set (Eucl (P + 1)) := fun i j =>
        {y | π y ∈ C i ∧ (a : ℝ) + j * d i ≤ y0 y ∧ y0 y ≤ a + (j + 1) * d i} with hQdef
      have hQdiam : ∀ i j, ediam (Q i j) ≤ ENNReal.ofReal (2 * d i) := by
        intro i j
        refine ediam_le_of_forall_dist_le fun y hy y' hy' => ?_
        have h1 : |y0 y - y0 y'| ≤ d i := by
          rw [abs_le]; constructor <;> nlinarith [hy.2.1, hy.2.2, hy'.2.1, hy'.2.2]
        have h2 : dist (π y) (π y') ≤ d i := (hCdist i _ hy.1 _ hy'.1).trans (hDd i)
        have h3 : dist y y' ^ 2 ≤ (2 * d i) ^ 2 := by
          rw [hdist]
          have : (y0 y - y0 y') ^ 2 ≤ d i ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have : dist (π y) (π y') ^ 2 ≤ d i ^ 2 := pow_le_pow_left₀ dist_nonneg h2 2
          nlinarith
        have h4 : 0 ≤ 2 * d i := by have := hd0 i; positivity
        exact (pow_le_pow_iff_left₀ dist_nonneg h4 two_ne_zero).mp h3
      -- the indexed cover
      set t : ℕ → Set (Eucl (P + 1)) := fun n =>
        if n.unpair.2 < k n.unpair.1 then Q n.unpair.1 n.unpair.2 else ∅ with htdef
      have htpair : ∀ i j, t (Nat.pair i j) = if j < k i then Q i j else ∅ := by
        intro i j; simp only [htdef, Nat.unpair_pair]
      have htcov : {y : Eucl (P + 1) | π y ∈ N ∧ (a : ℝ) ≤ y0 y ∧ y0 y ≤ a + 1} ⊆ ⋃ n, t n := by
        intro y hy
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hCcov hy.1)
        set u : ℝ := (y0 y - a) / d i with hudef
        have hu0 : 0 ≤ u := div_nonneg (by linarith [hy.2.1]) (hd0 i).le
        have hu1 : u ≤ 1 / d i := div_le_div_of_nonneg_right (by linarith [hy.2.2]) (hd0 i).le
        set j := ⌊u⌋₊ with hjdef
        have hjk : j < k i := by
          have : ⌊u⌋₊ ≤ ⌊1 / d i⌋₊ := Nat.floor_le_floor hu1
          simp only [hkdef]; omega
        refine mem_iUnion.mpr ⟨Nat.pair i j, ?_⟩
        rw [htpair, ite_eq_left hjk]
        refine ⟨hi, ?_, ?_⟩
        · have h1 : (j : ℝ) ≤ u := Nat.floor_le hu0
          have h2 : (j : ℝ) * d i ≤ y0 y - a := by
            rw [hudef, le_div_iff₀ (hd0 i)] at h1; exact h1
          linarith
        · have h1 : u < j + 1 := Nat.lt_floor_add_one u
          have h2 : y0 y - a < (j + 1) * d i := by
            rw [hudef, div_lt_iff₀ (hd0 i)] at h1; exact h1
          linarith
      have htdiam : ∀ n, ediam (t n) ≤ r := by
        intro n
        simp only [htdef]
        split_ifs
        · exact (hQdiam _ _).trans
            ((ENNReal.ofReal_le_ofReal (by linarith [hdδ n.unpair.1])).trans hδr)
        · rw [ediam_empty]; exact zero_le
      refine iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htdiam ?_))
      -- the sum estimate
      have hterm : ∀ n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ((m + 1 : ℕ) : ℝ)) ≤
          ediam (t n) ^ (m + 1) := fun n => by
        rw [ENNReal.rpow_natCast]; exact iSup_le fun _ => le_rfl
      have hinner : ∀ i, ∑' j, ediam (t (Nat.pair i j)) ^ (m + 1) ≤
          ENNReal.ofReal (2 ^ (m + 2)) * (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
        intro i
        have hsupp : ∀ j ∉ Finset.range (k i), ediam (t (Nat.pair i j)) ^ (m + 1) = 0 := by
          intro j hj
          rw [Finset.mem_range, not_lt] at hj
          rw [htpair, ite_eq_right (by omega), ediam_empty, zero_pow (by omega)]
        rw [tsum_eq_sum hsupp]
        calc ∑ j ∈ Finset.range (k i), ediam (t (Nat.pair i j)) ^ (m + 1)
            ≤ ∑ j ∈ Finset.range (k i), ENNReal.ofReal (2 * d i) ^ (m + 1) := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [Finset.mem_range] at hj
              rw [htpair, ite_eq_left hj]
              exact pow_le_pow_left₀ zero_le (hQdiam i j) _
          _ = ENNReal.ofReal ((k i : ℝ) * (2 * d i) ^ (m + 1)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
                ENNReal.ofReal_pow (by have := hd0 i; positivity)]
          _ ≤ ENNReal.ofReal (2 ^ (m + 2) * (D i ^ m + ε / 2 / 2 ^ i)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hdi := hd0 i
              calc (k i : ℝ) * (2 * d i) ^ (m + 1) ≤ 2 / d i * (2 * d i) ^ (m + 1) := by
                    gcongr; exact hk i
                _ = 2 ^ (m + 2) * d i ^ m := by
                    field_simp; ring
                _ ≤ 2 ^ (m + 2) * (D i ^ m + ε / 2 / 2 ^ i) := by gcongr; exact hdm i
          _ = ENNReal.ofReal (2 ^ (m + 2)) *
                (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
              rw [ENNReal.ofReal_mul (by positivity), hCeq i,
                ← ENNReal.ofReal_pow (hD0 i), ← ENNReal.ofReal_add (pow_nonneg (hD0 i) _)
                  (by positivity)]
      have hgeom : ∑' i : ℕ, ENNReal.ofReal (ε / 2 / 2 ^ i) = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' ε),
          tsum_geometric_two']
      calc ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ((m + 1 : ℕ) : ℝ))
          ≤ ∑' n, ediam (t n) ^ (m + 1) := ENNReal.tsum_le_tsum hterm
        _ = ∑' p : ℕ × ℕ, ediam (t (Nat.pair p.1 p.2)) ^ (m + 1) :=
            (Nat.pairEquiv.tsum_eq (fun n => ediam (t n) ^ (m + 1))).symm
        _ = ∑' i, ∑' j, ediam (t (Nat.pair i j)) ^ (m + 1) :=
            ENNReal.tsum_prod (f := fun i j => ediam (t (Nat.pair i j)) ^ (m + 1))
        _ ≤ ∑' i, ENNReal.ofReal (2 ^ (m + 2)) *
              (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) :=
            ENNReal.tsum_le_tsum hinner
        _ = ENNReal.ofReal (2 ^ (m + 2)) * (∑' i, ediam (C i) ^ m +
              ∑' i : ℕ, ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ ≤ ENNReal.ofReal (2 ^ (m + 2)) * (ENNReal.ofReal ε + ENNReal.ofReal ε) := by
            rw [hgeom]; gcongr
        _ = ENNReal.ofReal (2 ^ (m + 3) * ε) := by
            rw [← ENNReal.ofReal_add hε0.le hε0.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεη
        _ = (η : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    exact measure_mono_null hsub (measure_iUnion_null hstrip)
theorem Submission.iwl_cr_hp_injective_pieces : ∀ (P m : ℕ) (A : Set (Eucl P)), MeasurableSet A → CountablyRectifiable m A → ∃ (G : ℕ → Eucl m → Eucl P) (B : ℕ → Set (Eucl m)), (∀ p, ∃ K : ℝ≥0, LipschitzWith K (G p)) ∧ (∀ p, MeasurableSet (B p)) ∧ (∀ p, InjOn (G p) (B p)) ∧ (∀ p, ∀ b ∈ B p, DifferentiableAt ℝ (G p) b) ∧ (∀ p, G p '' B p ⊆ A) ∧ (∀ p, MeasurableSet (G p '' B p)) ∧ Pairwise (Function.onFun Disjoint fun p => G p '' B p) ∧ (μHE[m] : Measure (Eucl P)) (A \ ⋃ p, G p '' B p) = 0 := by
  intro P m A hA hM
  -- Step 1: `A ⊆ M₀ ∪ ⋃_j F_j(ℝᵐ)` with `Hᵐ(M₀) = 0` and every `F_j` Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 2: lower-bound constants for injective linear maps.
  have hchoice : ∀ L : Eucl m →L[ℝ] Eucl P, ∃ δ : ℝ≥0, 0 < δ ∧ ∃ k : ℝ, 0 < k ∧
      (Function.Injective L → ∀ (t : Set (Eucl m)) (g : Eucl m → Eucl P),
        ApproximatesLinearOn g L t δ → ∀ b ∈ t, ∀ b' ∈ t, k * ‖b - b'‖ ≤ ‖g b - g b'‖) := by
    intro L
    by_cases hL : Function.Injective L
    · obtain ⟨K, hKpos, hK⟩ := (L : Eucl m →ₗ[ℝ] Eucl P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hL)
      have hK0 : (0 : ℝ) < K := hKpos
      refine ⟨(2 * K)⁻¹, by positivity, (2 * (K : ℝ))⁻¹, by positivity,
        fun _ t g hg b hb b' hb' => ?_⟩
      have h1 : ‖b - b'‖ ≤ K * ‖L (b - b')‖ := by
        have := hK.le_mul_dist b b'
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe, map_sub] using this
      have h2 : ‖g b - g b' - L (b - b')‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖b - b'‖ := hg b hb b' hb'
      have h3 : ‖L (b - b')‖ ≤ ‖g b - g b'‖ + ‖g b - g b' - L (b - b')‖ := by
        have := norm_sub_le (g b - g b') (g b - g b' - L (b - b'))
        simpa using this
      push_cast at h2
      have h4 : ‖b - b'‖ / K ≤ ‖L (b - b')‖ := by
        rw [div_le_iff₀ hK0]; linarith
      have h5 : (2 * (K : ℝ))⁻¹ * ‖b - b'‖ = ‖b - b'‖ / K - (2 * (K : ℝ))⁻¹ * ‖b - b'‖ := by
        field_simp; ring
      linarith
    · exact ⟨1, one_pos, 1, one_pos, fun h => (hL h).elim⟩
  choose δ hδpos k hkpos hk using hchoice
  -- Step 3: the regular set `R_j` of `F_j` (differentiability points with injective derivative)
  -- is Borel, as injective linear maps form an open set; partition it into injective pieces.
  set R : ℕ → Set (Eucl m) :=
    fun j => {b | DifferentiableAt ℝ (F j) b ∧ Function.Injective (fderiv ℝ (F j) b)} with hRdef
  have hRmeas : ∀ j, MeasurableSet (R j) := fun j =>
    (measurableSet_of_differentiableAt ℝ (F j)).inter
      (ContinuousLinearMap.isOpen_injective.measurableSet.preimage (measurable_fderiv ℝ (F j)))
  have hpart : ∀ j, ∃ (t : ℕ → Set (Eucl m)),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ R j) ∧ R j ⊆ ⋃ i, t i ∧
      ∀ i, InjOn (F j) (t i) := by
    intro j
    rcases eq_empty_or_nonempty (R j) with hR | hR
    · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun _ => empty_subset _,
        by rw [hR]; exact empty_subset _, fun i => injOn_empty _⟩
    obtain ⟨t, Al, -, ht, hcov, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) (R j) (fderiv ℝ (F j))
        (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) δ (fun L => (hδpos L).ne')
    refine ⟨fun i => R j ∩ t i, fun i => (hRmeas j).inter (ht i), fun i => inter_subset_left,
      ?_, ?_⟩
    · intro b hb
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hb)
      exact mem_iUnion.2 ⟨i, hb, hi⟩
    · intro i b hb b' hb' hbb
      obtain ⟨y, hy, hAy⟩ := hactual hR i
      have hlow := hk (Al i) (hAy ▸ hy.2) (R j ∩ t i) (F j) (happrox i) b hb b' hb'
      rw [hbb, sub_self, norm_zero] at hlow
      have h0 : ‖b - b'‖ ≤ 0 := by
        have := hkpos (Al i)
        nlinarith [norm_nonneg (b - b')]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  choose t ht_meas ht_sub ht_cov ht_inj using hpart
  -- Step 4: enumeration of the pieces by `Nat.unpair`.
  set Gp : ℕ → Eucl m → Eucl P := fun p => F p.unpair.1 with hGpdef
  set Sp : ℕ → Set (Eucl m) := fun p => t p.unpair.1 p.unpair.2 with hSpdef
  have hGpL : ∀ p, ∃ K : ℝ≥0, LipschitzWith K (Gp p) := fun p => hF _
  have hSpm : ∀ p, MeasurableSet (Sp p) := fun p => ht_meas _ _
  have hSpinj : ∀ p, InjOn (Gp p) (Sp p) := fun p => ht_inj _ _
  have hSpdiff : ∀ p, ∀ b ∈ Sp p, DifferentiableAt ℝ (Gp p) b := fun p b hb =>
    (ht_sub _ _ hb).1
  have hGpc : ∀ p, Continuous (Gp p) := fun p => by
    obtain ⟨K, hK⟩ := hGpL p; exact hK.continuous
  have himgm : ∀ p, MeasurableSet (Gp p '' Sp p) := fun p =>
    (hSpm p).image_of_continuousOn_injOn (hGpc p).continuousOn (hSpinj p)
  -- Step 5: the exceptional set `N = M₀ ∪ ⋃_j F_j(ℝᵐ ∖ R_j)` is `Hᵐ`-null.
  -- Local estimate: if `f` is `s²`-close on `S` to a linear `Λ` with `Λ e = 0`, `|e| = 1`, then
  -- compressing `ℝᵐ` by the factor `s` in the direction `e` (`T`, with `Lᵐ(T S) = s Lᵐ(S)`)
  -- makes `f ∘ T⁻¹` `(‖Λ‖ + s)`-Lipschitz on `T S`, so `Hᵐ(f S) ≤ (‖Λ‖ + s)ᵐ s Lᵐ(S)`.
  have hpiece : ∀ (f : Eucl m → Eucl P) (Λ : Eucl m →L[ℝ] Eucl P) (S : Set (Eucl m)) (s : ℝ≥0),
      0 < s → s ≤ 1 → ¬ Function.Injective Λ → ApproximatesLinearOn f Λ S (s ^ 2) →
      (μHE[m] : Measure (Eucl P)) (f '' S) ≤
        ((‖Λ‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m * ((s : ℝ≥0∞) * volume S) := by
    intro f Λ S s hs0 hs1 hΛ happ
    obtain ⟨v, hv0, hΛv⟩ : ∃ v, v ≠ 0 ∧ Λ v = 0 := by
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, Λ x = Λ y ∧ x ≠ y := by
        simpa [Function.Injective] using hΛ
      exact ⟨x - y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩
    set e : Eucl m := ‖v‖⁻¹ • v with he_def
    have he : ‖e‖ = 1 := norm_smul_inv_norm hv0
    have hΛe : Λ e = 0 := by rw [he_def, map_smul, hΛv, smul_zero]
    have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    have hs0' : (0 : ℝ) < s := hs0
    have hs1' : (s : ℝ) ≤ 1 := hs1
    set T : Eucl m →L[ℝ] Eucl m :=
      ContinuousLinearMap.id ℝ (Eucl m) + ((s : ℝ) - 1) • (innerSL ℝ e).smulRight e with hT_def
    set T' : Eucl m →L[ℝ] Eucl m :=
      ContinuousLinearMap.id ℝ (Eucl m) + ((s : ℝ)⁻¹ - 1) • (innerSL ℝ e).smulRight e
      with hT'_def
    have hTx : ∀ x, T x = x + (((s : ℝ) - 1) * inner ℝ e x) • e := by
      intro x
      simp [T, smul_smul]
    have hT'x : ∀ x, T' x = x + (((s : ℝ)⁻¹ - 1) * inner ℝ e x) • e := by
      intro x
      simp [T', smul_smul]
    have hT'T : ∀ x, T' (T x) = x := by
      intro x
      rw [hT'x, hTx, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul]
      have h0 : ((s : ℝ) - 1) * inner ℝ e x +
          ((s : ℝ)⁻¹ - 1) * (inner ℝ e x + ((s : ℝ) - 1) * inner ℝ e x * 1) = 0 := by
        field_simp
        ring
      rw [h0, zero_smul, add_zero]
    -- `det T = 1 + (s - 1) |e|² = s` (matrix determinant lemma in the standard basis).
    have hdet : LinearMap.det (T : Eucl m →ₗ[ℝ] Eucl m) = s := by
      set b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      rw [← LinearMap.det_toMatrix b]
      have hmat : LinearMap.toMatrix b b (T : Eucl m →ₗ[ℝ] Eucl m) =
          1 + Matrix.replicateCol Unit (fun i => ((s : ℝ) - 1) * e i) *
            Matrix.replicateRow Unit (fun i => e i) := by
        ext i j
        simp [T, LinearMap.toMatrix_apply, b, Matrix.one_apply, Matrix.mul_apply,
          EuclideanSpace.inner_single_right]
        ring
      rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
      have h2 := EuclideanSpace.real_norm_sq_eq e
      rw [he] at h2
      simp only [dotProduct]
      rw [show (∑ i, e i * (((s : ℝ) - 1) * e i)) = ((s : ℝ) - 1) * ∑ i, e i ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, ← h2]
      ring
    have hvol : (volume : Measure (Eucl m)) (T '' S) = (s : ℝ≥0∞) * volume S := by
      rw [Measure.addHaar_image_continuousLinearMap, hdet, abs_of_pos hs0',
        ENNReal.ofReal_coe_nnreal]
    -- For `x, x' ∈ S`: `Λ (x - x') = Λ (T x - T x')` as `Λ e = 0`, and
    -- `|x - x'| ≤ s⁻¹ |T x - T x'|`.
    have hlip : LipschitzOnWith (‖Λ‖₊ + s) (f ∘ T') (T '' S) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      simp only [Function.comp_apply, hT'T, dist_eq_norm, NNReal.coe_add, coe_nnnorm]
      have h1 : ‖f x - f x' - Λ (x - x')‖ ≤ (s : ℝ) ^ 2 * ‖x - x'‖ := by
        simpa using happ x hx x' hx'
      have hxx : x - x' = T' (T x - T x') := by rw [map_sub, hT'T, hT'T]
      have h2 : Λ (x - x') = Λ (T x - T x') := by
        rw [hxx, hT'x, map_add, map_smul, hΛe, smul_zero, add_zero]
      have h3 : ‖x - x'‖ ≤ (s : ℝ)⁻¹ * ‖T x - T x'‖ := by
        rw [hxx, hT'x]
        have hsi : 0 ≤ (s : ℝ)⁻¹ - 1 := sub_nonneg.mpr (one_le_inv₀ hs0' |>.mpr hs1')
        calc ‖(T x - T x') + (((s : ℝ)⁻¹ - 1) * inner ℝ e (T x - T x')) • e‖
            ≤ ‖T x - T x'‖ + ‖(((s : ℝ)⁻¹ - 1) * inner ℝ e (T x - T x')) • e‖ :=
              norm_add_le _ _
          _ = ‖T x - T x'‖ + ((s : ℝ)⁻¹ - 1) * |inner ℝ e (T x - T x')| := by
              rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hsi]
          _ ≤ ‖T x - T x'‖ + ((s : ℝ)⁻¹ - 1) * ‖T x - T x'‖ := by
              gcongr
              exact (abs_real_inner_le_norm e _).trans (by rw [he, one_mul])
          _ = (s : ℝ)⁻¹ * ‖T x - T x'‖ := by ring
      have h4 : ‖Λ (T x - T x')‖ ≤ ‖Λ‖ * ‖T x - T x'‖ := Λ.le_opNorm _
      calc ‖f x - f x'‖ ≤ ‖Λ (x - x')‖ + ‖f x - f x' - Λ (x - x')‖ := norm_le_insert' _ _
        _ ≤ ‖Λ‖ * ‖T x - T x'‖ + (s : ℝ) ^ 2 * ((s : ℝ)⁻¹ * ‖T x - T x'‖) :=
            add_le_add (by rw [h2]; exact h4) (h1.trans (by gcongr))
        _ = (‖Λ‖ + s) * ‖T x - T x'‖ := by field_simp
    have himg : f '' S = (f ∘ T') '' (T '' S) := by
      rw [image_image]
      exact image_congr fun x _ => by simp only [Function.comp_apply, hT'T]
    calc (μHE[m] : Measure (Eucl P)) (f '' S)
        = (μHE[m] : Measure (Eucl P)) ((f ∘ T') '' (T '' S)) := by rw [himg]
      _ ≤ ((‖Λ‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m * (μHE[m] : Measure (Eucl m)) (T '' S) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hlip
      _ = ((‖Λ‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m * ((s : ℝ≥0∞) * volume S) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvol]
  -- The image of the critical set of a Lipschitz map is `Hᵐ`-null: split the critical points
  -- in `B_r(0)` into countably many disjoint Borel pieces on which `f` is `s²`-close to its
  -- (non-injective) derivative at some point of the piece; then
  -- `Hᵐ(f(C ∩ B_r)) ≤ (L + 1)ᵐ s Lᵐ(B_r)` for every `s ∈ (0, 1]`.
  have hcrit : ∀ (f : Eucl m → Eucl P) (L : ℝ≥0), LipschitzWith L f →
      (μHE[m] : Measure (Eucl P))
        (f '' {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}) = 0 := by
    intro f L hf
    set C := {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}
    have hCr : ∀ r : ℕ, (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r)) = 0 := by
      intro r
      set V := (volume : Measure (Eucl m)) (ball 0 r)
      have hV : V ≠ ∞ := measure_ball_lt_top.ne
      have hbound : ∀ s : ℝ≥0, 0 < s → s ≤ 1 →
          (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r)) ≤
            ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V * s := by
        intro s hs0 hs1
        rcases (C ∩ ball (0 : Eucl m) r).eq_empty_or_nonempty with hC | hC
        · rw [hC, image_empty, measure_empty]
          exact bot_le
        obtain ⟨T, Λ, hTdisj, hTmeas, hCT, hTapprox, hTΛ⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (C ∩ ball 0 r)
            (fderiv ℝ f) (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => s ^ 2)
            (fun _ => pow_ne_zero 2 hs0.ne')
        have hpi : ∀ i, (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r ∩ T i)) ≤
            ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (ball (0 : Eucl m) r ∩ T i) := by
          intro i
          -- `Λ i = Df(y)` for a critical point `y`, so `Λ i` is not injective and `‖Λ i‖ ≤ L`.
          obtain ⟨y, hy, hΛy⟩ := hTΛ hC i
          have hΛinj : ¬ Function.Injective (Λ i) := by
            rw [hΛy]
            exact hy.1.2
          have hΛn : ‖Λ i‖₊ ≤ L := by
            rw [hΛy, ← NNReal.coe_le_coe, coe_nnnorm]
            exact norm_fderiv_le_of_lipschitz ℝ hf
          calc (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r ∩ T i))
              ≤ ((‖Λ i‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m *
                  ((s : ℝ≥0∞) * volume (C ∩ ball 0 r ∩ T i)) :=
                hpiece f (Λ i) _ s hs0 hs1 hΛinj (hTapprox i)
            _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m *
                  ((s : ℝ≥0∞) * volume (ball (0 : Eucl m) r ∩ T i)) := by
                gcongr
                exact inter_subset_right
            _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (ball (0 : Eucl m) r ∩ T i) := by
                ring
        calc (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r))
            ≤ (μHE[m] : Measure (Eucl P)) (⋃ i, f '' (C ∩ ball 0 r ∩ T i)) := by
              refine measure_mono ?_
              rintro _ ⟨x, hx, rfl⟩
              obtain ⟨i, hi⟩ := mem_iUnion.mp (hCT hx)
              exact mem_iUnion.mpr ⟨i, x, ⟨hx, hi⟩, rfl⟩
          _ ≤ ∑' i, (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r ∩ T i)) :=
              measure_iUnion_le _
          _ ≤ ∑' i, ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (ball (0 : Eucl m) r ∩ T i) :=
              ENNReal.tsum_le_tsum hpi
          _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (⋃ i, ball (0 : Eucl m) r ∩ T i) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (hTdisj hij).mono inter_subset_right inter_subset_right
              · exact fun i => measurableSet_ball.inter (hTmeas i)
          _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * V := by
              gcongr
              exact measure_mono (iUnion_subset fun i => inter_subset_left)
          _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V * s := by ring
      -- Let `s = 1 / (l + 1) → 0`.
      have hlim : Tendsto (fun l : ℕ => ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V * ((l + 1 : ℕ) : ℝ≥0∞)⁻¹)
          atTop (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
          (Or.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hV) :
            (0 : ℝ≥0∞) ≠ 0 ∨ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V ≠ ∞)
        rw [mul_zero] at h
        exact h
      refine le_antisymm (ge_of_tendsto' hlim fun l => ?_) bot_le
      have hl : ((l + 1 : ℕ) : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr l.succ_ne_zero
      have h := hbound ((l + 1 : ℕ) : ℝ≥0)⁻¹ (inv_pos.mpr (pos_iff_ne_zero.mpr hl))
        (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr l.succ_pos))
      rwa [ENNReal.coe_inv hl, ENNReal.coe_natCast] at h
    refine measure_mono_null ?_ (measure_iUnion_null hCr)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨r, x, ⟨hx, mem_ball_zero_iff.mpr hr⟩, rfl⟩
  set N := M₀ ∪ ⋃ j, F j '' (univ \ R j) with hNdef
  have hN : (μHE[m] : Measure (Eucl P)) N = 0 := by
    refine measure_union_null hM₀ (measure_iUnion_null fun j => ?_)
    obtain ⟨K, hK⟩ := hF j
    -- By Rademacher's theorem the non-differentiability set is `Lᵐ`-null, and `Hᵐ = Lᵐ` on
    -- `ℝᵐ`, so its image under the Lipschitz map `F_j` is `Hᵐ`-null.
    have hND : (volume : Measure (Eucl m)) {w | ¬ DifferentiableAt ℝ (F j) w} = 0 :=
      ae_iff.mp (hK.ae_differentiableAt (μ := volume))
    have hNDimg : (μHE[m] : Measure (Eucl P)) (F j '' {w | ¬ DifferentiableAt ℝ (F j) w}) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
        (hK.lipschitzOnWith (s := {w | ¬ DifferentiableAt ℝ (F j) w}))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m, hND, mul_zero] at h
      exact le_antisymm h bot_le
    refine measure_mono_null ?_ (measure_union_null (hcrit (F j) K hK) hNDimg)
    rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F j) w
    · exact Or.inl ⟨w, ⟨hd, fun hinj => hw ⟨hd, hinj⟩⟩, rfl⟩
    · exact Or.inr ⟨w, hd, rfl⟩
  -- Step 6: covering, `A ⊆ N ∪ ⋃_p G_p(S_p)`.
  have hcov2 : A ⊆ N ∪ ⋃ p, Gp p '' Sp p := by
    intro x hx
    rcases hcover hx with h0 | h1
    · exact Or.inl (Or.inl h0)
    · obtain ⟨j, b, rfl⟩ := mem_iUnion.1 h1
      by_cases hb : b ∈ R j
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (ht_cov j hb)
        refine Or.inr (mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
        simp only [hGpdef, hSpdef, Nat.unpair_pair]
        exact ⟨b, hi, rfl⟩
      · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, hb⟩, rfl⟩))
  -- Steps 7–8: disjointification and null remainder.
  set Ap : ℕ → Set (Eucl P) := disjointed fun p => A ∩ Gp p '' Sp p with hApdef
  set Bp : ℕ → Set (Eucl m) := fun p => Sp p ∩ Gp p ⁻¹' Ap p with hBpdef
  have hApm : ∀ p, MeasurableSet (Ap p) :=
    MeasurableSet.disjointed fun p => hA.inter (himgm p)
  have hApsub : ∀ p, Ap p ⊆ A ∩ Gp p '' Sp p := fun p => disjointed_subset _ p
  have himgB : ∀ p, Gp p '' Bp p = Ap p := by
    intro p
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb.2
    · intro hx
      obtain ⟨b, hb, rfl⟩ := ((hApsub p) hx).2
      exact ⟨b, ⟨hb, hx⟩, rfl⟩
  refine ⟨Gp, Bp, hGpL, fun p => (hSpm p).inter ((hApm p).preimage (hGpc p).measurable),
    fun p => (hSpinj p).mono inter_subset_left,
    fun p b hb => hSpdiff p b hb.1, fun p => by rw [himgB p]; exact fun x hx => ((hApsub p) hx).1,
    fun p => by rw [himgB p]; exact hApm p, ?_, ?_⟩
  · intro p q hpq
    simp only [Function.onFun, himgB]
    exact disjoint_disjointed _ hpq
  · simp only [himgB]
    rw [hApdef, iUnion_disjointed]
    refine measure_mono_null ?_ hN
    intro x ⟨hxA, hxU⟩
    rcases hcov2 hxA with hxN | hxG
    · exact hxN
    · exfalso
      obtain ⟨p, hp⟩ := mem_iUnion.1 hxG
      exact hxU (mem_iUnion.2 ⟨p, hxA, hp⟩)
/-- Gram determinant of the cylinder lift `G̃(v) = (v₀, G(v₁, …, v_m))` (the Jacobian step of the
Hausdorff product formula).  With `Λ(s, x) = (s, x)`, `pr₀ v = v₀` and `tl v = (v₁, …, v_m)`,
the chain rule gives `DG̃(w) = Λ ∘ (pr₀, DG(b) ∘ tl)`; as `⟨Λ(s, x), Λ(s', x')⟩ = s s' + ⟨x, x'⟩`,
the Gram matrix of `DG̃(w)` on the standard basis is `diag(1, Gram(DG(b)))`, and Laplace
expansion along row `0` gives `det Gram(DG̃(w)) = det Gram(DG(b))`. -/
theorem Submission.iwl_cr_hp_lift_gram_det : ∀ (P m : ℕ) (G : Eucl m → Eucl P) (Gt : Eucl (m + 1) → Eucl (P + 1)) (w : Eucl (m + 1)) (b : Eucl m), (∀ v : Eucl (m + 1), Gt v = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons (EuclideanSpace.equiv (Fin (m + 1)) ℝ v 0) (EuclideanSpace.equiv (Fin P) ℝ (G ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))))))) → b = (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ w)) → DifferentiableAt ℝ G b → (Matrix.of fun i j : Fin (m + 1) => inner ℝ (fderiv ℝ Gt w (EuclideanSpace.single i 1)) (fderiv ℝ Gt w (EuclideanSpace.single j 1))).det = (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G b (EuclideanSpace.single i 1)) (fderiv ℝ G b (EuclideanSpace.single j 1))).det := by
  intro P m G Gt w b hGt hb hd
  -- the linear lift `Λ(s, x) = (s, x₁, …, x_P)` and the tail map, as continuous linear maps
  let Λ : (ℝ × Eucl P) →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun q => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2))
      map_add' := by
        intro q q'
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp
      map_smul' := by
        intro c q
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp }
  have hΛ : ∀ (s : ℝ) (x : Eucl P), Λ (s, x) = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) := fun s x => rfl
  have hinnerΛ : ∀ (s s' : ℝ) (x x' : Eucl P),
      inner ℝ (Λ (s, x)) (Λ (s', x')) = s * s' + inner ℝ x x' := by
    intro s s' x x'
    rw [hΛ, hΛ]
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_succ, mul_comm]
  let tl : Eucl (m + 1) →L[ℝ] Eucl m := LinearMap.toContinuousLinearMap
    { toFun := fun v => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))
      map_add' := by intro v v'; ext k; simp [Fin.tail]
      map_smul' := by intro c v; ext k; simp [Fin.tail] }
  have htl : ∀ v : Eucl (m + 1), tl v = (EuclideanSpace.equiv (Fin m) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v)) := fun v => rfl
  set L := fderiv ℝ G b with hLdef
  set pr0 : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (m + 1)) with hpr0
  have hGt' : Gt = fun v => Λ (pr0 v, G (tl v)) := by
    funext v; rw [hGt]; rfl
  have hb' : tl w = b := by rw [hb]; rfl
  -- the derivative of the lift
  have hinner : HasFDerivAt (fun v => (pr0 v, G (tl v))) (pr0.prod (L.comp tl)) w := by
    refine pr0.hasFDerivAt.prodMk ?_
    have hG : HasFDerivAt G L (tl w) := by rw [hb']; exact hd.hasFDerivAt
    exact hG.comp w tl.hasFDerivAt
  have hD : fderiv ℝ Gt w = Λ.comp (pr0.prod (L.comp tl)) := by
    rw [hGt']
    exact (Λ.hasFDerivAt.comp w hinner).fderiv
  rw [hD]
  -- values on the standard basis
  have hpr0_zero : pr0 (EuclideanSpace.single 0 1) = 1 := by simp [hpr0]
  have hpr0_succ : ∀ j : Fin m, pr0 (EuclideanSpace.single j.succ 1) = 0 := by
    intro j; simp [hpr0, Fin.succ_ne_zero]
  have htl_zero : tl (EuclideanSpace.single 0 1) = 0 := by
    ext k; simp [htl, Fin.tail, Fin.succ_ne_zero]
  have htl_succ : ∀ j : Fin m, tl (EuclideanSpace.single j.succ 1) = EuclideanSpace.single j 1 := by
    intro j; ext k
    rw [htl]
    by_cases hk : k = j
    · subst hk; simp [Fin.tail]
    · simp [Fin.tail, hk]
  have hentry : ∀ i j : Fin (m + 1),
      inner ℝ ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single i 1))
        ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)) =
      pr0 (EuclideanSpace.single i 1) * pr0 (EuclideanSpace.single j 1) +
        inner ℝ (L (tl (EuclideanSpace.single i 1))) (L (tl (EuclideanSpace.single j 1))) := by
    intro i j
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply]
    exact hinnerΛ _ _ _ _
  -- Laplace expansion along the first row of the block-diagonal Gram matrix
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hrest : ∀ k : Fin m, (-1 : ℝ) ^ (k.succ : ℕ) *
      (Matrix.of fun i j : Fin (m + 1) => inner ℝ ((Λ.comp (pr0.prod (L.comp tl)))
        (EuclideanSpace.single i 1)) ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)))
        0 k.succ *
      ((Matrix.of fun i j : Fin (m + 1) => inner ℝ ((Λ.comp (pr0.prod (L.comp tl)))
        (EuclideanSpace.single i 1)) ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)))
        |>.submatrix Fin.succ k.succ.succAbove).det = 0 := by
    intro k
    rw [Matrix.of_apply, hentry, hpr0_zero, hpr0_succ, htl_zero, map_zero, inner_zero_left]
    ring
  rw [Finset.sum_eq_zero (fun k _ => hrest k), add_zero]
  rw [Matrix.of_apply, hentry, hpr0_zero, htl_zero, map_zero, inner_zero_left, Fin.succAbove_zero]
  simp only [pow_zero, Fin.val_zero, mul_one, add_zero, one_mul]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hentry, hpr0_succ, hpr0_succ, htl_succ, htl_succ]
  ring

/-- Product formula `Hᵐ⁺¹ ⌞ (ℝ × G(B)) = L¹ ⊗ Hᵐ ⌞ G(B)` for one injective Lipschitz piece
`G : ℝᵐ → ℝ^P` on a Borel set `B`, with `Φ(s, x) = (s, x)` and `π(s, x) = x`: for Borel `g ≥ 0`,
`φ(s) = ∫_{G(B)} g(Φ(s, x)) dHᵐ(x)` is measurable and `∫_{π⁻¹(G(B))} g dHᵐ⁺¹ = ∫_ℝ φ(s) ds`.
Both sides come from the injective area formula `∫_{f(S)} u dHᵏ = ∫_S J(Df) · u ∘ f` (proved
inline: partition `S` into pieces where `f` is almost linear, compare with the linear area
formula `Hᵏ(L E) = J(L) |E|`, `J(L) = √det ⟨L eᵢ, L eⱼ⟩`, and let the error go to `0`): in
dimension `m` for `G` on `B`, and in dimension `m + 1` for the lift `G̃(v) = Φ(v₀, G(v₁, …, v_m))`
on `ℝ × B`, whose Jacobian equals that of `G` (`iwl_cr_hp_lift_gram_det`); Tonelli in
`v = (v₀, (v₁, …, v_m))` finishes. -/
theorem Submission.iwl_cr_hp_piece_product :
    ∀ (P m : ℕ) (G : Eucl m → Eucl P) (K : ℝ≥0) (B : Set (Eucl m)), LipschitzWith K G →
      MeasurableSet B → InjOn G B → (∀ b ∈ B, DifferentiableAt ℝ G b) →
      ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g →
        Measurable (fun s : ℝ => ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) ∧
        ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B},
            g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) =
          ∫⁻ s : ℝ, ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) := by
  -- the area Jacobian `J L = √(det Gram(L))` of a linear map `L : ℝᵏ → ℝ^Q`
  obtain ⟨J, hJ⟩ : ∃ J : ∀ k Q : ℕ, (Eucl k →L[ℝ] Eucl Q) → ℝ, ∀ k Q L, J k Q L =
      Real.sqrt (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det :=
    ⟨fun k Q L => Real.sqrt (Matrix.of fun i j : Fin k =>
          inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det, fun _ _ _ => rfl⟩
  -- the Jacobian `J L = √det ⟨L eᵢ, L eⱼ⟩` is continuous in `L`
  have hJc :
      ∀ k Q : ℕ, Continuous (J k Q) := by
    intro k Q
    have hJk : J k Q = fun L => Real.sqrt (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det :=
      funext (hJ k Q)
    rw [hJk]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.of_apply]
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- `J L = 0` when `L` is not injective
  have hJ0 :
      ∀ (k Q : ℕ) (L : Eucl k →L[ℝ] Eucl Q), ¬ Function.Injective L → J k Q L = 0 := by
    intro k Q L hL
    obtain ⟨u, hu0, hLu⟩ : ∃ u : Eucl k, u ≠ 0 ∧ L u = 0 := by
      simp only [Function.Injective, not_forall] at hL
      obtain ⟨a, b, hab, hne⟩ := hL
      exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩
    rw [hJ]
    have hdet : (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨u.ofLp, ?_, ?_⟩
      · intro h
        apply hu0
        ext i
        simp [h]
      · ext i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        have hsum : u = ∑ j, u.ofLp j • EuclideanSpace.single j (1 : ℝ) := by
          conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr u]
          simp
        have : inner ℝ (L (EuclideanSpace.single i 1)) (L u) = 0 := by rw [hLu, inner_zero_right]
        rw [hsum, map_sum, inner_sum] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, inner_smul_right, mul_comm]
    rw [hdet, Real.sqrt_zero]
  -- linear area formula: `Hᵏ(L E) = J L · |E|` (factor `L` through a linear isometry)
  have hLAF :
      ∀ (k Q : ℕ) (L : Eucl k →L[ℝ] Eucl Q), Function.Injective L →
      ∀ E : Set (Eucl k), (μHE[k] : Measure (Eucl Q)) (L '' E) = ENNReal.ofReal (J k Q L) * volume E := by
    intro k Q L hL E
    set V := LinearMap.range (L : Eucl k →ₗ[ℝ] Eucl Q) with hVdef
    have hV : Module.finrank ℝ V = k := by
      rw [LinearMap.finrank_range_of_inj (f := (L : Eucl k →ₗ[ℝ] Eucl Q)) hL]
      exact finrank_euclideanSpace_fin
    let b : OrthonormalBasis (Fin k) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
    let e : V ≃ₗᵢ[ℝ] Eucl k := b.repr
    let M : Eucl k →ₗ[ℝ] Eucl k :=
      e.toLinearEquiv.toLinearMap ∘ₗ (L : Eucl k →ₗ[ℝ] Eucl Q).rangeRestrict
    let ι : Eucl k →ₗᵢ[ℝ] Eucl Q := V.subtypeₗᵢ.comp e.symm.toLinearIsometry
    have hfac : ∀ x, L x = ι (M x) := by
      intro x
      simp [ι, M]
    have himg : L '' E = ι '' (M '' E) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hfac x)
    rw [himg, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
    congr 2
    rw [hJ]
    set bE := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis with hbE
    have hgram : (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))) =
        (LinearMap.toMatrix bE bE M).transpose * LinearMap.toMatrix bE bE M := by
      ext i j
      rw [Matrix.of_apply, hfac, hfac, LinearIsometry.inner_map_map, Matrix.mul_apply,
        EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Matrix.transpose_apply, LinearMap.toMatrix_apply, star_trivial]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [bE, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
      ring
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, ← sq,
      Real.sqrt_sq_eq_abs]
  -- the lift `L_η x = (L x, η x)`: `|L_η v| ≥ |L v|, η |v|` and `J L_η → J L` as `η → 0`
  have hlift :
      ∀ (k Q : ℕ) (L : Eucl k →L[ℝ] Eucl Q) (κ : ℝ), 0 < κ → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ Lη : Eucl k →L[ℝ] Eucl (Q + k),
        (∀ v, ‖L v‖ ≤ ‖Lη v‖) ∧ (∀ v, η * ‖v‖ ≤ ‖Lη v‖) ∧ J k (Q + k) Lη ≤ J k Q L + κ := by
    intro k Q L κ hκ
    let lift : ℝ → (Eucl k →L[ℝ] Eucl (Q + k)) := fun η => LinearMap.toContinuousLinearMap
      { toFun := fun x => (EuclideanSpace.equiv (Fin (Q + k)) ℝ).symm
          (Fin.append (EuclideanSpace.equiv (Fin Q) ℝ (L x)) (η • EuclideanSpace.equiv (Fin k) ℝ x))
        map_add' := by
          intro x y
          ext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
        map_smul' := by
          intro c x
          ext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [mul_left_comm] }
    have hlift : ∀ η x, lift η x = (EuclideanSpace.equiv (Fin (Q + k)) ℝ).symm
        (Fin.append (EuclideanSpace.equiv (Fin Q) ℝ (L x)) (η • EuclideanSpace.equiv (Fin k) ℝ x)) :=
      fun η x => rfl
    have hinner : ∀ η x y, inner ℝ (lift η x) (lift η y) =
        inner ℝ (L x) (L y) + η ^ 2 * inner ℝ x y := by
      intro η x y
      rw [hlift, hlift]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_add]
      simp [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hnorm : ∀ η x, ‖lift η x‖ ^ 2 = ‖L x‖ ^ 2 + η ^ 2 * ‖x‖ ^ 2 := by
      intro η x
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, hinner]
    set G0 : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1)) with hG0
    have hgram : ∀ η : ℝ, (Matrix.of fun i j : Fin k => inner ℝ (lift η (EuclideanSpace.single i 1))
        (lift η (EuclideanSpace.single j 1))) = Matrix.of fun i j => G0 i j +
          η ^ 2 * (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
      intro η
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, hinner, EuclideanSpace.inner_single_left]
      by_cases hij : i = j
      · subst hij
        simp [hG0]
      · simp [hG0, hij]
    set F : ℝ → ℝ := fun η => (Matrix.of fun i j => G0 i j +
        η ^ 2 * (1 : Matrix (Fin k) (Fin k) ℝ) i j).det with hF
    have hFc : Continuous F := by
      refine Continuous.matrix_det ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.of_apply]
      fun_prop
    have hF0 : F 0 = G0.det := by
      simp only [hF]
      congr 1
      ext i j
      simp
    have hcont : Continuous fun η => Real.sqrt (F η) := Real.continuous_sqrt.comp hFc
    obtain ⟨η₀, hη₀, hη₀'⟩ := Metric.continuous_iff.mp hcont 0 κ hκ
    refine ⟨η₀, hη₀, fun η hη hηlt => ⟨lift η, ?_, ?_, ?_⟩⟩
    · intro v
      have h := hnorm η v
      have : ‖L v‖ ^ 2 ≤ ‖lift η v‖ ^ 2 := by
        rw [h]
        have : 0 ≤ η ^ 2 * ‖v‖ ^ 2 := by positivity
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    · intro v
      have h := hnorm η v
      have : (η * ‖v‖) ^ 2 ≤ ‖lift η v‖ ^ 2 := by
        rw [h, mul_pow]
        have : 0 ≤ ‖L v‖ ^ 2 := by positivity
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this
    · rw [hJ, hJ, hgram, ← hG0]
      have h := hη₀' η (by rw [Real.dist_eq, sub_zero, abs_of_pos hη]; exact hηlt)
      rw [Real.dist_eq] at h
      have h' : Real.sqrt (F η) - Real.sqrt (F 0) < κ := lt_of_abs_lt h
      rw [hF0] at h'
      simp only [hF] at h'
      linarith
  -- Lipschitz comparison of images: `Hᵏ(g₂ S) ≤ cᵏ Hᵏ(g₁ S)` when `|Δg₂| ≤ c |Δg₁|` on `S`
  have hcomp :
      ∀ (k Q₁ Q₂ : ℕ) (g₁ : Eucl k → Eucl Q₁) (g₂ : Eucl k → Eucl Q₂)
      (S : Set (Eucl k)) (c : ℝ≥0), InjOn g₁ S →
      (∀ x ∈ S, ∀ x' ∈ S, ‖g₂ x - g₂ x'‖ ≤ c * ‖g₁ x - g₁ x'‖) →
      (μHE[k] : Measure (Eucl Q₂)) (g₂ '' S) ≤
        (c : ℝ≥0∞) ^ k * (μHE[k] : Measure (Eucl Q₁)) (g₁ '' S) := by
    intro k Q₁ Q₂ g₁ g₂ S c hinj hle
    set h : Eucl Q₁ → Eucl Q₂ := fun y => g₂ (Function.invFunOn g₁ S y) with hhdef
    have hh : ∀ x ∈ S, h (g₁ x) = g₂ x := fun x hx => by
      simp only [hhdef]
      rw [hinj.leftInvOn_invFunOn hx]
    have himg : h '' (g₁ '' S) = g₂ '' S := by
      rw [image_image]
      exact image_congr hh
    have hlip : LipschitzOnWith c h (g₁ '' S) := by
      refine LipschitzOnWith.of_dist_le_mul ?_
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      rw [hh x hx, hh x' hx', dist_eq_norm, dist_eq_norm]
      exact hle x hx x' hx'
    have hH := hlip.hausdorffMeasure_image_le (d := (k : ℝ)) (Nat.cast_nonneg k)
    rw [ENNReal.rpow_natCast, himg] at hH
    rw [Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
    exact mul_le_mul_right hH _
  -- the two-sided estimate on a partition into almost-linear pieces
  have hkey :
      ∀ (k Q : ℕ) (f : Eucl k → Eucl Q) (K : ℝ≥0) (S : Set (Eucl k)), LipschitzWith K f →
      MeasurableSet S → InjOn f S → (∀ x ∈ S, DifferentiableAt ℝ f x) →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ κ : ℝ, 0 < κ →
        (μHE[k] : Measure (Eucl Q)) (f '' S) ≤ ENNReal.ofReal (1 + δ) ^ k *
          ((∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x))) + 2 * ENNReal.ofReal κ * volume S) ∧
        (∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x))) ≤
          ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' S) +
            ENNReal.ofReal κ * volume S := by
    intro k Q f K S hf hS hinj hdiff δ hδ hδ2 κ hκ
    -- uniform continuity of `J` on the ball of radius `K`
    obtain ⟨ρ0, hρ0, hρ0'⟩ : ∃ ρ0 > 0, ∀ L ∈ closedBall (0 : Eucl k →L[ℝ] Eucl Q) K,
        ∀ L' ∈ closedBall (0 : Eucl k →L[ℝ] Eucl Q) K, dist L L' < ρ0 →
          dist (J k Q L) (J k Q L') < κ :=
      Metric.uniformContinuousOn_iff.mp ((isCompact_closedBall _ _).uniformContinuousOn_of_continuous
        (hJc k Q).continuousOn) κ hκ
    have hDf : ∀ x, fderiv ℝ f x ∈ closedBall (0 : Eucl k →L[ℝ] Eucl Q) K := fun x => by
      rw [mem_closedBall, dist_zero_right]
      exact norm_fderiv_le_of_lipschitz ℝ hf
    -- a dense sequence of linear maps, and the pre-pieces
    obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq (Eucl k →L[ℝ] Eucl Q)
    set P : ℕ → Set (Eucl k) := fun n => S ∩ fderiv ℝ f ⁻¹' ball (D n) (ρ0 / 2) with hPdef
    have hPm : ∀ n, MeasurableSet (P n) := fun n =>
      hS.inter (measurable_fderiv ℝ f measurableSet_ball)
    have hPcov : S ⊆ ⋃ n, P n := by
      intro x hx
      obtain ⟨n, hn⟩ := (Metric.denseRange_iff.mp hD) (fderiv ℝ f x) (ρ0 / 2) (by positivity)
      exact mem_iUnion.mpr ⟨n, hx, by rw [mem_preimage, mem_ball]; exact hn⟩
    set P' : ℕ → Set (Eucl k) := disjointed P with hP'eq
    have hP'm : ∀ n, MeasurableSet (P' n) := MeasurableSet.disjointed hPm
    have hP'P : ∀ n, P' n ⊆ P n := disjointed_subset P
    have hP'S : ∀ n, P' n ⊆ S := fun n => (hP'P n).trans inter_subset_left
    have hP'cov : S ⊆ ⋃ n, P' n := by rw [hP'eq, iUnion_disjointed]; exact hPcov
    have hP'disj : Pairwise (Function.onFun Disjoint P') := disjoint_disjointed P
    -- the scale `ρ A` attached to each linear map
    have hρex : ∀ A : Eucl k →L[ℝ] Eucl Q, ∃ ρ : ℝ, 0 < ρ ∧
        (Function.Injective A → ∀ v, ρ * ‖v‖ ≤ ‖A v‖) ∧
        ∃ Aρ : Eucl k →L[ℝ] Eucl (Q + k), (∀ v, ‖A v‖ ≤ ‖Aρ v‖) ∧ (∀ v, ρ * ‖v‖ ≤ ‖Aρ v‖) ∧
          J k (Q + k) Aρ ≤ J k Q A + κ := by
      intro A
      obtain ⟨η₀, hη₀, hη₀'⟩ := hlift k Q A κ hκ
      by_cases hA : Function.Injective A
      · obtain ⟨C, hC, hCA⟩ := (A : Eucl k →ₗ[ℝ] Eucl Q).exists_antilipschitzWith
          (LinearMap.ker_eq_bot.mpr hA)
        have hCpos : (0 : ℝ) < C := hC
        set ρ := min (η₀ / 2) (1 / (C : ℝ)) with hρ
        have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
        obtain ⟨Aρ, h1, h2, h3⟩ := hη₀' ρ hρpos (lt_of_le_of_lt (min_le_left _ _) (by linarith))
        refine ⟨ρ, hρpos, fun _ v => ?_, Aρ, h1, h2, h3⟩
        have hv : ‖v‖ ≤ C * ‖A v‖ := by
          have := hCA.le_mul_dist v 0
          simpa [dist_zero_right] using this
        calc ρ * ‖v‖ ≤ (1 / C) * ‖v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
          _ ≤ (1 / C) * (C * ‖A v‖) := mul_le_mul_of_nonneg_left hv (by positivity)
          _ = ‖A v‖ := by field_simp
      · obtain ⟨Aρ, h1, h2, h3⟩ := hη₀' (η₀ / 2) (by positivity) (by linarith)
        exact ⟨η₀ / 2, by positivity, fun h => absurd h hA, Aρ, h1, h2, h3⟩
    choose ρ hρpos hρinj Aρ hAρ1 hAρ2 hAρJ using hρex
    set r : (Eucl k →L[ℝ] Eucl Q) → ℝ≥0 := fun A => Real.toNNReal (δ * ρ A) with hrdef
    have hrpos : ∀ A, r A ≠ 0 := fun A => by
      simp only [hrdef, ne_eq, Real.toNNReal_eq_zero, not_le]
      exact mul_pos hδ (hρpos A)
    have hr : ∀ A, (r A : ℝ) = δ * ρ A := fun A => Real.coe_toNNReal _ (mul_pos hδ (hρpos A)).le
    -- the partition of each pre-piece
    have hpart : ∀ n, ∃ (t : ℕ → Set (Eucl k)) (A : ℕ → (Eucl k →L[ℝ] Eucl Q)),
        Pairwise (Function.onFun Disjoint t) ∧ (∀ j, MeasurableSet (t j)) ∧ P' n ⊆ ⋃ j, t j ∧
        (∀ j, ApproximatesLinearOn f (A j) (P' n ∩ t j) (r (A j))) ∧
        ((P' n).Nonempty → ∀ j, ∃ y ∈ P' n, A j = fderiv ℝ f y) := fun n =>
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (P' n) (fderiv ℝ f)
        (fun x hx => (hdiff x (hP'S n hx)).hasFDerivAt.hasFDerivWithinAt) r hrpos
    choose t A ht_disj ht_meas ht_cov ht_approx ht_der using hpart
    -- the pieces
    set Sp : ℕ × ℕ → Set (Eucl k) := fun p => P' p.1 ∩ t p.1 p.2 with hSpdef
    have hSpm : ∀ p, MeasurableSet (Sp p) := fun p => (hP'm p.1).inter (ht_meas p.1 p.2)
    have hSpS : ∀ p, Sp p ⊆ S := fun p => inter_subset_left.trans (hP'S p.1)
    have hSpdisj : Pairwise (Function.onFun Disjoint Sp) := by
      rintro ⟨n, j⟩ ⟨n', j'⟩ hne
      by_cases hn : n = n'
      · subst hn
        have hj : j ≠ j' := fun h => hne (by rw [h])
        exact Disjoint.mono inter_subset_right inter_subset_right (ht_disj n hj)
      · exact Disjoint.mono inter_subset_left inter_subset_left (hP'disj hn)
    have hSpcov : S = ⋃ p, Sp p := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp (hP'cov hx)
        obtain ⟨j, hj⟩ := mem_iUnion.mp (ht_cov n hn)
        exact mem_iUnion.mpr ⟨(n, j), hn, hj⟩
      · exact iUnion_subset hSpS
    -- the three quantities as sums over the pieces
    have hXsum : (μHE[k] : Measure (Eucl Q)) (f '' S) =
        ∑' p, (μHE[k] : Measure (Eucl Q)) (f '' Sp p) := by
      conv_lhs => rw [hSpcov, image_iUnion]
      refine measure_iUnion ?_ ?_
      · intro p q hpq
        refine Set.disjoint_left.mpr ?_
        rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
        have : x' = x := hinj (hSpS q hx') (hSpS p hx) hxx'
        subst this
        exact Set.disjoint_left.mp (hSpdisj hpq) hx hx'
      · intro p
        exact (hSpm p).image_of_continuousOn_injOn hf.continuous.continuousOn (hinj.mono (hSpS p))
    have hYsum : ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) =
        ∑' p, ∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
      conv_lhs => rw [hSpcov]
      exact lintegral_iUnion hSpm hSpdisj _
    have hVsum : volume S = ∑' p, volume (Sp p) := by
      conv_lhs => rw [hSpcov]
      exact measure_iUnion hSpdisj hSpm
    -- the estimates on one piece
    have hpiece : ∀ p, (μHE[k] : Measure (Eucl Q)) (f '' Sp p) ≤ ENNReal.ofReal (1 + δ) ^ k *
          ((∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
            2 * ENNReal.ofReal κ * volume (Sp p)) ∧
        (∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))) ≤
          ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' Sp p) +
            ENNReal.ofReal κ * volume (Sp p) := by
      rintro ⟨n, j⟩
      rcases (Sp (n, j)).eq_empty_or_nonempty with hemp | hne
      · simp [hemp]
      obtain ⟨y, hyP, hAy⟩ := ht_der n ⟨hne.some, hne.some_mem.1⟩ j
      have happ := ht_approx n j
      generalize A n j = A0 at happ hAy
      have hJclose : ∀ x ∈ Sp (n, j), dist (J k Q (fderiv ℝ f x)) (J k Q A0) < κ := by
        intro x hx
        refine hρ0' _ (hDf x) _ (by rw [hAy]; exact hDf y) ?_
        have hx1 : dist (fderiv ℝ f x) (D n) < ρ0 / 2 := (hP'P n hx.1).2
        have hy1 : dist (fderiv ℝ f y) (D n) < ρ0 / 2 := (hP'P n hyP).2
        rw [hAy]
        calc dist (fderiv ℝ f x) (fderiv ℝ f y)
            ≤ dist (fderiv ℝ f x) (D n) + dist (D n) (fderiv ℝ f y) := dist_triangle _ _ _
          _ < ρ0 / 2 + ρ0 / 2 := by rw [dist_comm (D n)]; exact add_lt_add hx1 hy1
          _ = ρ0 := by ring
      have happ' : ∀ x ∈ Sp (n, j), ∀ x' ∈ Sp (n, j),
          ‖f x - f x' - A0 (x - x')‖ ≤ δ * ρ A0 * ‖x - x'‖ := by
        intro x hx x' hx'
        have := happ x hx x' hx'
        rwa [hr] at this
      -- upper bound through the lift `Aρ A0`
      have hup : ∀ x ∈ Sp (n, j), ∀ x' ∈ Sp (n, j),
          ‖f x - f x'‖ ≤ (Real.toNNReal (1 + δ) : ℝ) * ‖Aρ A0 x - Aρ A0 x'‖ := by
        intro x hx x' hx'
        rw [Real.coe_toNNReal _ (by linarith), ← map_sub]
        have h1 := happ' x hx x' hx'
        have h2 := hAρ1 A0 (x - x')
        have h3 := hAρ2 A0 (x - x')
        calc ‖f x - f x'‖ = ‖(f x - f x' - A0 (x - x')) + A0 (x - x')‖ := by congr 1; abel
          _ ≤ ‖f x - f x' - A0 (x - x')‖ + ‖A0 (x - x')‖ := norm_add_le _ _
          _ ≤ δ * ρ A0 * ‖x - x'‖ + ‖Aρ A0 (x - x')‖ := add_le_add h1 h2
          _ ≤ δ * ‖Aρ A0 (x - x')‖ + ‖Aρ A0 (x - x')‖ := by nlinarith
          _ = (1 + δ) * ‖Aρ A0 (x - x')‖ := by ring
      have hAρinj : Function.Injective (Aρ A0) := by
        intro v w hvw
        have h := hAρ2 A0 (v - w)
        rw [map_sub, hvw, sub_self, norm_zero] at h
        have h' : ‖v - w‖ = 0 :=
          le_antisymm (by nlinarith [hρpos A0, norm_nonneg (v - w)]) (norm_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp h')
      have hX_le : (μHE[k] : Measure (Eucl Q)) (f '' Sp (n, j)) ≤ ENNReal.ofReal (1 + δ) ^ k *
          (ENNReal.ofReal (J k (Q + k) (Aρ A0)) * volume (Sp (n, j))) := by
        have := hcomp k (Q + k) Q (Aρ A0) f (Sp (n, j)) (Real.toNNReal (1 + δ)) hAρinj.injOn hup
        rwa [hLAF k (Q + k) (Aρ A0) hAρinj] at this
      -- comparison of `J (Df x)` with `J A0` on the piece
      have hJx_le : ∀ x ∈ Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x)) ≤
          ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ := by
        intro x hx
        have h := hJclose x hx
        rw [Real.dist_eq] at h
        exact (ENNReal.ofReal_le_ofReal (by linarith [abs_lt.mp h])).trans ENNReal.ofReal_add_le
      have hA_le : ∀ x ∈ Sp (n, j), ENNReal.ofReal (J k Q A0) ≤
          ENNReal.ofReal (J k Q (fderiv ℝ f x)) + ENNReal.ofReal κ := by
        intro x hx
        have h := hJclose x hx
        rw [Real.dist_eq] at h
        exact (ENNReal.ofReal_le_ofReal (by linarith [abs_lt.mp h])).trans ENNReal.ofReal_add_le
      have hY_le : ∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x)) ≤
          (ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) * volume (Sp (n, j)) := by
        calc _ ≤ ∫⁻ x in Sp (n, j), (ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) :=
              setLIntegral_mono' (hSpm _) (fun x hx => hJx_le x hx)
          _ = _ := setLIntegral_const _ _
      have hA_int : ENNReal.ofReal (J k Q A0) * volume (Sp (n, j)) ≤
          (∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
            ENNReal.ofReal κ * volume (Sp (n, j)) := by
        calc ENNReal.ofReal (J k Q A0) * volume (Sp (n, j))
            = ∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q A0) := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in Sp (n, j), (ENNReal.ofReal (J k Q (fderiv ℝ f x)) + ENNReal.ofReal κ) :=
              setLIntegral_mono' (hSpm _) (fun x hx => hA_le x hx)
          _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      -- lower bound through `A0` itself
      have hlow : ENNReal.ofReal (J k Q A0) * volume (Sp (n, j)) ≤
          ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' Sp (n, j)) := by
        by_cases hinjA : Function.Injective A0
        · rw [← hLAF k Q A0 hinjA]
          refine hcomp k Q Q f A0 (Sp (n, j)) (Real.toNNReal (1 - δ)⁻¹) (hinj.mono (hSpS _)) ?_
          intro x hx x' hx'
          have h1δ : 0 < 1 - δ := by linarith
          rw [Real.coe_toNNReal _ (by positivity), ← map_sub]
          have h1 := happ' x hx x' hx'
          have h2 := hρinj A0 hinjA (x - x')
          have h3 : ‖A0 (x - x')‖ ≤ ‖f x - f x'‖ + δ * ‖A0 (x - x')‖ := by
            calc ‖A0 (x - x')‖ = ‖(f x - f x') - (f x - f x' - A0 (x - x'))‖ := by
                  congr 1; abel
              _ ≤ ‖f x - f x'‖ + ‖f x - f x' - A0 (x - x')‖ := norm_sub_le _ _
              _ ≤ ‖f x - f x'‖ + δ * ρ A0 * ‖x - x'‖ := by linarith
              _ ≤ ‖f x - f x'‖ + δ * ‖A0 (x - x')‖ := by nlinarith
          rw [inv_mul_eq_div, le_div_iff₀ h1δ]
          linarith
        · rw [hJ0 k Q A0 hinjA, ENNReal.ofReal_zero, zero_mul]
          exact bot_le
      constructor
      · calc (μHE[k] : Measure (Eucl Q)) (f '' Sp (n, j))
            ≤ ENNReal.ofReal (1 + δ) ^ k *
                (ENNReal.ofReal (J k (Q + k) (Aρ A0)) * volume (Sp (n, j))) := hX_le
          _ ≤ ENNReal.ofReal (1 + δ) ^ k *
                ((ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) * volume (Sp (n, j))) := by
            gcongr
            exact (ENNReal.ofReal_le_ofReal (hAρJ A0)).trans ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal (1 + δ) ^ k *
                ((∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
                  2 * ENNReal.ofReal κ * volume (Sp (n, j))) := by
            gcongr
            rw [add_mul]
            calc _ ≤ ((∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
                    ENNReal.ofReal κ * volume (Sp (n, j))) +
                    ENNReal.ofReal κ * volume (Sp (n, j)) := add_le_add hA_int le_rfl
              _ = _ := by ring
      · calc _ ≤ (ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) * volume (Sp (n, j)) := hY_le
          _ = ENNReal.ofReal (J k Q A0) * volume (Sp (n, j)) +
                ENNReal.ofReal κ * volume (Sp (n, j)) := add_mul _ _ _
          _ ≤ _ := add_le_add hlow le_rfl
    -- summing over the pieces
    constructor
    · rw [hXsum, hYsum, hVsum]
      calc ∑' p, (μHE[k] : Measure (Eucl Q)) (f '' Sp p)
          ≤ ∑' p, ENNReal.ofReal (1 + δ) ^ k *
              ((∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
                2 * ENNReal.ofReal κ * volume (Sp p)) := ENNReal.tsum_le_tsum fun p => (hpiece p).1
        _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    · rw [hXsum, hYsum, hVsum]
      calc ∑' p, ∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))
          ≤ ∑' p, (ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' Sp p) +
              ENNReal.ofReal κ * volume (Sp p)) := ENNReal.tsum_le_tsum fun p => (hpiece p).2
        _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  -- injective area formula for sets: `Hᵏ(f S) = ∫_S J(Df)`
  have hC7 :
      ∀ (k Q : ℕ) (f : Eucl k → Eucl Q) (K : ℝ≥0) (S : Set (Eucl k)), LipschitzWith K f →
      MeasurableSet S → InjOn f S → (∀ x ∈ S, DifferentiableAt ℝ f x) →
      (μHE[k] : Measure (Eucl Q)) (f '' S) = ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
    intro k Q f K S hf hS hinj hdiff
    -- the finite-volume case
    have hfin : ∀ T ⊆ S, MeasurableSet T → volume T < ∞ →
        (μHE[k] : Measure (Eucl Q)) (f '' T) = ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
      intro T hTS hT hTfin
      have hkeyT := hkey k Q f K T hf hT (hinj.mono hTS) (fun x hx => hdiff x (hTS hx))
      have hXfin : (μHE[k] : Measure (Eucl Q)) (f '' T) < ∞ := by
        have h := hcomp k k Q id f T K (injOn_id T) (fun x _ x' _ => by
          simpa [dist_eq_norm] using hf.dist_le_mul x x')
        rw [image_id, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
        exact h.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hTfin)
      have hVne : volume T ≠ ∞ := hTfin.ne
      -- `X ≤ Y`
      have hle1 : (μHE[k] : Measure (Eucl Q)) (f '' T) ≤
          ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
        set Y := ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) with hY
        have ha : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 + δ) ^ k) (𝓝 0) (𝓝 1) := by
          have : Continuous (fun δ : ℝ => ENNReal.ofReal (1 + δ) ^ k) :=
            (ENNReal.continuous_pow k).comp
              (ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id))
          simpa using this.tendsto 0
        have hb : Tendsto (fun δ : ℝ => Y + 2 * ENNReal.ofReal δ * volume T) (𝓝 0) (𝓝 Y) := by
          have : Continuous (fun δ : ℝ => Y + 2 * ENNReal.ofReal δ * volume T) :=
            continuous_const.add ((ENNReal.continuous_mul_const hVne).comp
              ((ENNReal.continuous_const_mul (by simp)).comp ENNReal.continuous_ofReal))
          simpa using this.tendsto 0
        have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 + δ) ^ k *
            (Y + 2 * ENNReal.ofReal δ * volume T)) (𝓝[>] 0) (𝓝 Y) := by
          have := ENNReal.Tendsto.mul ha (Or.inl one_ne_zero) hb (Or.inr ENNReal.one_ne_top)
          rw [one_mul] at this
          exact this.mono_left nhdsWithin_le_nhds
        refine ge_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
        exact (hkeyT δ hδ.1 hδ.2 δ hδ.1).1
      -- `Y ≤ X`
      have hle2 : ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) ≤
          (μHE[k] : Measure (Eucl Q)) (f '' T) := by
        set X := (μHE[k] : Measure (Eucl Q)) (f '' T) with hX
        have ha : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 - δ)⁻¹ ^ k) (𝓝 0) (𝓝 1) := by
          have h1 : ContinuousAt (fun δ : ℝ => (1 - δ)⁻¹) 0 :=
            (continuous_const.sub continuous_id).continuousAt.inv₀ (by norm_num)
          have h2 : ContinuousAt (fun δ : ℝ => ENNReal.ofReal (1 - δ)⁻¹ ^ k) 0 :=
            (ENNReal.continuous_pow k).continuousAt.comp
              (ENNReal.continuous_ofReal.continuousAt.comp h1)
          simpa using h2.tendsto
        have hb : Tendsto (fun δ : ℝ => ENNReal.ofReal δ * volume T) (𝓝 0) (𝓝 0) := by
          have : Continuous (fun δ : ℝ => ENNReal.ofReal δ * volume T) :=
            (ENNReal.continuous_mul_const hVne).comp ENNReal.continuous_ofReal
          simpa using this.tendsto 0
        have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 - δ)⁻¹ ^ k * X +
            ENNReal.ofReal δ * volume T) (𝓝[>] 0) (𝓝 X) := by
          have h1 := ENNReal.Tendsto.mul_const ha (Or.inr hXfin.ne)
          have := h1.add hb
          rw [one_mul, add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        refine ge_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
        exact (hkeyT δ hδ.1 hδ.2 δ hδ.1).2
      exact le_antisymm hle1 hle2
    -- exhaustion by balls
    set T : ℕ → Set (Eucl k) := fun j => S ∩ closedBall 0 j with hTdef
    have hTmono : Monotone T := fun a b hab =>
      inter_subset_inter_right _ (closedBall_subset_closedBall (by exact_mod_cast hab))
    have hTU : S = ⋃ j, T j := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
        exact mem_iUnion.mpr ⟨j, hx, by rw [mem_closedBall, dist_zero_right]; exact hj⟩
      · exact iUnion_subset fun j => inter_subset_left
    have hTm : ∀ j, MeasurableSet (T j) := fun j => hS.inter measurableSet_closedBall
    calc (μHE[k] : Measure (Eucl Q)) (f '' S)
        = ⨆ j, (μHE[k] : Measure (Eucl Q)) (f '' T j) := by
          rw [hTU, image_iUnion]
          exact Monotone.measure_iUnion (fun a b hab => image_mono (hTmono hab))
      _ = ⨆ j, ∫⁻ x in T j, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
          refine iSup_congr fun j => hfin (T j) inter_subset_left (hTm j) ?_
          exact (measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top
      _ = ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
          rw [hTU]
          simp_rw [← withDensity_apply _ (hTm _)]
          rw [← withDensity_apply _ (MeasurableSet.iUnion hTm)]
          exact (Monotone.measure_iUnion hTmono).symm
  -- injective area formula for nonnegative weights
  have hAF :
      ∀ (k Q : ℕ) (f : Eucl k → Eucl Q) (K : ℝ≥0) (S : Set (Eucl k)), LipschitzWith K f →
      MeasurableSet S → InjOn f S → (∀ x ∈ S, DifferentiableAt ℝ f x) →
      ∀ u : Eucl Q → ℝ≥0∞, Measurable u →
        ∫⁻ y in f '' S, u y ∂(μHE[k] : Measure (Eucl Q)) =
          ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) * u (f x) := by
    intro k Q f K S hf hS hinj hdiff u hu
    have hφm : Measurable fun x => ENNReal.ofReal (J k Q (fderiv ℝ f x)) :=
      ENNReal.measurable_ofReal.comp ((hJc k Q).measurable.comp (measurable_fderiv ℝ f))
    have hfm : Measurable f := hf.continuous.measurable
    have hmeas : (μHE[k] : Measure (Eucl Q)).restrict (f '' S) =
        ((volume.restrict S).withDensity fun x => ENNReal.ofReal (J k Q (fderiv ℝ f x))).map f := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.map_apply hfm hT, withDensity_apply _ (hfm hT),
        Measure.restrict_restrict (hfm hT), inter_comm T, ← image_inter_preimage,
        inter_comm (f ⁻¹' T)]
      exact hC7 k Q f K (S ∩ f ⁻¹' T) hf (hS.inter (hfm hT)) (hinj.mono inter_subset_left)
        (fun x hx => hdiff x hx.1)
    rw [hmeas, lintegral_map hu hfm]
    exact lintegral_withDensity_eq_lintegral_mul (volume.restrict S) hφm (hu.comp hfm)
  intro P m G K B hG hB hinj hdiff g hg
  -- notation
  set Φ : ℝ → Eucl P → Eucl (P + 1) := fun s x =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))
    with hΦdef
  have hΦc : Continuous fun q : ℝ × Eucl P => Φ q.1 q.2 := by
    have : Continuous fun q : ℝ × Eucl P =>
        (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2) : Fin (P + 1) → ℝ) := by
      refine continuous_pi fun k => ?_
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
    exact (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp this
  -- (8.1): the area formula in dimension `m`
  set Jm : Eucl m → ℝ≥0∞ := fun b => ENNReal.ofReal (J m P (fderiv ℝ G b)) with hJmdef
  have hJmm : Measurable Jm :=
    ENNReal.measurable_ofReal.comp ((hJc m P).measurable.comp (measurable_fderiv ℝ G))
  set H : ℝ × Eucl m → ℝ≥0∞ := fun q => Jm q.2 * g (Φ q.1 (G q.2)) with hHdef
  have hHm : Measurable H := by
    refine (hJmm.comp measurable_snd).mul (hg.comp ?_)
    exact (hΦc.comp (continuous_fst.prodMk (hG.continuous.comp continuous_snd))).measurable
  have hinner : ∀ s : ℝ, ∫⁻ b in B, H (s, b) =
      ∫⁻ x in G '' B, g (Φ s x) ∂(μHE[m] : Measure (Eucl P)) := fun s =>
    (hAF m P G K B hG hB hinj hdiff (fun x => g (Φ s x))
      (hg.comp (hΦc.comp (continuous_const.prodMk continuous_id)).measurable)).symm
  refine ⟨?_, ?_⟩
  · -- measurability of the inner integral
    have hmeas : Measurable fun s : ℝ => ∫⁻ b, H (s, b) ∂((volume : Measure (Eucl m)).restrict B) :=
      hHm.lintegral_prod_right'
    have heq : (fun s : ℝ => ∫⁻ b, H (s, b) ∂((volume : Measure (Eucl m)).restrict B)) =
        fun s => ∫⁻ x in G '' B, g (Φ s x) ∂(μHE[m] : Measure (Eucl P)) := funext hinner
    rw [heq] at hmeas
    exact hmeas
  · -- the lift
    set e1 := EuclideanSpace.equiv (Fin (m + 1)) ℝ with he1
    set tl : Eucl (m + 1) → Eucl m := fun v =>
      (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (e1 v)) with htldef
    have htlc : Continuous tl := by
      have : Continuous fun v : Eucl (m + 1) => Fin.tail (e1 v) :=
        continuous_pi fun i => (continuous_apply i.succ).comp e1.continuous
      exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp this
    set Gt : Eucl (m + 1) → Eucl (P + 1) := fun v => Φ (e1 v 0) (G (tl v)) with hGtdef
    set Bt : Set (Eucl (m + 1)) := tl ⁻¹' B with hBtdef
    have hBt : MeasurableSet Bt := hB.preimage htlc.measurable
    -- norm identities
    have hnormΦ : ∀ (s : ℝ) (x : Eucl P), ‖Φ s x‖ ^ 2 = s ^ 2 + ‖x‖ ^ 2 := by
      intro s x
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp [hΦdef]
    have hΦsub : ∀ (s s' : ℝ) (x x' : Eucl P), Φ s x - Φ s' x' = Φ (s - s') (x - x') := by
      intro s s' x x'
      ext k
      refine Fin.cases ?_ (fun j => ?_) k <;> simp [hΦdef]
    have hnormw : ∀ v : Eucl (m + 1), ‖v‖ ^ 2 = (e1 v 0) ^ 2 + ‖tl v‖ ^ 2 := by
      intro v
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp [htldef, he1, Fin.tail]
    have htlsub : ∀ v v' : Eucl (m + 1), tl v - tl v' = tl (v - v') := by
      intro v v'; ext k; simp [htldef, he1, Fin.tail]
    -- (i) Lipschitz
    have hGtL : LipschitzWith (max 1 K) Gt := by
      refine LipschitzWith.of_dist_le_mul fun v v' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : ‖Gt v - Gt v'‖ ^ 2 ≤ ((max 1 K : ℝ≥0) * ‖v - v'‖) ^ 2 := by
        simp only [hGtdef]
        rw [hΦsub, hnormΦ, mul_pow, hnormw (v - v')]
        have hK : ‖G (tl v) - G (tl v')‖ ≤ K * ‖tl v - tl v'‖ := by
          have := hG.dist_le_mul (tl v) (tl v')
          rwa [dist_eq_norm, dist_eq_norm] at this
        have hKm : (K : ℝ) ≤ (max 1 K : ℝ≥0) := by exact_mod_cast le_max_right 1 K
        have h1m : (1 : ℝ) ≤ (max 1 K : ℝ≥0) := by exact_mod_cast le_max_left 1 K
        have he0 : e1 v 0 - e1 v' 0 = e1 (v - v') 0 := by simp
        rw [he0, ← htlsub]
        have hA : (e1 (v - v') 0) ^ 2 ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 * (e1 (v - v') 0) ^ 2 := by
          have : (1 : ℝ) ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 := by nlinarith
          nlinarith [sq_nonneg (e1 (v - v') 0)]
        have hB2 : ‖G (tl v) - G (tl v')‖ ^ 2 ≤
            ((max 1 K : ℝ≥0) : ℝ) ^ 2 * ‖tl v - tl v'‖ ^ 2 := by
          have h0 : 0 ≤ ‖G (tl v) - G (tl v')‖ := norm_nonneg _
          have h2 : ‖G (tl v) - G (tl v')‖ ≤ ((max 1 K : ℝ≥0) : ℝ) * ‖tl v - tl v'‖ :=
            hK.trans (mul_le_mul_of_nonneg_right hKm (norm_nonneg _))
          calc ‖G (tl v) - G (tl v')‖ ^ 2 ≤ (((max 1 K : ℝ≥0) : ℝ) * ‖tl v - tl v'‖) ^ 2 :=
                pow_le_pow_left₀ h0 h2 2
            _ = _ := by ring
        nlinarith
      have h0 : 0 ≤ ((max 1 K : ℝ≥0) : ℝ) * ‖v - v'‖ := by positivity
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp h1
    -- coordinates of `Gt`
    have hπGt : ∀ v, (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ (Gt v))) = G (tl v) := by
      intro v; ext k; simp [hGtdef, hΦdef, Fin.tail]
    -- (ii) injectivity
    have hinjt : InjOn Gt Bt := by
      intro v hv v' hv' hvv
      have h0 : e1 v 0 = e1 v' 0 := by
        have := congrArg (fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ) y 0) hvv
        simpa [hGtdef, hΦdef] using this
      have htl : tl v = tl v' := by
        have := congrArg (fun y => (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) hvv
        simp only [hπGt] at this
        exact hinj hv hv' this
      ext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa [he1] using h0
      · have := congrArg (fun z => z j) htl
        simpa [htldef, he1, Fin.tail] using this
    -- (iii) image
    have himg : Gt '' Bt = {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B} := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        simp only [mem_ofPred_eq, hπGt]
        exact ⟨tl v, hv, rfl⟩
      · rintro ⟨b, hb, hby⟩
        refine ⟨e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin m) ℝ b)), ?_, ?_⟩
        · have : tl (e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
              (EuclideanSpace.equiv (Fin m) ℝ b))) = b := by
            ext k; simp [htldef, he1, Fin.tail]
          simp only [hBtdef, mem_preimage, this]
          exact hb
        · have htlb : tl (e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
              (EuclideanSpace.equiv (Fin m) ℝ b))) = b := by
            ext k; simp [htldef, he1, Fin.tail]
          simp only [hGtdef, htlb, hby]
          ext k
          refine Fin.cases ?_ (fun j => ?_) k
          · simp [hΦdef, he1]
          · simp [hΦdef, Fin.tail]
    -- differentiability of the lift on `Bt`
    have hdiffGt : ∀ v ∈ Bt, DifferentiableAt ℝ Gt v := by
      let Λ : (ℝ × Eucl P) →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
        { toFun := fun q => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2))
          map_add' := by
            intro q q'
            ext k
            refine Fin.cases ?_ (fun j => ?_) k <;> simp
          map_smul' := by
            intro c q
            ext k
            refine Fin.cases ?_ (fun j => ?_) k <;> simp }
      let tlL : Eucl (m + 1) →L[ℝ] Eucl m := LinearMap.toContinuousLinearMap
        { toFun := fun v => (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))
          map_add' := by intro v v'; ext k; simp [Fin.tail]
          map_smul' := by intro c v; ext k; simp [Fin.tail] }
      let pr0 : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (m + 1))
      have hGt' : Gt = fun v => Λ (pr0 v, G (tlL v)) := by
        funext v
        rfl
      intro v hv
      rw [hGt']
      exact Λ.differentiableAt.comp v
        (pr0.differentiableAt.prodMk ((hdiff (tl v) hv).comp v tlL.differentiableAt))
    -- (iv) Jacobians
    have hjac : ∀ v ∈ Bt, J (m + 1) (P + 1) (fderiv ℝ Gt v) = J m P (fderiv ℝ G (tl v)) := by
      intro v hv
      rw [hJ, hJ,
        Submission.iwl_cr_hp_lift_gram_det P m G Gt v (tl v) (fun v => rfl) rfl (hdiff _ hv)]
    -- area formula in dimension `m + 1`
    have harea1 := hAF (m + 1) (P + 1) Gt (max 1 K) Bt hGtL hBt hinjt hdiffGt g hg
    rw [himg] at harea1
    rw [harea1]
    have hcongr : ∫⁻ v in Bt, ENNReal.ofReal (J (m + 1) (P + 1) (fderiv ℝ Gt v)) * g (Gt v) =
        ∫⁻ v in Bt, H (e1 v 0, tl v) := by
      refine setLIntegral_congr_fun hBt (fun v hv => ?_)
      rw [hjac v hv]
    rw [hcongr]
    -- the coordinate split
    set Ψ : Eucl (m + 1) → ℝ × Eucl m := fun v => (e1 v 0, tl v) with hΨdef
    have hΨ : MeasurePreserving Ψ (volume : Measure (Eucl (m + 1)))
        ((volume : Measure ℝ).prod (volume : Measure (Eucl m))) := by
      have h1 := PiLp.volume_preserving_ofLp (ι := Fin (m + 1))
      have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0
      have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_toLp (ι := Fin m))
      have h := h3.comp (h2.comp h1)
      convert h using 1
      funext v
      simp only [Function.comp_apply, hΨdef, htldef, he1]
      ext <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    have hpre : Bt = Ψ ⁻¹' (univ ×ˢ B) := by
      ext v; simp [hBtdef, hΨdef]
    rw [hpre, hΨ.setLIntegral_comp_preimage (MeasurableSet.univ.prod hB) hHm,
      ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod H hHm.aemeasurable]
    exact lintegral_congr fun s => hinner s

/-- Product formula for Hausdorff measure on rectifiable sets (Federer 3.2.23), with
`π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`, so `{y : π y ∈ S} = Φ(ℝ × S)`:
(a) if `Hᵐ(N) = 0` then `Hᵐ⁺¹(ℝ × N) = 0`; (b) if `A ⊆ ℝ^P` is `Hᵐ`-measurable and countably
`m`-rectifiable, then `∫_{ℝ × A} g dHᵐ⁺¹ = ∫_ℝ ∫_A g(Φ(s, x)) dHᵐ(x) ds` for Borel `g ≥ 0`, i.e.
`Hᵐ⁺¹ ⌞ (ℝ × A) = L¹ ⊗ Hᵐ ⌞ A`.  (a) is `iwl_cr_hp_cylinder_null`.  For (b), `A` is replaced by a
Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`, which by (a) changes neither side.  Up to an `Hᵐ`-null set,
`A₀` is the disjoint union of the Borel pieces `G p '' B p` with `G p` Lipschitz and injective on
`B p` (`iwl_cr_hp_injective_pieces`); the formula holds on each piece
(`iwl_cr_hp_piece_product`), and both sides are countably additive over the pieces, the cylinder
over the remainder being `Hᵐ⁺¹`-null by (a).  The local finiteness of `Hᵐ ⌞ A` is not needed. -/
theorem Submission.iwl_cr_hausdorff_product_formula : (∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) ∧ (∀ (P m : ℕ) (A : Set (Eucl P)), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) := by
  refine ⟨Submission.iwl_cr_hp_cylinder_null, ?_⟩
  intro P m A hA hrect _hfin g hg
  -- `pr y = (y₁, …, y_P)`, so the cylinder `ℝ × S` over `S ⊆ ℝ^P` is `pr ⁻¹' S`
  set pr : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hpr : Measurable pr := by
    have : Continuous fun y : Eucl (P + 1) => Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y) :=
      continuous_pi fun i => (continuous_apply i.succ).comp
        (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
    exact ((EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp this).measurable
  have hcyl : ∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1))) (pr ⁻¹' N) = 0 :=
    Submission.iwl_cr_hp_cylinder_null P m
  show ∫⁻ y in pr ⁻¹' A, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = _
  -- (1) a Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`; by (a) neither side changes
  obtain ⟨A₀, hA₀A, hA₀m, hA₀ae⟩ := hA.exists_measurable_subset_ae_eq
  have hL₀ : pr ⁻¹' A =ᵐ[(μHE[m + 1] : Measure (Eucl (P + 1)))] pr ⁻¹' A₀ :=
    ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy) (hcyl (A \ A₀) (ae_eq_set.1 hA₀ae).2),
      measure_mono_null (fun y hy => (hy.2 (hA₀A hy.1)).elim) measure_empty⟩
  -- (2) disjoint Borel pieces `G p '' B p` of `A₀`, Lipschitz and injective, up to a null set
  obtain ⟨G, B, hGL, hBm, hinj, hdiff, hsub, hGBm, hdisj, hrest⟩ :=
    Submission.iwl_cr_hp_injective_pieces P m A₀ hA₀m (hrect.mono hA₀A)
  choose K hK using hGL
  have hpiece := fun p => Submission.iwl_cr_hp_piece_product P m (G p) (K p) (B p) (hK p)
    (hBm p) (hinj p) (hdiff p) g hg
  have hU : A₀ =ᵐ[(μHE[m] : Measure (Eucl P))] ⋃ p, G p '' B p :=
    ae_eq_set.2 ⟨hrest,
      measure_mono_null (fun x hx => (hx.2 (iUnion_subset hsub hx.1)).elim) measure_empty⟩
  have hÛ : pr ⁻¹' A₀ =ᵐ[(μHE[m + 1] : Measure (Eucl (P + 1)))] ⋃ p, pr ⁻¹' (G p '' B p) := by
    rw [← preimage_iUnion]
    exact ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy) (hcyl (A₀ \ ⋃ p, G p '' B p) hrest),
      measure_mono_null (fun y hy => (hy.2 (iUnion_subset hsub hy.1)).elim) measure_empty⟩
  -- (3) both sides are countably additive over the pieces, and agree on each piece
  have hR : ∀ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) =
      ∑' p, ∫⁻ x in G p '' B p, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) := by
    intro s
    rw [setLIntegral_congr hA₀ae.symm, setLIntegral_congr hU, lintegral_iUnion hGBm hdisj]
  rw [setLIntegral_congr hL₀, setLIntegral_congr hÛ,
    lintegral_iUnion (fun p => hpr (hGBm p)) (fun p q hpq => (hdisj hpq).preimage pr),
    lintegral_congr hR, lintegral_tsum fun p => (hpiece p).1.aemeasurable]
  exact tsum_congr fun p => (hpiece p).2

/-- **The product `[[(0,1)]] × X` of an integer multiplicity current (Simon Ch. 6, 3.2(2)).**
Write `Φ(s, x) = (s, x)`, `π(Φ(s, x)) = x`, `e₀ = Φ(1, 0)` and `X = τ(M, θ, ξ)` with `θ ∈ ℕ` on
`M`, so `θ ≥ 1` on `M`.  The product formula for Hausdorff measure (Federer 3.2.23), in the
measure form `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)`, makes `((0,1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` a
rectifiable triple; `Z := τ((0,1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` is a current (integrable,
sequentially continuous), integer multiplicity since `θ ∘ π ∈ ℕ`, and Fubini gives
`Z(η) = ∫₀¹ τ(M, θ, ξ)(φ(s)) ds = ∫₀¹ X(φ(s)) ds`. -/
theorem Submission.iwl_cr_interval_product_im : ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m), IsIntegerMultiplicity X → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1), IsIntegerMultiplicity Z ∧ ∀ (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), (φ s : DifferentialForm (Eucl P) m) x v = (η : DifferentialForm (Eucl (P + 1)) (m + 1)) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s) := by
  intro P m X hX
  -- Step 1: `X = τ(M, θ, ξ)` with `θ` positive and integer-valued on `M`, hence `θ ≥ 1` on `M`.
  obtain ⟨M, θ, ξ, hT, hθN, hXτ⟩ := hX
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθN x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hpos)
  -- Step 2: the product formula in measure form, `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)` for every
  -- `Hᵐ`-measurable, countably `m`-rectifiable `A` with `Hᵐ⌞A` locally finite.
  have hMP : ∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) →
      CountablyRectifiable m A →
      (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) →
      (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} =
      Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
        ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A)) :=
    fun A hA hAr hAK => Submission.iwl_cr_ip_restrict_preimage_eq_map P m A hAK
      (Submission.iwl_cr_hausdorff_product_formula.2 P m A hA hAr hAK)
  -- Step 3: the product triple `((0,1) × M, θ ∘ π, ξ')`, with `ξ'(Φ(s, x))(α) = ξ(x)(ℒα)` for
  -- the contraction `ℒα = α(e₀, ι ·)`.
  obtain ⟨ξ', hT', hξ'⟩ := Submission.iwl_cr_ip_product_triple P m hMP M θ ξ hT hθ1
  -- Step 4: `Z := τ((0,1) × M, θ ∘ π, ξ')` is a current.
  obtain ⟨Z, hZ⟩ := Submission.br_loc_tauAction_current (P + 1) (m + 1) univ _ _ ξ' hT'
  -- Step 5: `Z` is integer multiplicity, since `θ(π y) ∈ ℕ` for `y ∈ (0,1) × M`.
  refine ⟨Z, ⟨_, _, ξ', hT', fun y hy => hθN _ hy.1, hZ⟩, ?_⟩
  -- Step 6: the slice formula (Fubini for `H^{m+1}⌞((0,1) × M) = Φ_#(L¹⌞(0,1) ⊗ Hᵐ⌞M)`), whose
  -- integrability hypothesis holds as `η` is continuous with compact support; then use
  -- `X = τ(M, θ, ξ)`.
  intro η φ hφ
  have hint := (Submission.ltg_tau_integrable (P + 1) (m + 1) univ _ _ ξ' hT').2
    (η : DifferentialForm (Eucl (P + 1)) (m + 1)) η.property.1.1.continuous η.property.1.2
    η.property.2
  rw [hZ η, Submission.iwl_cr_ip_slice_formula P m hMP M θ ξ ξ' hT hθ1 hξ' η
    (fun s => (φ s : DifferentialForm (Eucl P) m)) hint hφ]
  exact intervalIntegral.integral_congr fun s _ => (hXτ (φ s)).symm

/-- The cone `0 ⨯ X` over an integer multiplicity `X` with `spt X ⊆ B̄_R(0)` is integer
multiplicity.  `Z = [[(0,1)]] × X` is integer multiplicity with compact support, so `H_push` gives
its integer multiplicity push-forward `S` by the cone map `h(y) = y₀ • π(y)`.  Testing with
`η = ϑ(y₀) ζ(π y) • h^# ω`, which agrees with `h^# ω` near `spt Z`, the slices of `η` are
`ζ(x) sᵐ ω(s x)(x, ·)`, so `S(ω) = Z(η) = ∫₀¹ X(η_s) ds = X(ζ ψ_ω) = C(ω)` for the radial integral
`ψ_ω(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt`. -/
theorem Submission.iwl_cr_cone_integer_multiplicity :
    ∀ (P m : ℕ),
      (∀ (Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1)) (f : Eucl (P + 1) → Eucl P),
        IsIntegerMultiplicity Z → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
        (∀ K : Set (Eucl P), IsCompact K → IsCompact (f ⁻¹' K ∩ Z.support)) →
        ∃ S : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), IsIntegerMultiplicity S ∧
          ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1))
            (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)),
            (∃ N : Set (Eucl (P + 1)), IsOpen N ∧ Z.support ⊆ N ∧ ∀ y ∈ N,
              (η : DifferentialForm (Eucl (P + 1)) (m + 1)) y =
                ((ω : DifferentialForm (Eucl P) (m + 1)) (f y)).compContinuousLinearMap
                  (fderiv ℝ f y)) →
            S ω = Z η) →
      ∀ (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m)
        (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
        IsIntegerMultiplicity X → X.support ⊆ closedBall 0 R →
        (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m),
          (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P,
            (ψ : DifferentialForm (Eucl P) m) x v =
              ∫ t in (0 : ℝ)..1,
                t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) →
          C ω = X ψ) →
        IsIntegerMultiplicity C := by
  intro P m hpush R X C hX hXR hcone
  -- `Z = [[(0,1)]] × X` is integer multiplicity, `Z(η) = ∫₀¹ X(η_s) ds` for the slices
  -- `η_s = η(Φ(s, ·))(e₀, ι ·)`, and `spt Z` lies in the compact set `L = Φ([0,1] × B̄_R(0))`.
  obtain ⟨Z, hZ, hZη⟩ := Submission.iwl_cr_interval_product_im P m X hX
  obtain ⟨hLc, hZL⟩ := Submission.iwl_cr_ci_product_support P m R X Z hXR hZη
  -- The cone map `h(y) = y₀ • π(y)` is `C^∞` and proper on the closed set `spt Z ⊆ L`, so `Z`
  -- pushes forward to an integer multiplicity `S = τ(M, θ, ξ)`.
  obtain ⟨hh, hhΦ⟩ := Submission.iwl_cr_ci_cone_map P m
  have hZc : IsClosed Z.support := isClosed_univ.sdiff Z.isOpen_zeroRegion
  obtain ⟨S, ⟨M, θ, ξ, hMθξ, hθ, hSτ⟩, hSZ⟩ := hpush Z _ hZ hh fun K hK =>
    hLc.of_isClosed_subset ((hK.isClosed.preimage hh.continuous).inter hZc)
      (inter_subset_right.trans hZL)
  -- It remains to show `C(ω) = S(ω)` for every `ω`.
  refine ⟨M, θ, ξ, hMθξ, hθ, fun ω => ?_⟩
  rw [← hSτ ω]
  -- Cut-offs `ϑ = 1` on `[-1, 2]` and `ζ = 1` on `B̄_r(0)`, where `R < r`.
  obtain ⟨r, hr0, hRr⟩ : ∃ r : ℝ, 0 < r ∧ R < r :=
    ⟨max R 0 + 1, by linarith [le_max_right R 0], by linarith [le_max_left R 0]⟩
  obtain ⟨ϑ, hϑs, hϑc, hϑ1⟩ : ∃ ϑ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑ ∧
      HasCompactSupport ϑ ∧ ∀ s ∈ Icc (-1 : ℝ) 2, ϑ s = 1 := by
    let b : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 2, by norm_num, by norm_num⟩
    refine ⟨b, b.contDiff, b.hasCompactSupport, fun s hs => b.one_of_mem_closedBall ?_⟩
    show dist s (1 / 2) ≤ 3 / 2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨ζ, hζs, hζc, hζ1⟩ : ∃ ζ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧
      HasCompactSupport ζ ∧ ∀ x ∈ closedBall (0 : Eucl P) r, ζ x = 1 := by
    let b : ContDiffBump (0 : Eucl P) := ⟨r, r + 1, hr0, by linarith⟩
    exact ⟨b, b.contDiff, b.hasCompactSupport, fun x hx => b.one_of_mem_closedBall hx⟩
  -- The test form `η = χ • h^# ω` on `ℝ^{P+1}`, `χ(y) = ϑ(y₀) ζ(π y)`.
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) (m + 1)) :=
    ω.property.1.1
  obtain ⟨hχs, hχc⟩ := Submission.iwl_cr_ci_product_cutoff P ϑ ζ hϑs hϑc hζs hζc
  obtain ⟨η, hη⟩ :=
    Submission.iwl_cr_ci_cutoff_pullback_testForm (P + 1) P (m + 1) _ _ _ hh hχs hχc hωs
  -- `χ = 1` on the open set `N = {y : y₀ ∈ (-1, 2), π y ∈ B_r(0)} ⊇ L ⊇ spt Z`, so `S(ω) = Z(η)`.
  have hSη : S ω = Z η := by
    refine hSZ ω η ⟨(fun y : Eucl (P + 1) => y 0) ⁻¹' Ioo (-1) 2 ∩
      (fun y : Eucl (P + 1) => (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) ⁻¹' ball 0 r,
      (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop)), ?_, ?_⟩
    · intro _ hy
      obtain ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩ := hZL hy
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show -1 < s
        linarith [hs.1]
      · show s < 2
        linarith [hs.2]
      · show x ∈ ball (0 : Eucl P) r
        exact mem_ball.2 ((mem_closedBall.1 hx).trans_lt hRr)
    · intro y hy
      have hy0 : y 0 ∈ Icc (-1 : ℝ) 2 := ⟨hy.1.1.le, hy.1.2.le⟩
      have hyπ : (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ closedBall (0 : Eucl P) r :=
        ball_subset_closedBall hy.2
      rw [hη y, hϑ1 _ hy0, hζ1 _ hyπ, one_mul, one_smul]
  -- The slices `φ(s)` of `η`: `Z(η) = ∫₀¹ X(φ(s)) ds`, and `φ(s)(x)(v) = ζ(x) sᵐ ω(s x)(x, v)` for
  -- `s ∈ [0, 1]`, because `Dh(Φ(s, x))` maps `e₀ ↦ x` and `ι v ↦ s v`.
  obtain ⟨φ, hφc, hφ⟩ := Submission.iwl_cr_ci_slice_testForm P m η
  have hZφ : Z η = ∫ s in (0 : ℝ)..1, X (φ s) := hZη η φ fun s _ x v => hφ s x v
  have hφv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P),
      (φ s : DifferentialForm (Eucl P) m) x v =
        ζ x * (s ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (s • x) (Fin.cons x v)) := by
    intro s hs x v
    have hΦ0 : ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) : Eucl (P + 1)) 0 = s := rfl
    have hπΦ : (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))))) = x := rfl
    rw [hφ, hη, ContinuousAlternatingMap.smul_apply, smul_eq_mul, (hhΦ s x).2, hΦ0, hπΦ,
      hϑ1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩, one_mul]
  -- `ψ = ζ ψ_ω` with `ψ_ω(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt` is a test form, and `C(ω) = X(ψ)` by
  -- the cone property, since `ζ = 1` on the open ball `B_r(0) ⊇ B̄_R(0) ⊇ spt X`.
  obtain ⟨ψω, hψωs, hψω, -⟩ :=
    Submission.iwl_cr_radial_operator P m m (ω : DifferentialForm (Eucl P) (m + 1)) hωs
  obtain ⟨ψ, hψ⟩ : ∃ ψ : TestFormOn (univ : Set (Eucl P)) m,
      ∀ x, (ψ : DifferentialForm (Eucl P) m) x = ζ x • ψω x :=
    ⟨⟨fun x => ζ x • ψω x, ⟨⟨hζs.smul hψωs, hζc.smul_right⟩, subset_univ _⟩⟩, fun _ => rfl⟩
  have hCψ : C ω = X ψ := by
    refine hcone ω ψ ⟨ball 0 r, isOpen_ball,
      fun x hx => mem_ball.2 ((mem_closedBall.1 (hXR hx)).trans_lt hRr), fun x hx v => ?_⟩
    rw [hψ, ContinuousAlternatingMap.smul_apply, smul_eq_mul, hζ1 x (ball_subset_closedBall hx),
      one_mul, hψω]
  -- `∫₀¹ X(φ(s)) ds = X(ψ)`: every `φ(s)`, `s ∈ [0, 1]`, is supported in `tsupport ζ`, and
  -- `ψ(x)(v) = ∫₀¹ φ(s)(x)(v) ds`.
  have hXψ : ∫ s in (0 : ℝ)..1, X (φ s) = X ψ := by
    refine Submission.iwl_cr_ci_integral_exchange P m X (tsupport ζ) φ ψ hX hζc hφc
      (fun s hs => closure_mono fun x hx => ?_) fun x v => ?_
    · rw [Function.mem_support] at hx ⊢
      contrapose! hx
      ext v
      rw [hφv s hs x v, hx, zero_mul, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    · rw [hψ, ContinuousAlternatingMap.smul_apply, smul_eq_mul, hψω,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hs
      exact (hφv s hs x v).symm
  rw [hSη, hZφ, hXψ, hCψ]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
