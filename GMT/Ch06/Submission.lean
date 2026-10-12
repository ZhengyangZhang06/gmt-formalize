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

/-- Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): an integer
multiplicity `Y = τ(M, θ, ξ) ∈ 𝒟₀(U)` is a locally finite integer combination of point masses,
`Y(ω) = ∑_{x ∈ N} c(x) ω(x)` with `c(x) ≠ 0` on `N = M`.  `H⁰` is counting measure, so `H⁰`-null
sets are empty and sets of finite `H⁰` measure are finite.  As `θ ≥ 1` on `M` and `θ` is locally
`H⁰`-integrable, `M ∩ K` is finite for compact `K ⊆ U`; the orientation condition holds at every
point of `M`, where `ξ(x) = ±[[x]]`, so `c(x) = θ(x) ξ(x)(1) = ±θ(x)` is a nonzero integer, and the
integral over `M` reduces to the finite sum over `M ∩ spt ω`. -/
theorem Submission.br_zd_im_dirac_repr :
    ∀ (P : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U 0), IsIntegerMultiplicity Y → ∃ (N : Set (Eucl P)) (c : Eucl P → ℤ), N ⊆ U ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) ∧ (∀ x ∈ N, c x ≠ 0) ∧ ∀ ω : TestFormOn U 0, Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  classical
  rintro P U Y ⟨M, θ, ξ, hT, hθ, hY⟩
  set μ : Measure (Eucl P) := (μHE[0] : Measure (Eucl P)) with hμ
  -- `H⁰ = μH[0]` gives every point mass `1`.
  have hpt : ∀ x : Eucl P, μ {x} = 1 := fun x => by
    rw [hμ, Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  -- `H⁰`-null sets are empty.
  have hnull : ∀ E : Set (Eucl P), μ E = 0 → E = ∅ := by
    intro E hE
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have h1 := measure_mono (μ := μ) (singleton_subset_iff.2 hx)
    rw [hpt, hE] at h1
    exact absurd h1 (by simp)
  -- `H⁰` of a finset is its cardinality.
  have hcard : ∀ F : Finset (Eucl P), μ (F : Set (Eucl P)) = F.card := by
    intro F
    rw [← sum_measure_singleton]
    simp [hpt]
  -- Sets of finite `H⁰` measure are finite.
  have hfin : ∀ E : Set (Eucl P), μ E < ∞ → E.Finite := by
    intro E hE
    by_contra hinf
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hE.ne
    obtain ⟨F, hFE, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have h1 := measure_mono (μ := μ) hFE
    rw [hcard, hFcard] at h1
    exact absurd (h1.trans_lt hn) (lt_irrefl _)
  -- Integrals over finsets are finite sums.
  have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ), IntegrableOn g (F : Set (Eucl P)) μ := by
/-- Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): a finite
integer combination of point masses `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`, `D ⊆ U`, is the integer
multiplicity current `τ(M, θ, ξ)` with `M = {x ∈ D : a(x) ≠ 0}`, `θ = |a|` and `ξ = ±1` the sign
of `a`.  `Y` is continuous since convergence of test forms gives pointwise convergence.  `M` is
finite, so it is `H⁰`-measurable and countably `0`-rectifiable and `H⁰`-integrals over it are
finite sums; at `x ∈ M`, for small `r` the blow-up `η_{x,r}(M)` meets the support of a given
`f ∈ C_c` only in `0`, so the weighted tangent space is `{0}`, spanned by the empty frame. -/
theorem Submission.br_zd_finite_dirac_im :
    ∀ (P : ℕ) (U : Set (Eucl P)) (D : Finset (Eucl P)) (a : Eucl P → ℤ),
      (↑D : Set (Eucl P)) ⊆ U → ∃ Y : GeometricCurrentOn U 0, IsIntegerMultiplicity Y ∧
        ∀ ω : TestFormOn U 0,
          Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  classical
  intro P U D a hDU
  -- `H⁰{x} = 1`, so `H⁰`-integrals over finite sets are finite sums.
  have hpt : ∀ x : Eucl P, (μHE[0] : Measure (Eucl P)) {x} = 1 := fun x => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      IntegrableOn g (F : Set (Eucl P)) (μHE[0] : Measure (Eucl P)) := by
    intro F g
    rw [← biUnion_of_singleton (F : Set (Eucl P)), Finset.set_biUnion_coe,
      integrableOn_finset_iUnion]
    exact fun x _ => integrableOn_singleton (hx := by rw [hpt]; exact ENNReal.one_lt_top)
  have hsum : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      ∫ x in (F : Set (Eucl P)), g x ∂μ = ∑ x ∈ F, g x := by
    intro F g
    rw [setIntegral_finset F (hint F g)]
    simp only [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
  -- `θ ≥ 1` on `M`.
  have hθ1 : ∀ x ∈ M, (1 : ℝ) ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθ x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hpos)
  -- Local finiteness: `H⁰(M ∩ K) ≤ ∫_{M ∩ K} θ dH⁰ < ∞`.
  have hlocfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (M ∩ K).Finite := by
    intro K hK hKU
    apply hfin
    have hMK : NullMeasurableSet (M ∩ K) μ :=
      hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
    have h1 : IntegrableOn (fun _ => (1 : ℝ)) (M ∩ K) μ := by
      refine (hT.integrableOn K hK hKU).mono' aestronglyMeasurable_const ?_
      filter_upwards [ae_restrict_mem₀ hMK] with x hx
      simpa using hθ1 x hx.1
    rcases (integrableOn_const_iff (by simp)).1 h1 with h | h
    · simp at h
    · exact h
  -- Orientation at every point of `M`: its failure set is `H⁰`-null in `M`, hence empty.
  set ε : NVector (Eucl P) 0 := simpleNVector (![] : Fin 0 → Eucl P) with hε
  have horient : ∀ x ∈ M, ξ x = ε ∨ ξ x = -ε := by
    have h := hT.orients
    rw [Filter.Eventually, mem_ae_iff] at h
    have h2 := Measure.le_restrict_apply (μ := μ) (s := M) _ |>.trans_eq h
    rw [nonpos_iff_eq_zero] at h2
    have h3 := hnull _ h2
    intro x hx
    have hx' : x ∉ {x | ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
        (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)}ᶜ := by
      intro hmem
      have : x ∈ ({x | ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
        (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)}ᶜ ∩ M) := ⟨hmem, hx⟩
      rw [h3] at this
      exact this
    rw [Set.notMem_compl_iff] at hx'
    obtain ⟨τ, -, -, hτ⟩ := hx'
    rwa [Subsingleton.elim τ ![]] at hτ
  -- The unit `0`-covector `1`: every `0`-covector is `α = α(![]) • 1`.
  set one0 : Covector (Eucl P) 0 :=
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) 1 with hone0
  have hdecomp : ∀ (α : Covector (Eucl P) 0), α = α ![] • one0 := by
    intro α
    ext v
    rw [Subsingleton.elim v ![]]
    simp [one0]
  have hpair : ∀ (w : NVector (Eucl P) 0) (α : Covector (Eucl P) 0), w α = α ![] * w one0 := by
    intro w α
    conv_lhs => rw [hdecomp α]
    rw [map_smul, smul_eq_mul]
  -- The coefficients `c(x) = ⌊θ(x) ξ(x)(1)⌋`, equal to `±θ(x) ∈ ℤ ∖ {0}` on `M`.
  let c : Eucl P → ℤ := fun x => ⌊θ x * ξ x one0⌋
  have hcM : ∀ x ∈ M, (c x : ℝ) = θ x * ξ x one0 ∧ c x ≠ 0 := by
    intro x hx
    obtain ⟨k, hk⟩ := hθ x hx
    have hk1 : (1 : ℝ) ≤ k := hk ▸ hθ1 x hx
    have hk1' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
    have hεone : ε one0 = 1 := by simp [ε, one0]
    rcases horient x hx with h | h
    · have he : θ x * ξ x one0 = ((k : ℤ) : ℝ) := by rw [h, hεone, hk]; simp
      refine ⟨by simp only [c, he, Int.floor_intCast], ?_⟩
      simp only [c, he, Int.floor_intCast]
      omega
    · have he : θ x * ξ x one0 = (Int.cast (-(k : ℤ)) : ℝ) := by
        rw [h, neg_apply, hεone, hk]; simp
      refine ⟨by simp only [c, he, Int.floor_intCast], ?_⟩
      simp only [c, he, Int.floor_intCast]
      omega
  refine ⟨M, c, hT.subset, hlocfin, fun x hx => (hcM x hx).2, ?_⟩
  -- The integral over `M` is the finite sum over `S = M ∩ spt ω`.
  intro ω
  set f : DifferentialForm (Eucl P) 0 := (ω : DifferentialForm (Eucl P) 0) with hf
  have hKc : IsCompact (tsupport f) := ω.property.1.2
  have hKU : tsupport f ⊆ U := ω.property.2
  have hSfin : (M ∩ tsupport f).Finite := hlocfin _ hKc hKU
  set S : Finset (Eucl P) := hSfin.toFinset with hS
  have hSM : (S : Set (Eucl P)) = M ∩ tsupport f := hSfin.coe_toFinset
  have hzero : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  rw [hY ω, tauAction]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := (S : Set (Eucl P))) hT.nullMeasurableSet
    (by rw [hSM]; exact inter_subset_left) (Eventually.of_forall fun x hx => ?_)]
  · rw [hsum, finsum_mem_eq_sum_of_subset _ (t := S) ?_ (by rw [hSM]; exact inter_subset_left)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hxM : x ∈ M := by
        have : x ∈ (S : Set (Eucl P)) := hx
        rw [hSM] at this
        exact this.1
      rw [hpair, (hcM x hxM).1]
      ring
    · rintro x ⟨hxM, hx0⟩
      rw [hSM]
      refine ⟨hxM, subset_tsupport _ ?_⟩
      intro hfx
      apply hx0
      simp [hfx]
  · have hx' : x ∉ tsupport f := fun h => hx.2 (by rw [hSM]; exact ⟨hx.1, h⟩)
    have h0 : (ω : DifferentialForm (Eucl P) 0) x = 0 := hzero x hx'
    simp [h0]
/-- The mass lower bound for a locally finite Dirac sum (the `0`-dimensional step in the proof of
Simon Ch. 6, 6.3): if `Y(ω) = ∑ᶠ_{x ∈ N} c(x) ω(x)` with `N ∩ K` finite for compact `K ⊆ U`, then
`∑_{x ∈ S} |c(x)| ≤ M_W(Y)` for every finite `S ⊆ N ∩ W`, `W ⊆ U` open.  Test with
`ω = ∑_{x ∈ S} sign(c(x)) φₓ`, where the bumps `φₓ` (`φₓ(x) = 1`) have pairwise disjoint
supports `B(x, δ) ⊆ W` meeting `N` only in `x`: then `|ω| ≤ 1` and `Y(ω) = ∑_{x ∈ S} |c(x)|`. -/
theorem Submission.br_zd_dirac_massOn_ge :
    ∀ (P : ℕ) (U W N : Set (Eucl P)) (Y : GeometricCurrentOn U 0) (c : Eucl P → ℤ), IsOpen W →
      W ⊆ U → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) →
      (∀ ω : TestFormOn U 0,
        Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) →
      ∀ S : Finset (Eucl P), (↑S : Set (Eucl P)) ⊆ N ∩ W →
        ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) ≤ Y.massOn W := by
  classical
  intro P U W N Y c hW hWU hN hY S hS
  -- A common radius `δ > 0`: for `x ∈ S`, `B̄(x, 2δ) ⊆ W` and `N ∩ B̄(x, 2δ) = {x}`.
  have hloc : ∀ x ∈ S, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      closedBall x (2 * δ) ⊆ W ∧ ∀ y ∈ N, dist y x ≤ 2 * δ → y = x := by
    intro x hx
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW x (hS hx).2
    have hfin : (N ∩ closedBall x (r / 2)).Finite :=
      hN _ (isCompact_closedBall x (r / 2))
        (((closedBall_subset_ball (half_lt_self hr)).trans hrW).trans hWU)
    obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.mp
      (hfin.subset (sdiff_subset (t := {x}))).isClosed.isOpen_compl x (by simp)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (r / 4) (ε / 4) by positivity)]
      with δ ⟨hδ0, hδ⟩
    have h1 : δ < r / 4 := hδ.trans_le (min_le_left _ _)
    have h2 : δ < ε / 4 := hδ.trans_le (min_le_right _ _)
    refine ⟨(closedBall_subset_ball (by linarith)).trans hrW, fun y hyN hyx => ?_⟩
    by_contra hne
    exact hεF (mem_ball.2 (by linarith)) ⟨⟨hyN, mem_closedBall.2 (by linarith)⟩, hne⟩
  obtain ⟨δ, hδS, hδ : 0 < δ⟩ :=
    (((Filter.eventually_all_finset S).2 hloc).and self_mem_nhdsWithin).exists
  -- Bumps `φ x` with `φ x = 1` on `B̄(x, δ/2)`, support `B(x, δ)`, and signs `s x` of `c x`.
  let φ : (x : Eucl P) → ContDiffBump x := fun x => ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let s : Eucl P → ℝ := fun x => if 0 ≤ (c x : ℝ) then 1 else -1
  have hφ0 : ∀ x y, δ ≤ dist y x → φ x y = 0 := fun x y h => (φ x).zero_of_le_dist h
  have hφ1 : ∀ x, φ x x = 1 := fun x =>
    (φ x).one_of_mem_closedBall (mem_closedBall_self (half_pos hδ).le)
  -- The balls `B(x, δ)`, `x ∈ S`, are pairwise disjoint.
  have hsep : ∀ x ∈ S, ∀ x' ∈ S, x' ≠ x → ∀ y, dist y x < δ → δ ≤ dist y x' := by
    intro x hx x' hx' hne y hy
    by_contra h
    refine hne ((hδS x hx).2 x' (hS hx').1 ?_)
    have := dist_triangle x' y x
    rw [dist_comm x' y] at this
    linarith
  let h : Eucl P → ℝ := fun y => ∑ x ∈ S, s x * φ x y
  have hh0 : ∀ y, h y ≠ 0 → ∃ x ∈ S, dist y x < δ := by
    intro y hy
    by_contra hcon
    exact hy (Finset.sum_eq_zero fun x hx => by
      rw [hφ0 x y (not_lt.1 fun h' => hcon ⟨x, hx, h'⟩), mul_zero])
  have hhS : ∀ x ∈ S, h x = s x := by
    intro x hx
    rw [show h x = ∑ x' ∈ S, s x' * φ x' x from rfl,
      Finset.sum_eq_single_of_mem x hx fun x' hx' hne =>
        by rw [hφ0 x' x (hsep x hx x' hx' hne x (by simpa using hδ)), mul_zero],
      hφ1, mul_one]
  have hh1 : ∀ y, |h y| ≤ 1 := by
    intro y
    by_cases hy : h y = 0
    · simp [hy]
    obtain ⟨x, hx, hyx⟩ := hh0 y hy
    rw [show h y = ∑ x' ∈ S, s x' * φ x' y from rfl,
      Finset.sum_eq_single_of_mem x hx fun x' hx' hne =>
        by rw [hφ0 x' y (hsep x hx x' hx' hne y hyx), mul_zero], abs_mul]
    have hs : |s x| = 1 := by simp only [s]; split_ifs <;> simp
    rw [hs, one_mul, abs_of_nonneg (φ x).nonneg]
    exact (φ x).le_one
  -- The test form `ω = h • 𝟙`, where `𝟙` is the `0`-covector with value `1`.
  let e : Covector (Eucl P) 0 :=
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) (1 : ℝ)
  let f : DifferentialForm (Eucl P) 0 := fun y => h y • e
  have hfe : ∀ y, f y ![] = h y := fun y => by simp [f, e]
  set B : Set (Eucl P) := ⋃ x ∈ S, closedBall x δ
  have hB : IsCompact B := S.isCompact_biUnion fun x _ => isCompact_closedBall x δ
  have hBW : B ⊆ W := iUnion₂_subset fun x hx =>
    (closedBall_subset_closedBall (by linarith)).trans (hδS x hx).1
  have hfB : ∀ y, y ∉ B → f y = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨x, hx, hyx⟩ := hh0 y fun h0 => hne (by simp [f, h0])
    exact hy (mem_iUnion₂.2 ⟨x, hx, mem_closedBall.2 hyx.le⟩)
  have hfsupp : tsupport f ⊆ B :=
    closure_minimal (fun y hy => by_contra fun hyB => hy (hfB y hyB)) hB.isClosed
  have hfsmooth : IsSmoothForm f :=
    (ContDiff.sum fun x _ => contDiff_const.mul (φ x).contDiff).smul contDiff_const
  have hfcpt : HasCompactSupport f := HasCompactSupport.intro hB hfB
  let ω : TestFormOn U 0 := ⟨f, show IsTestForm f ∧ tsupport f ⊆ U from
    ⟨⟨hfsmooth, hfcpt⟩, hfsupp.trans (hBW.trans hWU)⟩⟩
  have hadm : ω ∈ massAdmissibleOn U 0 W := by
    refine show tsupport f ⊆ W ∧ ∀ y, covectorEuclideanNorm (f y) ≤ 1 from
      ⟨hfsupp.trans hBW, fun y => ?_⟩
    -- For a `0`-covector `α`, the coefficient norm is `|α(![])|`.
    rw [covectorEuclideanNorm, Fintype.sum_unique, ite_eq_left (Subsingleton.strictMono _),
      show (fun i => EuclideanSpace.basisFun (Fin P) ℝ ((default : Fin 0 → Fin P) i)) = ![] from
        Subsingleton.elim _ _, hfe, Real.sqrt_sq_eq_abs]
    exact hh1 y
  -- Only the points of `S` contribute to `Y(ω) = ∑ᶠ_{y ∈ N} c(y) h(y)`, and `h = s` on `S`.
  have hval : Y ω = ∑ x ∈ S, |(c x : ℝ)| := by
    rw [hY]
    change ∑ᶠ y ∈ N, (c y : ℝ) * f y ![] = _
    simp_rw [hfe]
    rw [finsum_mem_eq_sum_of_inter_support_eq (fun y => (c y : ℝ) * h y) (t := S) ?_]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [hhS x hx]
      simp only [s]
      split_ifs with h0
      · rw [mul_one, abs_of_nonneg h0]
      · rw [mul_neg_one, abs_of_neg (not_le.1 h0)]
    · ext y
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      constructor
      · rintro ⟨hyN, hy⟩
        refine ⟨?_, hy⟩
        obtain ⟨x, hx, hyx⟩ := hh0 y (right_ne_zero_of_mul hy)
        rw [(hδS x hx).2 y hyN (by linarith)]
        exact hx
      · rintro ⟨hyS, hy⟩
        exact ⟨(hS hyS).1, hy⟩
  calc ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) = ENNReal.ofReal (Y ω) := by rw [hval]
    _ ≤ Y.massOn W := Y.le_massOn hadm
      ∫ x in (F : Set (Eucl P)), g x ∂(μHE[0] : Measure (Eucl P)) = ∑ x ∈ F, g x := by
    intro F g
    rw [setIntegral_finset F (hint F g)]
    simp only [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
  -- The current `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`: if `ω_j → 0`, then `ω_j(x) → 0` for every `x`
  -- (uniformly on the common compact support `K`, and `ω_j(x) = 0` off `K`).
  let L : TestFormOn U 0 →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]
      map_add' := fun ω η => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun t ω => by simp [Finset.mul_sum, mul_left_comm] }
  have hcont : ∀ ωs : ℕ → TestFormOn U 0, TestFormOnConverges ωs 0 →
      Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    rintro ωs ⟨K, -, -, hsupp, -, hconv⟩
    have hx : ∀ x, Tendsto (fun j => (ωs j : DifferentialForm (Eucl P) 0) x ![]) atTop (𝓝 0) := by
      intro x
      by_cases hxK : x ∈ K
      · have hev : Continuous fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Eucl P)
            (Covector (Eucl P) 0) => T ![] ![] := by fun_prop
        simpa [Function.comp_def] using (hev.tendsto _).comp ((hconv 0).tendsto_at hxK)
      · have h0 : ∀ j, (ωs j : DifferentialForm (Eucl P) 0) x = 0 := fun j =>
          image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp j h)
        simp [h0]
    simpa [L] using tendsto_finsetSum D fun x _ => (hx x).const_mul (a x : ℝ)
  obtain ⟨Y, hY⟩ : ∃ Y : GeometricCurrentOn U 0, ∀ ω : TestFormOn U 0,
      Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] :=
    ⟨⟨L, hcont⟩, fun ω => rfl⟩
  refine ⟨Y, ?_, hY⟩
  -- The triple: `M = {a ≠ 0}`, `θ = |a|`, `ξ = -ε` on `N = {a < 0}` and `ξ = ε` elsewhere, where
  -- `⟨α, ε⟩ = α(![])`; then `θ(x) ⟨α, ξ(x)⟩ = a(x) α(![])` on `M`.
  set M : Finset (Eucl P) := D.filter (fun x => a x ≠ 0) with hM
  set N : Finset (Eucl P) := D.filter (fun x => a x < 0) with hN
  let ε : NVector (Eucl P) 0 := simpleNVector ![]
  let θ : Eucl P → ℝ := fun x => |(a x : ℝ)|
  let ξ : Eucl P → NVector (Eucl P) 0 := fun x => if x ∈ N then -ε else ε
  have hMmeas : MeasurableSet (M : Set (Eucl P)) := M.finite_toSet.measurableSet
  have hterm : ∀ x ∈ M, ∀ α : Covector (Eucl P) 0, θ x * ξ x α = (a x : ℝ) * α ![] := by
    intro x hx α
    have hxD : x ∈ D := (Finset.mem_filter.1 hx).1
    by_cases hneg : a x < 0
    · have hxN : x ∈ N := Finset.mem_filter.2 ⟨hxD, hneg⟩
      have ha : (a x : ℝ) < 0 := by exact_mod_cast hneg
      simp only [θ, ξ, ε, hxN, ↓reduceIte, neg_apply, simpleNVector_apply,
        abs_of_neg ha]
      ring
    · have hxN : x ∉ N := fun h => hneg (Finset.mem_filter.1 h).2
      have ha : (0 : ℝ) ≤ a x := by exact_mod_cast not_lt.1 hneg
      simp only [θ, ξ, ε, hxN, ↓reduceIte, simpleNVector_apply, abs_of_nonneg ha]
  refine ⟨M, θ, ξ,
    { subset := fun x hx => hDU (Finset.mem_filter.1 hx).1
      nullMeasurableSet := hMmeas.nullMeasurableSet
      countablyRectifiable := ?_
      pos := fun x hx => abs_pos.2 (Int.cast_ne_zero.2 (Finset.mem_filter.1 hx).2)
      integrableOn := fun K _ _ => (hint M θ).mono_set inter_subset_left
      aestronglyMeasurable := ?_
      orients := ?_ }, fun x _ => ⟨(a x).natAbs, by simp [θ, Nat.cast_natAbs, Int.cast_abs]⟩, ?_⟩
  · -- `M` is countable, hence covered by the ranges of countably many constant maps.
    obtain ⟨g, hg⟩ := countable_iff_exists_subset_range.1 M.finite_toSet.countable
    refine ⟨∅, measure_empty, fun j _ => g j, fun j => ⟨0, LipschitzWith.const _⟩, fun y hy => ?_⟩
    obtain ⟨j, rfl⟩ := hg hy
    exact Or.inr (mem_iUnion.2 ⟨j, 0, rfl⟩)
  · -- `ξ` is constant off and on the finite set `N`.
    exact (StronglyMeasurable.ite N.finite_toSet.measurableSet stronglyMeasurable_const
      stronglyMeasurable_const).aestronglyMeasurable
  · -- Every `x ∈ M` is oriented by the empty frame, spanning the weighted tangent space `{0}`.
    refine ae_restrict_of_forall_mem hMmeas fun x hx =>
      ⟨![], ⟨fun i => i.elim0, fun i => i.elim0⟩, ?_, ?_⟩
    · rw [range_eq_empty, Submodule.span_empty]
      refine ⟨finrank_bot ℝ (Eucl P), fun f => ?_⟩
      have hbot : ∫ y in ((⊥ : Submodule ℝ (Eucl P)) : Set (Eucl P)), f y
          ∂(μHE[0] : Measure (Eucl P)) = f 0 := by
        simp
      rw [hbot]
      -- `f = 0` off `B_R(0)`, and the points of `M \ {x}` have distance `≥ d` from `x`; so for
      -- `0 < r < d / R` only `y = x` contributes to `∑_{y ∈ M} f(η_{x,r}(y)) θ(y)`.
      obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
      obtain ⟨d, hd, hdM⟩ := Metric.isOpen_iff.mp
        (M.erase x).finite_toSet.isClosed.isOpen_compl x (by simp)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (div_pos hd hR)] with r ⟨hr0, hrd⟩
      have hinj : Function.Injective (blowUpMap x r) := fun y z h => by
        simpa [blowUpMap, hr0.ne'] using h
      have hback : ∀ y, x + r • blowUpMap x r y = y := fun y => by
        simp [blowUpMap, smul_smul, hr0.ne']
      rw [← Finset.coe_image, hsum, Finset.sum_image fun y _ z _ h => hinj h]
      simp only [hback]
      rw [Finset.sum_eq_single x (fun y hy hyx => ?_) (fun h => absurd hx h)]
      · simp [blowUpMap, mul_comm]
      · have hyd : d ≤ ‖y - x‖ := by
          rw [← dist_eq_norm]
          by_contra h
          exact hdM (mem_ball.2 (not_le.1 h)) (Finset.mem_erase.2 ⟨hyx, hy⟩)
        rw [lt_div_iff₀ hR] at hrd
        rw [hfR, zero_mul]
        rw [blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0, le_inv_mul_iff₀ hr0]
        linarith
    · by_cases hxN : x ∈ N
      · exact Or.inr (by simp [ξ, ε, hxN])
      · exact Or.inl (by simp [ξ, ε, hxN])
  · -- `τ(M, θ, ξ)(ω) = ∑_{x ∈ M} a(x) ω(x) = ∑_{x ∈ D} a(x) ω(x)`, as `a = 0` on `D \ M`.
    intro ω
    rw [hY, tauAction, hsum, Finset.sum_congr rfl fun x hx => hterm x hx _, hM,
      Finset.sum_filter_of_ne]
    intro x _ hne ha
    exact hne (by simp [ha])
/-- The case `n = 0` of Simon Ch. 6, 8.2 (p. 176, "trivial in case `n = 0`"), on a set `W` with
`closure W` compact (used for 6.3): let `X_j ⇀ X` and, on test forms supported in `W`, let
`X_j(ω) = ∑ᶠ_{x ∈ N_j} c_j(x) ω(x)` with integers `c_j ≠ 0` on `N_j`, `N_j ∩ W` finite and
`∑_{x ∈ N_j ∩ W} |c_j(x)| ≤ Λ`.  Then on such forms `X(ω) = ∑_{x ∈ D} a(x) ω(x)` for a finite
`D ⊆ W` and integers `a`.  Each `N_j ∩ W` has at most `Q = ⌊Λ⌋₊` points, with `|c_j| ≤ ⌊Λ⌋`;
padding with `0`-weighted copies of `0` gives configurations of length `Q` in a compact set, a
subsequence converges, limit points outside `W` contribute `0` and equal ones are grouped. -/
theorem Submission.br_zd_dirac_local_limit : ∀ (P : ℕ) (U W : Set (Eucl P)) (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0) (N : ℕ → Set (Eucl P)) (c : ℕ → Eucl P → ℤ) (Λ : ℝ), IsCompact (closure W) → WeaklyConvergesOn Xj X → (∀ j, ∀ x ∈ N j, c j x ≠ 0) → (∀ j, (N j ∩ W).Finite) → (∀ j (S : Finset (Eucl P)), (↑S : Set (Eucl P)) ⊆ N j ∩ W → ∑ x ∈ S, |(c j x : ℝ)| ≤ Λ) → (∀ j (ω : TestFormOn U 0), tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W → Xj j ω = ∑ᶠ x ∈ N j, (c j x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) → ∃ (D : Finset (Eucl P)) (a : Eucl P → ℤ), (↑D : Set (Eucl P)) ⊆ W ∧ ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W → X ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  intro P U W Xj X N c Λ hW hconv hc hfin hbound hrepr
  classical
  -- `ω°(x) = ω(x)(![])` is continuous and vanishes off `tsupport ω`.
  have hcont : ∀ ω : TestFormOn U 0,
      Continuous fun x => (ω : DifferentialForm (Eucl P) 0) x ![] := fun ω =>
    ω.property.1.1.continuous.eval_const _
  have hvan : ∀ (ω : TestFormOn U 0) (x : Eucl P),
      x ∉ tsupport (ω : DifferentialForm (Eucl P) 0) →
        (ω : DifferentialForm (Eucl P) 0) x ![] = 0 := fun ω x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  -- Step 1: on forms supported in `W`, `X_j(ω) = ∑_{x ∈ A_j} c_j(x) ω°(x)`, `A_j = N_j ∩ W`.
  let A : ℕ → Finset (Eucl P) := fun j => (hfin j).toFinset
  have hA : ∀ j x, x ∈ A j ↔ x ∈ N j ∧ x ∈ W := fun j x => by simp [A]
  have hXj : ∀ j (ω : TestFormOn U 0), tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W →
      Xj j ω = ∑ x ∈ A j, (c j x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
    intro j ω hω
    rw [hrepr j ω hω]
    refine finsum_mem_eq_sum_of_subset _ ?_ fun x hx => ((hA j x).1 hx).1
    rintro x ⟨hxN, hx0⟩
    refine (hA j x).2 ⟨hxN, by_contra fun hxW => hx0 ?_⟩
    simp [hvan ω x fun h => hxW (hω h)]
  -- Step 2: `#A_j ≤ Q = ⌊Λ⌋₊` (as `|c_j| ≥ 1` on `N_j`) and `|c_j| ≤ m = ⌊Λ⌋` on `A_j`.
  have hΛ : 0 ≤ Λ := by simpa using hbound 0 ∅ (by simp)
  obtain ⟨Q, hcard⟩ : ∃ Q : ℕ, ∀ j, (A j).card ≤ Q := by
    refine ⟨⌊Λ⌋₊, fun j => Nat.le_floor ?_⟩
    calc ((A j).card : ℝ) = ∑ x ∈ A j, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ A j, |(c j x : ℝ)| := Finset.sum_le_sum fun x hx => by
          exact_mod_cast Int.one_le_abs (hc j x ((hA j x).1 hx).1)
      _ ≤ Λ := hbound j (A j) fun x hx => (hA j x).1 hx
  obtain ⟨m, hm, hcoef⟩ : ∃ m : ℤ, 0 ≤ m ∧ ∀ j, ∀ x ∈ A j, |c j x| ≤ m := by
    refine ⟨⌊Λ⌋, Int.floor_nonneg.2 hΛ, fun j x hx => Int.le_floor.2 ?_⟩
    simpa using hbound j {x} (by simpa using (hA j x).1 hx)
  -- Step 3: pad each configuration to length `Q` by points `0` with coefficient `0`.
  have pad : ∀ (n : ℕ) (B : Finset (Eucl P)), B.card ≤ n → ∀ d : Eucl P → ℤ,
      ∃ (p : Fin n → Eucl P) (b : Fin n → ℤ), (∀ ℓ, p ℓ ∈ B ∨ p ℓ = 0) ∧
        (∀ ℓ, b ℓ = 0 ∨ ∃ x ∈ B, b ℓ = d x) ∧
        ∀ g : Eucl P → ℝ, ∑ x ∈ B, (d x : ℝ) * g x = ∑ ℓ, (b ℓ : ℝ) * g (p ℓ) := by
    intro n
    induction n with
    | zero =>
      intro B hB d
      obtain rfl : B = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hB)
      exact ⟨Fin.elim0, Fin.elim0, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0, fun g => by simp⟩
    | succ n ih =>
      intro B hB d
      rcases B.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact ⟨fun _ => 0, fun _ => 0, fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun g => by simp⟩
      obtain ⟨p, b, hp, hb, hpb⟩ :=
        ih (B.erase x) (by rw [Finset.card_erase_of_mem hx]; omega) d
      refine ⟨Fin.cons x p, Fin.cons (d x) b, fun ℓ => ?_, fun ℓ => ?_, fun g => ?_⟩
      · refine Fin.cases (by simp [hx]) (fun i => ?_) ℓ
        simpa using (hp i).imp_left Finset.mem_of_mem_erase
      · refine Fin.cases (Or.inr ⟨x, hx, by simp⟩) (fun i => ?_) ℓ
        simpa using (hb i).imp_right fun ⟨z, hz, h⟩ => ⟨z, Finset.mem_of_mem_erase hz, h⟩
      · rw [← Finset.add_sum_erase B _ hx, hpb g, Fin.sum_univ_succ]
        simp
  choose p b hp hb hpb using fun j => pad Q (A j) (hcard j) (c j)
  -- Step 4: `(p_j, b_j) ∈ (closure W ∪ {0})^Q × [-m, m]^Q`, which is compact; extract a
  -- subsequence `ψ` with `(p_{ψ i}, b_{ψ i}) → (y, β)`.
  have hK : IsCompact ((Set.univ.pi fun _ : Fin Q => closure W ∪ {0}) ×ˢ
      (Set.univ.pi fun _ : Fin Q => Set.Icc (-m) m)) :=
    (isCompact_univ_pi fun _ => hW.union isCompact_singleton).prod
      (isCompact_univ_pi fun _ => (Set.finite_Icc _ _).isCompact)
  have hmem : ∀ j, (p j, b j) ∈ (Set.univ.pi fun _ : Fin Q => closure W ∪ {0}) ×ˢ
      (Set.univ.pi fun _ : Fin Q => Set.Icc (-m) m) := by
    refine fun j => ⟨fun ℓ _ => ?_, fun ℓ _ => ?_⟩
    · exact (hp j ℓ).imp (fun h => subset_closure ((hA j _).1 h).2) id
    · show b j ℓ ∈ Set.Icc (-m) m
      rcases hb j ℓ with h | ⟨x, hx, h⟩
      · rw [h]
        exact ⟨neg_nonpos.2 hm, hm⟩
      · rw [h]
        exact abs_le.1 (hcoef j x hx)
  obtain ⟨⟨y, β⟩, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq hmem
  -- Step 5: `X(ω) = ∑_ℓ β_ℓ ω°(y_ℓ)` by continuity of `(p, b) ↦ ∑_ℓ b_ℓ ω°(p_ℓ)`.
  have hX : ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W →
      X ω = ∑ ℓ, (β ℓ : ℝ) * (ω : DifferentialForm (Eucl P) 0) (y ℓ) ![] := by
    intro ω hω
    have hΦ : Continuous fun q : (Fin Q → Eucl P) × (Fin Q → ℤ) =>
        ∑ ℓ, (q.2 ℓ : ℝ) * (ω : DifferentialForm (Eucl P) 0) (q.1 ℓ) ![] :=
      continuous_finsetSum _ fun ℓ _ =>
        ((continuous_of_discreteTopology (f := fun z : ℤ => (z : ℝ))).comp
          ((continuous_apply ℓ).comp continuous_snd)).mul
          ((hcont ω).comp ((continuous_apply ℓ).comp continuous_fst))
    refine tendsto_nhds_unique ((hconv ω).comp hψ.tendsto_atTop) ?_
    refine ((hΦ.tendsto (y, β)).comp hlim).congr fun i => ?_
    simp only [Function.comp_apply]
    rw [hXj (ψ i) ω hω, hpb (ψ i)]
  -- Steps 6–7: limit points outside `W` contribute `0`; group the others by position.
  let s : Finset (Fin Q) := Finset.univ.filter fun ℓ => y ℓ ∈ W
  refine ⟨s.image y, fun z => ∑ ℓ ∈ s.filter fun ℓ => y ℓ = z, β ℓ, ?_, fun ω hω => ?_⟩
  · intro z hz
    rw [Finset.coe_image] at hz
    obtain ⟨ℓ, hℓ, rfl⟩ := hz
    simpa [s] using hℓ
  · rw [hX ω hω, ← Finset.sum_subset (Finset.subset_univ s) fun ℓ _ hℓ => ?_,
      ← Finset.sum_fiberwise_of_maps_to fun ℓ hℓ => Finset.mem_image_of_mem y hℓ]
    · refine Finset.sum_congr rfl fun z _ => ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ℓ hℓ => by rw [(Finset.mem_filter.1 hℓ).2]
    · have hyW : y ℓ ∉ W := by simpa [s] using hℓ
      rw [hvan ω (y ℓ) fun h => hyW (hω h), mul_zero]
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
/-- Finitely many covectors separate `k`-vectors (Simon Ch. 6, §1): `Λᵏ(ℝ^P)` is
finite-dimensional, and `k`-vectors (continuous linear functionals on it) agreeing on a basis
agree.  Evaluation on tuples of standard basis vectors embeds `Λᵏ(ℝ^P)` linearly into
`ℝ^(Fin k → Fin P)` (a multilinear map is determined by its values on basis vectors). -/
theorem Submission.ltg_covector_separating :
    ∀ (P k : ℕ), ∃ (L : ℕ) (b : Fin L → Covector (Eucl P) k),
      ∀ w w' : NVector (Eucl P) k, (∀ l, w (b l) = w' (b l)) → w = w' := by
  intro P k
  -- Evaluation on `k`-tuples of standard basis vectors of `ℝ^P`.
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  let ev : Covector (Eucl P) k →ₗ[ℝ] (Fin k → Fin P) → ℝ :=
    { toFun := fun α I => α fun j => e (I j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- `ev` is injective, so `Λᵏ(ℝ^P)` is finite-dimensional.
  have hinj : Function.Injective ev := fun α β h =>
    ContinuousAlternatingMap.toAlternatingMap_injective <|
      Module.Basis.ext_alternating e fun v _ => congrFun h v
  have : FiniteDimensional ℝ (Covector (Eucl P) k) := FiniteDimensional.of_injective ev hinj
  -- Linear functionals agreeing on a basis are equal.
  let b := Module.finBasis ℝ (Covector (Eucl P) k)
  exact ⟨Module.finrank ℝ (Covector (Eucl P) k), b, fun w w' h =>
    ContinuousLinearMap.coe_injective (b.ext h)⟩
/-- Nonnegative multiples of unit simple `k`-vectors are rigid (the orientations
`ξ = ±τ₁ ∧ ⋯ ∧ τₖ` of Simon Ch. 6, 3.1): if `τ, τ'` are orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₖ`,
`w' = ±τ'₁ ∧ ⋯ ∧ τ'ₖ`, `a, a' ≥ 0` and `a w = a' w'`, then `a = a'`, and `w = w'` when `a ≠ 0`.
Evaluate on the dual covectors `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩`, `α_σ(v) = det(⟨σᵢ, vⱼ⟩)` (1.1):
with `d = det(⟨τᵢ, τ'ⱼ⟩)`, `α_τ(τ) = α_τ'(τ') = 1` and `α_τ(τ') = α_τ'(τ) = d` give
`a = a' |d|` and `a |d| = a'`. -/
theorem Submission.ltg_simple_unit_rigidity :
    ∀ (P k : ℕ) (τ τ' : Fin k → Eucl P) (w w' : NVector (Eucl P) k) (a a' : ℝ),
      Orthonormal ℝ τ → Orthonormal ℝ τ' → (w = simpleNVector τ ∨ w = -simpleNVector τ) →
      (w' = simpleNVector τ' ∨ w' = -simpleNVector τ') → 0 ≤ a → 0 ≤ a' → a • w = a' • w' →
      a = a' ∧ (a ≠ 0 → w = w') := by
  intro P k τ τ' w w' a a' hτ hτ' hw hw' ha ha' h
  -- The dual covector `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩` evaluates as `det(⟨σᵢ, vⱼ⟩)`.
  let α : (Fin k → Eucl P) → Covector (Eucl P) k :=
    fun σ => wedgeCovectors k fun i => innerSL ℝ (σ i)
  have hα : ∀ σ v : Fin k → Eucl P,
      α σ v = (Matrix.of fun i j => inner ℝ (σ i) (v j)).det := fun σ v => by
    simp only [α, wedgeCovectors_apply_det, innerSL_apply_apply]
  -- `α_σ(σ) = det 1 = 1` for orthonormal `σ`, and `α_τ'(τ) = α_τ(τ')` by transposition.
  have hone : ∀ σ : Fin k → Eucl P, Orthonormal ℝ σ → α σ σ = 1 := fun σ hσ => by
    have h1 : (Matrix.of fun i j => inner ℝ (σ i) (σ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [orthonormal_iff_ite.mp hσ, Matrix.one_apply]
    rw [hα, h1, Matrix.det_one]
  have hswap : α τ' τ = α τ τ' := by
    rw [hα, hα, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact real_inner_comm _ _
  -- Signs: `w = s • simpleNVector τ` and `w' = s' • simpleNVector τ'` with `|s| = |s'| = 1`.
  have hsign : ∀ (σ : Fin k → Eucl P) (v : NVector (Eucl P) k),
      (v = simpleNVector σ ∨ v = -simpleNVector σ) →
        ∃ s : ℝ, |s| = 1 ∧ v = s • simpleNVector σ := by
    rintro σ v (rfl | rfl)
    · exact ⟨1, abs_one, (one_smul ℝ _).symm⟩
    · refine ⟨-1, by simp, ?_⟩
      ext β
      simp
  obtain ⟨s, hs, rfl⟩ := hsign τ w hw
  obtain ⟨s', hs', rfl⟩ := hsign τ' w' hw'
  -- Evaluate `a • w = a' • w'` at `α_τ` and `α_τ'` and take absolute values:
  -- `a = a' |d|` and `a |d| = a'`, where `d = α_τ(τ')`.
  have e1 := congrArg (fun v : NVector (Eucl P) k => |v (α τ)|) h
  have e2 := congrArg (fun v : NVector (Eucl P) k => |v (α τ')|) h
  simp only [smul_apply, simpleNVector_apply, smul_eq_mul, hone τ hτ, hone τ' hτ', hswap,
    abs_mul, abs_of_nonneg ha, abs_of_nonneg ha', hs, hs', mul_one, one_mul] at e1 e2
  -- `a = a'`: trivial if `a = 0`; otherwise `a |d|² = a` forces `|d| = 1`.
  have haa : a = a' := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [← e2, ha0, zero_mul]
    · have hd : |α τ τ'| * |α τ τ'| = 1 :=
        mul_left_cancel₀ ha0 (by rw [← mul_assoc, e2, ← e1, mul_one])
      have hd' : |α τ τ'| = 1 := by nlinarith [abs_nonneg (α τ τ')]
      rw [← e2, hd', mul_one]
  -- `w = w'`: cancel the nonzero scalar `a` in `a • w = a • w'`.
  refine ⟨haa, fun ha0 => ?_⟩
  rw [← haa] at h
  exact smul_right_injective _ ha0 h

/-- Uniqueness of `τ(M, θ, ξ)` on an open set (Simon Ch. 6, 3.1): if two rectifiable triples
define the same current on test forms supported in an open `O ⊆ U`, then
`Hᵏ((M₁ Δ M₂) ∩ O) = 0`, and `θ₁ = θ₂`, `ξ₁ = ξ₂` `Hᵏ`-a.e. on `M₁ ∩ O`.  For a covector `b`,
testing with `φ b` and the fundamental lemma give `1_{M₁} θ₁ ξ₁(b) = 1_{M₂} θ₂ ξ₂(b)` a.e. on
`O`; finitely many separating covectors upgrade this to `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂`, and
rigidity of nonnegative multiples of unit simple `k`-vectors concludes. -/
theorem Submission.ltg_tau_unique_on_open :
    ∀ (P k : ℕ) (U O : Set (Eucl P)), IsOpen O → O ⊆ U →
      ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M₁ θ₁ ξ₁ → IsRectifiableTriple U k M₂ θ₂ ξ₂ →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M₁ θ₁ ξ₁ ω = tauAction k M₂ θ₂ ξ₂ ω) →
      (μHE[k] : Measure (Eucl P)) (symmDiff M₁ M₂ ∩ O) = 0 ∧
        ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ O)), θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x := by
  intro P k U O hO hOU M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ hT₁ hT₂ hτ
  -- The scalar density `g^b = 1_M θ ξ(b)` of a triple is locally integrable on `O`, and
  -- `∫ φ g^b dHᵏ = τ(M, θ, ξ)(φ b)` for smooth `φ` with compact support in `O`.
  have key : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ → ∀ b : Covector (Eucl P) k,
      LocallyIntegrableOn (M.indicator fun y => θ y * ξ y b) O (μHE[k] : Measure (Eucl P)) ∧
      ∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ O →
        Integrable (fun x => φ x • M.indicator (fun y => θ y * ξ y b) x)
          (μHE[k] : Measure (Eucl P)) ∧
        ∫ x, φ x • M.indicator (fun y => θ y * ξ y b) x ∂(μHE[k] : Measure (Eucl P)) =
          tauAction k M θ ξ (fun x => φ x • b) := by
    intro M θ ξ hT b
    have hI := Submission.ltg_tau_integrable P k U M θ ξ hT
    refine ⟨?_, fun φ hφ hφc hφO => ?_⟩
    · rw [locallyIntegrableOn_iff hO.isLocallyClosed]
      intro K hKO hK
      exact (integrableOn_indicator_iff hT.nullMeasurableSet).2 (hI.1 K b hK (hKO.trans hOU))
    · have hint := hI.2 (fun x => φ x • b) (hφ.continuous.smul continuous_const)
        hφc.smul_right ((tsupport_smul_subset_left φ fun _ => b).trans (hφO.trans hOU))
      have heq : (fun x => φ x • M.indicator (fun y => θ y * ξ y b) x) =
          M.indicator fun x => θ x * ξ x (φ x • b) := by
        funext x
        by_cases hx : x ∈ M
        · simp only [Set.indicator_of_mem hx, map_smul, smul_eq_mul]
          ring
        · simp [Set.indicator_of_notMem hx]
      rw [heq]
      exact ⟨(integrable_indicator_iff₀ hT.nullMeasurableSet).2 hint,
        integral_indicator₀ hT.nullMeasurableSet⟩
  -- Fundamental lemma: for each covector `b`, `g₁^b = g₂^b` a.e. on `O`.
  have hG : ∀ b : Covector (Eucl P) k, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      M₁.indicator (fun y => θ₁ y * ξ₁ y b) x - M₂.indicator (fun y => θ₂ y * ξ₂ y b) x = 0 := by
    intro b
    obtain ⟨hl₁, hi₁⟩ := key M₁ θ₁ ξ₁ hT₁ b
    obtain ⟨hl₂, hi₂⟩ := key M₂ θ₂ ξ₂ hT₂ b
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hl₁.sub hl₂) fun φ hφ hφc hφO => ?_
    obtain ⟨hint₁, he₁⟩ := hi₁ φ hφ hφc hφO
    obtain ⟨hint₂, he₂⟩ := hi₂ φ hφ hφc hφO
    -- The test form `φ b ∈ 𝒟ᵏ(U)`, supported in `O`.
    have hsmooth : IsSmoothForm (fun x => φ x • b : DifferentialForm (Eucl P) k) := by
      unfold IsSmoothForm
      exact hφ.smul contDiff_const
    have hts : tsupport (fun x => φ x • b : DifferentialForm (Eucl P) k) ⊆ O :=
      (tsupport_smul_subset_left φ fun _ => b).trans hφO
    let ω : TestFormOn U k := ⟨fun x => φ x • b, ⟨hsmooth, hφc.smul_right⟩, hts.trans hOU⟩
    simp_rw [smul_sub]
    rw [integral_sub hint₁ hint₂, he₁, he₂]
    exact sub_eq_zero.2 (hτ ω hts)
  -- Finitely many covectors separate `k`-vectors: `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` a.e. on `O`.
  obtain ⟨L, bs, hsep⟩ := Submission.ltg_covector_separating P k
  have hind : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k)
      (x : Eucl P) (b : Covector (Eucl P) k),
      (M.indicator θ x • ξ x) b = M.indicator (fun y => θ y * ξ y b) x := by
    intro M θ ξ x b
    by_cases hx : x ∈ M <;> simp [hx]
  have hW : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      M₁.indicator θ₁ x • ξ₁ x = M₂.indicator θ₂ x • ξ₂ x := by
    have hall : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), ∀ l, x ∈ O →
        M₁.indicator (fun y => θ₁ y * ξ₁ y (bs l)) x -
          M₂.indicator (fun y => θ₂ y * ξ₂ y (bs l)) x = 0 :=
      ae_all_iff.2 fun l => hG (bs l)
    filter_upwards [hall] with x hx hxO
    refine hsep _ _ fun l => ?_
    rw [hind, hind]
    exact sub_eq_zero.1 (hx l hxO)
  -- `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` for an orthonormal frame `τ`, a.e. on `M`.
  have hor : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ M →
        ∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
          (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
    intro M θ ξ hT
    filter_upwards [(ae_restrict_iff'₀ hT.nullMeasurableSet).1 hT.orients] with x hx hxM
    obtain ⟨τ, hτo, -, hξ⟩ := hx hxM
    exact ⟨τ, hτo, hξ⟩
  -- Pointwise rigidity, using `θᵢ > 0` on `Mᵢ`: a.e. on `O`, `x ∈ M₁ ↔ x ∈ M₂`, and on `M₁`
  -- `θ₁ = θ₂`, `ξ₁ = ξ₂`.
  have hpt : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      (x ∈ M₁ ↔ x ∈ M₂) ∧ (x ∈ M₁ → θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x) := by
    filter_upwards [hW, hor M₁ θ₁ ξ₁ hT₁, hor M₂ θ₂ ξ₂ hT₂] with x hWx h1x h2x hxO
    have hW' := hWx hxO
    by_cases h1 : x ∈ M₁ <;> by_cases h2 : x ∈ M₂
    · obtain ⟨τ, hτo, hξτ⟩ := h1x h1
      obtain ⟨τ', hτo', hξτ'⟩ := h2x h2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2] at hW'
      obtain ⟨hθ, hξ⟩ := Submission.ltg_simple_unit_rigidity P k τ τ' (ξ₁ x) (ξ₂ x) (θ₁ x)
        (θ₂ x) hτo hτo' hξτ hξτ' (hT₁.pos x h1).le (hT₂.pos x h2).le hW'
      exact ⟨iff_of_true h1 h2, fun _ => ⟨hθ, hξ (hT₁.pos x h1).ne'⟩⟩
    · -- On `M₁ \ M₂`, `θ₁ ξ₁ = 0 = 0 ξ₁` would force `θ₁ = 0`.
      obtain ⟨τ, hτo, hξτ⟩ := h1x h1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, zero_smul] at hW'
      exact absurd (Submission.ltg_simple_unit_rigidity P k τ τ (ξ₁ x) (ξ₁ x) (θ₁ x) 0 hτo hτo
        hξτ hξτ (hT₁.pos x h1).le le_rfl (by rw [hW', zero_smul])).1 (hT₁.pos x h1).ne'
    · obtain ⟨τ, hτo, hξτ⟩ := h2x h2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_smul] at hW'
      exact absurd (Submission.ltg_simple_unit_rigidity P k τ τ (ξ₂ x) (ξ₂ x) (θ₂ x) 0 hτo hτo
        hξτ hξτ (hT₂.pos x h2).le le_rfl (by rw [← hW', zero_smul])).1 (hT₂.pos x h2).ne'
    · exact ⟨iff_of_false h1 h2, fun h => absurd h h1⟩
  refine ⟨?_, ?_⟩
  · -- `(M₁ Δ M₂) ∩ O` lies in the exceptional null set.
    rw [ae_iff] at hpt
    refine measure_mono_null ?_ hpt
    rintro x ⟨hxs, hxO⟩ hcon
    rcases Set.mem_symmDiff.1 hxs with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact h2 ((hcon hxO).1.1 h1)
    · exact h1 ((hcon hxO).1.2 h2)
  · rw [ae_restrict_iff'₀ (hT₁.nullMeasurableSet.inter hO.measurableSet.nullMeasurableSet)]
    filter_upwards [hpt] with x hx hxMO
    exact (hx hxMO.2).2 hxMO.1
/-- Gluing compatible integer multiplicity triples along a countable open cover (Simon Ch. 6,
6.3): if `U ⊆ ⋃ᵢ Vᵢ` with `Vᵢ` open, `(Mᵢ, θᵢ, ξᵢ)` are triples in `U` with `θᵢ ∈ ℕ` on `Mᵢ`, and any
two agree `Hᵏ`-a.e. on `Vᵢ ∩ Vⱼ`, then one triple `(M₀, θ₀, ξ₀)` with `θ₀ ∈ ℕ` on `M₀` agrees with
each `(Mᵢ, θᵢ, ξᵢ)` `Hᵏ`-a.e. on `Vᵢ`.  The hypothesis (TL) is locality of weighted approximate
tangent spaces.  `M₀ = ⋃ᵢ Mᵢ ∩ Dᵢ` with `Dᵢ = Vᵢ \ ⋃_{j<i} Vⱼ`, and on `Dᵢ` the triple is
`(Mᵢ, θᵢ, ξᵢ)`. -/
theorem Submission.ltg_glue_triples :
    ∀ (P k : ℕ) (U : Set (Eucl P)), (∀ (A A' : Set (Eucl P)) (ϑ ϑ' : Eucl P → ℝ) (x : Eucl P) (W : Set (Eucl P)), IsOpen W → x ∈ W → (μHE[k] : Measure (Eucl P)) (symmDiff A A' ∩ W) = 0 → (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (A ∩ W)), ϑ y = ϑ' y) → ϑ x = ϑ' x → ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k A ϑ x L → HasWeightedApproximateTangentSpaceAt k A' ϑ' x L) → ∀ (V M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) k), (∀ i, IsOpen (V i)) → U ⊆ ⋃ i, V i → (∀ i, IsRectifiableTriple U k (M i) (θ i) (ξ i)) → (∀ i, ∀ x ∈ M i, ∃ n : ℕ, θ i x = n) → (∀ i j, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) (M j) ∩ (V i ∩ V j)) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ (V i ∩ V j))), θ i x = θ j x ∧ ξ i x = ξ j x) → ∃ (M₀ : Set (Eucl P)) (θ₀ : Eucl P → ℝ) (ξ₀ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ n : ℕ, θ₀ x = n) ∧ ∀ i, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) M₀ ∩ V i) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ V i)), θ i x = θ₀ x ∧ ξ i x = ξ₀ x := by
  classical
  intro P k U TL V M θ ξ hV hUV hM hint hcompat
  -- Step 1: disjointification `D i = V i \ ⋃_{j<i} V j`.
  set D : ℕ → Set (Eucl P) := fun i => V i ∩ ⋂ j, ⋂ (_ : j < i), (V j)ᶜ with hD_def
  have hD_mem : ∀ x i, x ∈ D i ↔ x ∈ V i ∧ ∀ j < i, x ∉ V j := by
    intro x i
    simp only [hD_def, mem_inter_iff, mem_iInter, mem_compl_iff]
  have hD_meas : ∀ i, MeasurableSet (D i) := fun i =>
    (hV i).measurableSet.inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hV j).measurableSet.compl)
  have hDV : ∀ i, D i ⊆ V i := fun i x hx => ((hD_mem x i).1 hx).1
  -- Step 2: the least index `ι x` of a set `V j` containing `x`.
  let ι : Eucl P → ℕ := fun x => if h : ∃ j, x ∈ V j then Nat.find h else 0
  have hι_V : ∀ x i, x ∈ V i → x ∈ D (ι x) ∧ ι x ≤ i := by
    intro x i hx
    have h : ∃ j, x ∈ V j := ⟨i, hx⟩
    have hιx : ι x = Nat.find h := dite_eq_left h
    rw [hιx]
    exact ⟨(hD_mem x _).2 ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩, Nat.find_min' h hx⟩
  have hι_D : ∀ x i, x ∈ D i → ι x = i := by
    intro x i hx
    obtain ⟨hxV, hlt⟩ := (hD_mem x i).1 hx
    obtain ⟨hxD, hle⟩ := hι_V x i hxV
    rcases lt_or_eq_of_le hle with h | h
    · exact absurd ((hD_mem x _).1 hxD).1 (hlt _ h)
    · exact h
  -- Step 3: the glued triple.
  set M₀ : Set (Eucl P) := ⋃ i, M i ∩ D i with hM₀_def
  set θ₀ : Eucl P → ℝ := fun x => θ (ι x) x with hθ₀_def
  set ξ₀ : Eucl P → NVector (Eucl P) k := fun x => ξ (ι x) x with hξ₀_def
  have hθ₀_D : ∀ x i, x ∈ D i → θ₀ x = θ i x := by
    intro x i hx
    simp only [hθ₀_def, hι_D x i hx]
  have hξ₀_D : ∀ x i, x ∈ D i → ξ₀ x = ξ i x := by
    intro x i hx
    simp only [hξ₀_def, hι_D x i hx]
  have hM₀_D : ∀ x i, x ∈ D i → (x ∈ M₀ ↔ x ∈ M i) := by
    intro x i hx
    constructor
    · intro h
      obtain ⟨j, hjM, hjD⟩ := mem_iUnion.1 h
      rw [← hι_D x i hx, hι_D x j hjD]
      exact hjM
    · intro h
      exact mem_iUnion.2 ⟨i, h, hx⟩
  have hM₀_mem : ∀ x ∈ M₀, ∃ i, x ∈ M i ∧ x ∈ D i := by
    intro x hx
    obtain ⟨i, hiM, hiD⟩ := mem_iUnion.1 hx
    exact ⟨i, hiM, hiD⟩
  -- Step 4: agreement of the carriers on each `V i`.
  have hagree_set : ∀ i, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) M₀ ∩ V i) = 0 := by
    intro i
    refine measure_mono_null ?_ (measure_iUnion_null fun j => (hcompat i j).1)
    rintro x ⟨hxs, hxV⟩
    obtain ⟨hxD, -⟩ := hι_V x i hxV
    have hiff := hM₀_D x (ι x) hxD
    refine mem_iUnion.2 ⟨ι x, ?_, hxV, hDV _ hxD⟩
    rw [mem_symmDiff] at hxs ⊢
    rcases hxs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun h => h2 (hiff.2 h)⟩
    · exact Or.inr ⟨hiff.1 h1, h2⟩
  -- Step 5: agreement of weights and orientations on each `M i ∩ V i`.
  have hnm : ∀ i, NullMeasurableSet (M i) (μHE[k] : Measure (Eucl P)) :=
    fun i => (hM i).nullMeasurableSet
  have hagree_fun : ∀ i, ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ V i)),
      θ i x = θ₀ x ∧ ξ i x = ξ₀ x := by
    intro i
    have hall : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), ∀ j, x ∈ M i ∩ (V i ∩ V j) →
        θ i x = θ j x ∧ ξ i x = ξ j x := by
      rw [ae_all_iff]
      intro j
      exact (ae_restrict_iff'₀ ((hnm i).inter
        ((hV i).measurableSet.inter (hV j).measurableSet).nullMeasurableSet)).1 (hcompat i j).2
    rw [ae_restrict_iff'₀ ((hnm i).inter (hV i).measurableSet.nullMeasurableSet)]
    filter_upwards [hall] with x hx hxMV
    obtain ⟨hxD, -⟩ := hι_V x i hxMV.2
    obtain ⟨h1, h2⟩ := hx (ι x) ⟨hxMV.1, hxMV.2, hDV _ hxD⟩
    exact ⟨h1.trans (hθ₀_D x _ hxD).symm, h2.trans (hξ₀_D x _ hxD).symm⟩
  -- Steps 6–10: the triple conditions.
  have hpiece_nm : ∀ i, NullMeasurableSet (M i ∩ D i) (μHE[k] : Measure (Eucl P)) :=
    fun i => (hnm i).inter (hD_meas i).nullMeasurableSet
  -- Not found by instance search; the topologies agree definitionally.
  have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) k) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (NVector (Eucl P) k) _
  refine ⟨M₀, θ₀, ξ₀, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun i => ⟨hagree_set i, hagree_fun i⟩⟩
  · -- subset
    intro x hx
    obtain ⟨i, hiM, -⟩ := hM₀_mem x hx
    exact (hM i).subset hiM
  · -- nullMeasurableSet
    exact NullMeasurableSet.iUnion hpiece_nm
  · -- countablyRectifiable
    exact (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion M
      (fun i => (hM i).countablyRectifiable)).mono (iUnion_mono fun i => inter_subset_left)
  · -- pos
    intro x hx
    obtain ⟨i, hiM, hiD⟩ := hM₀_mem x hx
    rw [hθ₀_D x i hiD]
    exact (hM i).pos x hiM
  · -- integrableOn: a compact `K ⊆ U` meets only `D 0, …, D N`
    intro K hK hKU
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (hKU.trans hUV)
    set N : ℕ := t.sup id with hN
    have hsub : M₀ ∩ K ⊆ ⋃ j ∈ Finset.range (N + 1), M j ∩ K ∩ D j := by
      rintro x ⟨hxM, hxK⟩
      obtain ⟨i, hiM, hiD⟩ := hM₀_mem x hxM
      obtain ⟨l, hlt, hxl⟩ := mem_iUnion₂.1 (ht hxK)
      have hil : i ≤ l := by
        rw [← hι_D x i hiD]
        exact (hι_V x l hxl).2
      have hlN : l ≤ N := Finset.le_sup (f := id) hlt
      exact mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le (hil.trans hlN)),
        ⟨hiM, hxK⟩, hiD⟩
    refine IntegrableOn.mono_set ?_ hsub
    refine integrableOn_finset_iUnion.2 fun j _ => ?_
    have hj : IntegrableOn (θ j) (M j ∩ K ∩ D j) (μHE[k] : Measure (Eucl P)) :=
      ((hM j).integrableOn K hK hKU).mono_set inter_subset_left
    refine hj.congr_fun_ae ?_
    filter_upwards [ae_restrict_mem₀ (((hnm j).inter hK.measurableSet.nullMeasurableSet).inter
      (hD_meas j).nullMeasurableSet)] with x hx
    exact (hθ₀_D x j hx.2).symm
  · -- aestronglyMeasurable
    rw [hM₀_def, aestronglyMeasurable_iUnion_iff]
    intro i
    refine ((hM i).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)).congr ?_
    filter_upwards [ae_restrict_mem₀ (hpiece_nm i)] with x hx
    exact (hξ₀_D x i hx.2).symm
  · -- orients: transfer the tangent space from `(M i, θ i)` by (TL) with `W = V i`
    rw [hM₀_def, ae_restrict_iUnion_iff]
    intro i
    filter_upwards [ae_restrict_mem₀ (hpiece_nm i),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hM i).orients]
      with x hx ⟨τ, hτ, htan, hsign⟩
    refine ⟨τ, hτ, ?_, ?_⟩
    · exact TL (M i) M₀ (θ i) θ₀ x (V i) (hV i) (hDV i hx.2) (hagree_set i)
        ((hagree_fun i).mono fun y hy => hy.1) (hθ₀_D x i hx.2).symm _ htan
    · rw [hξ₀_D x i hx.2]
      exact hsign
  · -- integrality
    intro x hx
    obtain ⟨i, hiM, hiD⟩ := hM₀_mem x hx
    rw [hθ₀_D x i hiD]
    exact hint i x hiM
/-- Locality of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1 (‡)), the locality step in the proof of 6.3: on
forms `ω` with `tsupport ω ⊆ V`, `V` open, `τ(M, θ, ξ)(ω)` only depends on `M ∩ V` up to
`Hᵏ`-null sets and on `θ, ξ` up to `Hᵏ ⌞ (M ∩ V)`-null sets.  Both integrands vanish off `V`,
so `∫_M = ∫_{M ∩ V}` and `∫_{M'} = ∫_{M' ∩ V}`; these agree since `M ∩ V`, `M' ∩ V` are
`Hᵏ`-a.e. equal and the integrands agree a.e. on `M ∩ V`.  No integrability is needed. -/
theorem Submission.ltg_tau_congr_on_open :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (ξ ξ' : Eucl P → NVector (Eucl P) k)
      (V : Set (Eucl P)), IsOpen V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ x = θ' x ∧ ξ x = ξ' x) →
      ∀ ω : DifferentialForm (Eucl P) k, tsupport ω ⊆ V →
        tauAction k M θ ξ ω = tauAction k M' θ' ξ' ω := by
  intro P k M M' θ θ' ξ ξ' V hV hMM' hθξ ω hω
  -- Both integrands vanish off `V`, since `ω = 0` off `tsupport ω ⊆ V`.
  have hvan : ∀ (η : Eucl P → ℝ) (ζ : Eucl P → NVector (Eucl P) k) (x : Eucl P), x ∉ V →
      η x * ζ x (ω x) = 0 := by
    intro η ζ x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), map_zero, mul_zero]
  -- Hence `∫_A = ∫_{A ∩ V}` for both integrands.
  have hcut : ∀ (A : Set (Eucl P)) (η : Eucl P → ℝ) (ζ : Eucl P → NVector (Eucl P) k),
      ∫ x in A, η x * ζ x (ω x) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ x in A ∩ V, η x * ζ x (ω x) ∂(μHE[k] : Measure (Eucl P)) := by
    intro A η ζ
    rw [inter_comm, ← Measure.restrict_restrict hV.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan η ζ)]
  -- `M ∩ V` and `M' ∩ V` differ by subsets of the null set `(M ∆ M') ∩ V`.
  have hset : M ∩ V =ᵐ[(μHE[k] : Measure (Eucl P))] M' ∩ V := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ hMM'
      rintro x ⟨⟨hxM, hxV⟩, hx⟩
      exact ⟨Or.inl ⟨hxM, fun hxM' => hx ⟨hxM', hxV⟩⟩, hxV⟩
    · refine measure_mono_null ?_ hMM'
      rintro x ⟨⟨hxM', hxV⟩, hx⟩
      exact ⟨Or.inr ⟨hxM', fun hxM => hx ⟨hxM, hxV⟩⟩, hxV⟩
  -- The integrands agree `Hᵏ ⌞ (M ∩ V)`-a.e.
  have hae : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)),
      θ x * ξ x (ω x) = θ' x * ξ' x (ω x) := by
    filter_upwards [hθξ] with x hx
    rw [hx.1, hx.2]
  calc tauAction k M θ ξ ω
      = ∫ x in M ∩ V, θ x * ξ x (ω x) ∂(μHE[k] : Measure (Eucl P)) := hcut M θ ξ
    _ = ∫ x in M ∩ V, θ' x * ξ' x (ω x) ∂(μHE[k] : Measure (Eucl P)) := integral_congr_ae hae
    _ = ∫ x in M' ∩ V, θ' x * ξ' x (ω x) ∂(μHE[k] : Measure (Eucl P)) :=
        setIntegral_congr_set hset
    _ = tauAction k M' θ' ξ' ω := (hcut M' θ' ξ').symm

/-- **Local-to-global for `τ(M, θ, ξ)` via a smooth partition of unity** (Simon Ch. 6, 3.1 (‡);
used in the local-to-global step of the proof of 6.3).  If every `x ∈ U` has an open
`V_x ∋ x` such that `X ∈ 𝒟ₖ(U)` agrees with `τ(M, θ, ξ)` on the test forms supported in `V_x`,
then `X = τ(M, θ, ξ)` on `𝒟ᵏ(U)`.
Cover the compact `K = spt ω ⊆ U` by finitely many `V_y` (`y ∈ K`), take a smooth partition of
unity `χ_y` on `K` subordinate to them and split `ω = ∑_y χ_y ω`: each `χ_y ω ∈ 𝒟ᵏ(U)` has support
in `V_y`, so `X(χ_y ω) = τ(χ_y ω)`; conclude by linearity of `X` and of the integral, each
`θ ⟨χ_y ω, ξ⟩` being `Hᵏ`-integrable on `M` by `Submission.ltg_tau_integrable`. -/
theorem Submission.ltg_tau_local_to_global :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U k) (M : Set (Eucl P))
      (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ →
      (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ ∀ ω : TestFormOn U k,
        tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = tauAction k M θ ξ ω) →
      ∀ ω : TestFormOn U k, X ω = tauAction k M θ ξ ω := by
  intro P k U X M θ ξ hT hloc ω
  classical
  -- 1. `f := ω` is smooth with compact support `K := tsupport f ⊆ U`.
  obtain ⟨f, hf⟩ := ω
  have ⟨⟨hfs, hfc⟩, hfU⟩ : IsTestForm f ∧ tsupport f ⊆ U := hf
  -- 2. Finitely many of the neighbourhoods `V y` (`y ∈ K`) cover `K`.
  choose! V hVo hyV hXV using hloc
  obtain ⟨t, htK⟩ := hfc.isCompact.elim_finite_subcover (fun y : tsupport f => V y)
    (fun y => hVo y (hfU y.2)) (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyV y (hfU hy)⟩)
  -- 3. A smooth partition of unity `χ` on `K` subordinate to `(V y)_{y ∈ t}`.
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Eucl P)) (isClosed_tsupport f)
    (fun i : t => V (i : tsupport f)) (fun i => hVo _ (hfU (i : tsupport f).2)) fun y hy => by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (htK hy)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hyi⟩
  -- 4. The pieces `g i := χ i • f` are test forms in `U`, supported in `V i`.
  let g : t → DifferentialForm (Eucl P) k := fun i x => χ i x • f x
  have hg : ∀ i, IsTestForm (g i) ∧ tsupport (g i) ⊆ U := fun i =>
    ⟨⟨(contMDiff_iff_contDiff.mp (χ i).contMDiff).smul hfs,
      hfc.mono (Function.support_smul_subset_right (fun x => χ i x) f)⟩,
      (tsupport_smul_subset_right _ _).trans hfU⟩
  have hgV : ∀ i, tsupport (g i) ⊆ V (i : tsupport f) := fun i =>
    (tsupport_smul_subset_left _ _).trans (hχ i)
  -- 5. `f = ∑ i, g i`: on `K` because `∑ i, χ i = 1` there, off `K` because `f = 0` there.
  have hsum : ∀ x, ∑ i : t, g i x = f x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have h1 : ∑ i : t, χ i x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact χ.sum_eq_one hx
      simp only [g]
      rw [← Finset.sum_smul, h1, one_smul]
    · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [g, h0]
  have hω : (⟨f, hf⟩ : TestFormOn U k) = ∑ i : t, (⟨g i, hg i⟩ : TestFormOn U k) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    rw [Finset.sum_apply]
    exact (hsum x).symm
  -- 6. Linearity of `X`, and local agreement `X (g i) = τ (g i)` on each piece.
  have hX : X ⟨f, hf⟩ = ∑ i : t, tauAction k M θ ξ (g i) := by
    rw [hω]
    refine (map_sum X.toCurrent _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact hXV (i : tsupport f) (hfU (i : tsupport f).2) ⟨g i, hg i⟩ (hgV i)
  -- 7. Linearity of the integral (each piece is integrable by `tau_integrable`) and of `ξ x`.
  have hint : ∀ i ∈ (Finset.univ : Finset t),
      Integrable (fun x => θ x * ξ x (g i x)) ((μHE[k] : Measure (Eucl P)).restrict M) :=
    fun i _ => (Submission.ltg_tau_integrable P k U M θ ξ hT).2 (g i) (hg i).1.1.continuous
      (hg i).1.2 (hg i).2
  rw [hX]
  unfold tauAction
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Finset.mul_sum, ← map_sum (ξ x) (fun i => g i x) Finset.univ, hsum x]
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the
proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to
`Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets, `V ∋ x` open.  If `B_δ(x) ⊆ V` and
`f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off
`W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and
`(M', θ')` agree for all small `r`. -/
theorem Submission.br_weightedTangent_congr :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P) (V : Set (Eucl P)),
      IsOpen V → x ∈ V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ y = θ' y) → θ x = θ' x →
      ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k M' θ' x L := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k M M' θ θ' x V hV hxV hMM' hθθ' hθx L hL
  -- `η_r(y) = r⁻¹ (y - x)` maps `Hᵏ`-null sets to `Hᵏ`-null sets: `Hᵏ(η_r Z) = r⁻ᵏ Hᵏ(Z)`.
  have hnull : ∀ r : ℝ, r ≠ 0 → ∀ Z : Set (Eucl P), (μHE[k] : Measure (Eucl P)) Z = 0 →
      (μHE[k] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- A measurable `N ⊇ {θ ≠ θ'}` with `Hᵏ(N ∩ M ∩ V) = 0`.
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hθθ')
  rw [Measure.restrict_apply hNmeas] at hN0
  refine ⟨hL.1, fun f => ?_⟩
  rw [← hθx]
  refine (hL.2 f).congr' ?_
  -- `f = 0` off `B_R(0)` and `B_δ(x) ⊆ V`; the blow-up integrals agree for `0 < r < δ / R`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hcont : Continuous fun y : Eucl P => x + r • y :=
    continuous_const.add (continuous_const_smul r)
  -- `W = η_r(V)` is open and the integrands `f(y) g(x + r y)` vanish off `W`.
  set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' V with hW
  have hWmeas : MeasurableSet W := (hV.preimage hcont).measurableSet
  have hvan : ∀ g : Eucl P → ℝ, ∀ y, y ∉ W → f y * g (x + r • y) = 0 := by
    intro g y hy
    have hfy : f y = 0 := by
      apply hfR
      have h1 : x + r • y ∉ ball x δ := fun h => hy (hδV h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, not_lt] at h1
      rw [lt_div_iff₀ hR] at hrR
      exact le_of_lt (lt_of_mul_lt_mul_left (hrR.trans_le h1) hr0.le)
    rw [hfy, zero_mul]
  -- Cutting by `W`: `∫_{η_r(S)} = ∫_{W ∩ η_r(S)}`.
  have hcut : ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ y in W ∩ blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
    intro S g
    rw [← Measure.restrict_restrict hWmeas,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan g)]
  -- `W ∩ η_r(M) = W ∩ η_r(M')` up to the null set `η_r((M ∆ M') ∩ V)`.
  have hset : W ∩ blowUpMap x r '' M =ᵐ[(μHE[k] : Measure (Eucl P))] W ∩ blowUpMap x r '' M' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inl ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inr ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
  -- `θ(x + r y) = θ'(x + r y)` a.e. on `W ∩ η_r(M)`, off the null set `η_r(N ∩ M ∩ V)`.
  have hae : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (W ∩ blowUpMap x r '' M)),
      f y * θ (x + r • y) = f y * θ' (x + r • y) := by
    have hN'meas : MeasurableSet ((fun y => x + r • y) ⁻¹' N) :=
      hNmeas.preimage hcont.measurable
    rw [ae_iff]
    refine measure_mono_null (t := (fun y => x + r • y) ⁻¹' N) ?_ ?_
    · intro y hy
      by_contra hyN
      apply hy
      have hθy : θ (x + r • y) = θ' (x + r • y) := by
        by_contra hne
        exact hyN (hNsub hne)
      rw [hθy]
    · rw [Measure.restrict_apply hN'meas]
      refine measure_mono_null ?_ (hnull r hr0.ne' _ hN0)
      rintro y ⟨hyN, hyW, z, hzM, rfl⟩
      refine ⟨z, ⟨?_, hzM, ?_⟩, rfl⟩
      · simpa [hinv r hr0.ne' z] using hyN
      · simpa [hW, hinv r hr0.ne' z] using hyW
  calc ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P))
      = ∫ y in W ∩ blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        hcut M θ
    _ = ∫ y in W ∩ blowUpMap x r '' M, f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        integral_congr_ae hae
    _ = ∫ y in W ∩ blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
        rw [Measure.restrict_congr_set hset]
    _ = ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        (hcut M' θ').symm

/-- Integer multiplicity is local (the patching step in the proof of Simon Ch. 6, 6.3): if every
`x ∈ U` has an open `V ∋ x` on which `X` agrees with an integer multiplicity current, then `X` is
integer multiplicity.  By Lindelöf countably many such `V_i`, with `Y_i = τ(M_i, θ_i, ξ_i)`, cover
`U`.  Two of these triples agree up to null sets on `V_i ∩ V_j`, where both represent `X`, so they
glue to one integer multiplicity triple `(M₀, θ₀, ξ₀)` that agrees with each on its `V_i`; then
`X = τ(M₀, θ₀, ξ₀)` on forms supported in some `V_i`, hence on all forms. -/
theorem Submission.br_isIntegerMultiplicity_of_local :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y ∧
          ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = Y ω) →
      IsIntegerMultiplicity X := by
  intro P k U _ X hloc
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · -- `U = ∅`: `X = τ(∅, 0, 0)`, since the local hypothesis is vacuous.
    have hT : IsRectifiableTriple (∅ : Set (Eucl P)) k ∅ 0 0 :=
      { subset := subset_rfl
        nullMeasurableSet := nullMeasurableSet_empty
        countablyRectifiable :=
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
        pos := fun x hx => absurd hx (notMem_empty x)
        integrableOn := fun K _ _ => by simp
        aestronglyMeasurable := by simp
        orients := by simp }
    exact ⟨∅, 0, 0, hT, fun x hx => absurd hx (notMem_empty x),
      Submission.ltg_tau_local_to_global P k ∅ X ∅ 0 0 hT fun x hx => absurd hx (notMem_empty x)⟩
  -- For each `x ∈ U` choose `V_x` and `Y_x`.
  choose! Vx hVo hxV hVU Y hY hXY using hloc
  -- Lindelöf: a countable subfamily `V_{f i}` (`i ∈ ℕ`) covers `U`.
  obtain ⟨T, hTU, hTc, hTV⟩ := TopologicalSpace.isOpen_biUnion_countable U Vx hVo
  have hcovT : U ⊆ ⋃ x ∈ T, Vx x := by
    rw [hTV]
    exact fun x hx => mem_biUnion hx (hxV x hx)
  obtain ⟨f, rfl⟩ : ∃ f : ℕ → Eucl P, T = range f := by
    refine hTc.exists_eq_range ?_
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (hcovT hx)
    exact ⟨y, hy⟩
  have hfU : ∀ i, f i ∈ U := fun i => hTU (mem_range_self i)
  have hcover : U ⊆ ⋃ i, Vx (f i) := by
    intro x hx
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.mp (hcovT hx)
    exact mem_iUnion.mpr ⟨i, hxy⟩
  -- `Y_{f i} = τ(M_i, θ_i, ξ_i)` with integer multiplicity triples.
  have hY' : ∀ i, ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ ∧ (∀ x ∈ M, ∃ n : ℕ, θ x = n) ∧
        ∀ ω : TestFormOn U k, Y (f i) ω = tauAction k M θ ξ ω :=
    fun i => hY (f i) (hfU i)
  choose M θ ξ hT hθ hrep using hY'
  -- On `V_{f i} ∩ V_{f j}` both triples represent `X`, so they agree there up to null sets.
  have hcompat : ∀ i j, (μHE[k] : Measure (Eucl P))
        (symmDiff (M i) (M j) ∩ (Vx (f i) ∩ Vx (f j))) = 0 ∧
      ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ (Vx (f i) ∩ Vx (f j)))),
        θ i x = θ j x ∧ ξ i x = ξ j x := fun i j =>
    Submission.ltg_tau_unique_on_open P k U (Vx (f i) ∩ Vx (f j))
      ((hVo _ (hfU i)).inter (hVo _ (hfU j))) (inter_subset_left.trans (hVU _ (hfU i)))
      (M i) (M j) (θ i) (θ j) (ξ i) (ξ j) (hT i) (hT j) fun ω hω => by
        rw [← hrep i ω, ← hrep j ω, ← hXY _ (hfU i) ω (hω.trans inter_subset_left),
          ← hXY _ (hfU j) ω (hω.trans inter_subset_right)]
  -- Glue them (tangent spaces transfer by `br_weightedTangent_congr`).
  obtain ⟨M₀, θ₀, ξ₀, hT₀, hθ₀, hagree⟩ :=
    Submission.ltg_glue_triples P k U (Submission.br_weightedTangent_congr P k)
      (fun i => Vx (f i)) M θ ξ (fun i => hVo _ (hfU i)) hcover hT hθ hcompat
  -- `X = Y_{f i} = τ(M_i, θ_i, ξ_i) = τ(M₀, θ₀, ξ₀)` on forms supported in `V_{f i}`.
  refine ⟨M₀, θ₀, ξ₀, hT₀, hθ₀, Submission.ltg_tau_local_to_global P k U X M₀ θ₀ ξ₀ hT₀ ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  refine ⟨Vx (f i), hVo _ (hfU i), hxi, fun ω hω => ?_⟩
  rw [hXY _ (hfU i) ω hω, hrep i ω]
  exact Submission.ltg_tau_congr_on_open P k (M i) M₀ (θ i) θ₀ (ξ i) ξ₀ (Vx (f i))
    (hVo _ (hfU i)) (hagree i).1 (hagree i).2 ω hω

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
