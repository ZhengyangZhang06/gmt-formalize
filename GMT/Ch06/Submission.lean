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

/-- Coordinate expansion of an `n`-covector on `ℝ^P` in the wedge basis:
`α = ∑_β α(e_{β(0)}, …, e_{β(n-1)}) dx^β` over the increasing multi-indices `β`. -/
theorem Submission.cmb_covector_eq_sum_coord_smul_wedge :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n), α = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) := by
  intro P n α
  classical
  -- `e v = (e_{v 0}, …, e_{v (n - 1)})` for a tuple `v` of coordinate indices.
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1
  set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
    euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) with hR
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P,
      wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · -- the matrix `[δ_{β i, β j}]` is the identity
      subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · -- some `β i` is not among the `γ j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
        by_contra! h
        apply hβγ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range β ⊆ Set.range γ := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range γ)
        rw [Set.ncard_range_of_injective γ.injective, Set.ncard_range_of_injective β.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [e, PiLp.single_apply, hi j]
  -- `R` agrees with `α` on increasing tuples of basis vectors.
  have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
    intro γ
    rw [hR, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  -- `R` agrees with `α` on injective tuples: sort them and use `map_perm`.
  have h2 : ∀ v : Fin n → Fin P, Function.Injective v → R (e v) = α (e v) := by
    intro v hv
    have hsm : StrictMono (v ∘ Tuple.sort v) :=
      (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
    have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
    have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
    rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
      ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
      AlternatingMap.map_perm] at hγ
    exact smul_left_cancel _ hγ
  -- Conclude by extensionality on the standard basis.
  symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  exact h2 v hv
/-- A coordinate of an `n`-covector is bounded by its Euclidean coefficient norm:
`|α(e_{β(0)}, …, e_{β(n-1)})| ≤ |α|` for every increasing multi-index `β`. -/
theorem Submission.cmb_rb_abs_euclideanCovectorCoordinate_le :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n) (β : SimonMultiIndex n P),
      |euclideanCovectorCoordinate α β| ≤ covectorEuclideanNorm α := by
  intro P n α β
  -- `|c| = √(c²)` and `√` is monotone, so it suffices to bound `c²` by the defining sum.
  rw [covectorEuclideanNorm, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  -- `c²` is the summand of the strictly increasing tuple `β`; every summand is nonnegative.
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun I _ => ?_) (Finset.mem_univ ⇑β))
  · simp only [euclideanCovectorCoordinate, β.strictMono, ↓reduceIte,
      EuclideanSpace.basisFun_apply]
  · exact ite_nonneg (sq_nonneg _) le_rfl

/-- Evaluation bound for an `n`-covector at an arbitrary tuple of vectors:
`|φ(v)| ≤ (∑_β |dx^β(v)|) · |φ|`, summing over the increasing multi-indices `β`. -/
theorem Submission.rpn_moc_abs_covector_apply_le :
    ∀ (P n : ℕ) (φ : Covector (Eucl P) n) (v : Fin n → Eucl P), |φ v| ≤
      (∑ β : SimonMultiIndex n P,
        |wedgeCovectors n (fun j => (EuclideanSpace.proj (β j) : Eucl P →L[ℝ] ℝ)) v|) *
        covectorEuclideanNorm φ := by
  intro P n φ v
  -- Evaluate the coordinate expansion `φ = ∑_β φ(e_β) dx^β` at `v`.
  have hexp := DFunLike.congr_fun (Submission.cmb_covector_eq_sum_coord_smul_wedge P n φ) v
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at hexp
  -- Triangle inequality, then `|φ(e_β)| ≤ |φ|` termwise.
  rw [hexp, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right
    (Submission.cmb_rb_abs_euclideanCovectorCoordinate_le P n φ β) (abs_nonneg _)).trans_eq
    (mul_comm _ _)

/-- Pairing bound for a unit `n`-vector on `ℝ^P`: if `∑_β w(dx^β)² = 1`, then
`|w(θ)| ≤ ∑_β |θ(e_{β(0)}, …, e_{β(n-1)})|`. -/
theorem Submission.rpn_moc_abs_nvector_apply_le :
    ∀ (P n : ℕ) (w : NVector (Eucl P) n) (θ : Covector (Eucl P) n),
      ∑ β : SimonMultiIndex n P, (euclideanNVectorCoordinate w β) ^ 2 = 1 →
      |w θ| ≤ ∑ β : SimonMultiIndex n P, |euclideanCovectorCoordinate θ β| := by
  intro P n w θ hw
  -- Each coordinate `w(dx^β)` is one nonnegative summand of `∑_γ w(dx^γ)² = 1`.
  have hcoord : ∀ β : SimonMultiIndex n P, |euclideanNVectorCoordinate w β| ≤ 1 := by
    intro β
    rw [← sq_le_one_iff_abs_le_one, ← hw]
    exact Finset.single_le_sum (f := fun γ => euclideanNVectorCoordinate w γ ^ 2)
      (fun γ _ => sq_nonneg _) (Finset.mem_univ β)
  -- Expand `θ = ∑_β θ(e_β) dx^β` and apply the linear map `w`.
  have hexp : w θ = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate θ β * euclideanNVectorCoordinate w β := by
    conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P n θ]
    simp only [map_sum, map_smul, smul_eq_mul, euclideanNVectorCoordinate]
  -- Triangle inequality, then `|θ(e_β)| |w(dx^β)| ≤ |θ(e_β)|`.
  rw [hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hcoord β)
/-- A smooth compactly supported `f` with `tsupport f ⊆ U` times a constant `n`-covector `θ`
is a test form in `𝒟ⁿ(U)`: `φ(x) = f(x) θ`. -/
theorem Submission.rpn_moc_exists_testForm_smul :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (f : Eucl P → ℝ) (θ : Covector (Eucl P) n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U →
        ∃ φ : TestFormOn U n, ∀ x, (φ : DifferentialForm (Eucl P) n) x = f x • θ := by
  intro P n U f θ hf hcf hsf
  -- `x ↦ f x • θ` is smooth, compactly supported, and `tsupport (f • θ) ⊆ tsupport f ⊆ U`.
  exact ⟨⟨fun x => f x • θ, ⟨⟨hf.smul contDiff_const, hcf.smul_right⟩,
    (tsupport_smul_subset_left f fun _ => θ).trans hsf⟩⟩, fun _ => rfl⟩
/-- Representation estimate on `W \ K`: if `φ = h • θ` where `|h| ≤ c`, `h = 0` off `W` and on
`K`, and `|ξ(x)(θ)| ≤ c'` for `μ`-a.e. `x`, then `|T φ| ≤ c c' μ(W \ K)`. -/
theorem Submission.rpn_moc_abs_apply_le_mul_measure_diff :
    ∀ (P n : ℕ) (U W K : Set (Eucl P)) (T : GeometricCurrentOn U n) (μ : Measure (Eucl P))
      (ξ : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ ξ → IsOpen W →
      IsCompact K → μ (W \ K) ≠ ∞ → ∀ (θ : Covector (Eucl P) n) (h : Eucl P → ℝ) (c c' : ℝ),
      (∀ x, |h x| ≤ c) → (∀ x, x ∉ W → h x = 0) → (∀ x ∈ K, h x = 0) →
      (∀ᵐ x ∂μ, |ξ x θ| ≤ c') → ∀ φ : TestFormOn U n,
      (∀ x, (φ : DifferentialForm (Eucl P) n) x = h x • θ) →
      |T φ| ≤ c * c' * (μ (W \ K)).toReal := by
  intro P n U W K T μ ξ hrep hW hK hμ θ h c c' hc hW0 hK0 hξ φ hφ
  have hA : MeasurableSet (W \ K) := hW.measurableSet.diff hK.isClosed.measurableSet
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- the integrand is `h x * ξ(x)(θ)`
  have hg : ∀ x, ξ x ((φ : DifferentialForm (Eucl P) n) x) = h x * ξ x θ := fun x => by
    rw [hφ x, map_smul, smul_eq_mul]
  -- `μ`-a.e. domination by `c c' 1_{W \ K}`
  have hbound : ∀ᵐ x ∂μ, ‖ξ x ((φ : DifferentialForm (Eucl P) n) x)‖ ≤
      (W \ K).indicator (fun _ => c * c') x := by
    filter_upwards [hξ] with x hx
    rw [hg x, Real.norm_eq_abs, abs_mul]
    by_cases hxA : x ∈ W \ K
    · rw [Set.indicator_of_mem hxA]
      exact mul_le_mul (hc x) hx (abs_nonneg _) hc0
    · have hx0 : h x = 0 := by
        by_cases hxW : x ∈ W
        · exact hK0 x (not_not.mp fun hxK => hxA ⟨hxW, hxK⟩)
        · exact hW0 x hxW
      rw [Set.indicator_of_notMem hxA, hx0, abs_zero, zero_mul]
  have hG : Integrable ((W \ K).indicator fun _ => c * c') μ :=
    (integrable_indicator_iff hA).2 (integrableOn_const hμ)
  rw [(hrep φ).2, ← Real.norm_eq_abs]
  calc ‖∫ x, ξ x ((φ : DifferentialForm (Eucl P) n) x) ∂μ‖
      ≤ ∫ x, (W \ K).indicator (fun _ => c * c') x ∂μ := norm_integral_le_of_norm_le hG hbound
    _ = c * c' * (μ (W \ K)).toReal := by
      rw [integral_indicator_const _ hA, measureReal_def, smul_eq_mul, mul_comm]

/-- Cut-off estimate for the top-degree form `f θ_L`, `θ_L = L^*(dy¹ ∧ ⋯ ∧ dyⁿ)` (Simon Ch. 6,
proof of Lemma 2.36, display (2)): from the pullback bound (H1) and cut-offs `b = 1` on `L(K)`
with `𝓛ⁿ(spt b)` arbitrarily small (H2), `|T(f θ_L)| ≤ c c' μ(W \ K)`. -/
theorem Submission.rpn_moc_abs_apply_top_form_le :
    ∀ (P m : ℕ) (U W K : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ ξ → IsOpen W →
      W ⊆ U → IsCompact K → μ (W \ K) ≠ ∞ →
      ∀ (L : Eucl P →L[ℝ] Eucl (m + 1)) (f : Eucl P → ℝ) (c c' : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ W →
      (∀ x, |f x| ≤ c) →
      (∀ᵐ x ∂μ, |ξ x (wedgeCovectors (m + 1)
        (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L))| ≤ c') →
      (∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a →
        HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ φ : TestFormOn U (m + 1),
        (∀ x, (φ : DifferentialForm (Eucl P) (m + 1)) x = (f x * a (L x)) •
          wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) →
        |T φ| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))) →
      (∀ δ : ℝ, 0 < δ → ∃ b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧
        HasCompactSupport b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∈ L '' K, b y = 1) ∧
        ((volume : Measure (Eucl (m + 1))) (tsupport b)).toReal ≤ δ) →
      ∀ ζ : TestFormOn U (m + 1), (∀ x, (ζ : DifferentialForm (Eucl P) (m + 1)) x =
        f x • wedgeCovectors (m + 1)
          (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) →
      |T ζ| ≤ c * c' * (μ (W \ K)).toReal := by
  intro P m U W K T μ ξ hrep hW hWU hK hμK L f c c' hf hfc hfW hfle hξ hH1 hH2 ζ hζ
  obtain ⟨C, hC⟩ := hH1
  set θ : Covector (Eucl P) (m + 1) :=
    wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)
  -- Step 1: it suffices to prove `|T ζ| ≤ c c' μ(W \ K) + ε` for every `ε > 0`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Step 2: a cut-off `b` from (H2) for `δ = (ε / (|C| + 1))ⁿ`.
  have hA : 0 < |C| + 1 := by positivity
  obtain ⟨b, hb, hbc, hb01, hbK, hbδ⟩ := hH2 ((ε / (|C| + 1)) ^ (m + 1)) (by positivity)
  -- Step 3: the test form `φ₁ = (f · (b ∘ L)) θ_L`.
  obtain ⟨φ₁, hφ₁⟩ := Submission.rpn_moc_exists_testForm_smul P (m + 1) U
    (fun x => f x * b (L x)) θ (hf.mul (hb.comp L.contDiff))
    (hfc.mul_right (f' := fun x => b (L x))) (tsupport_mul_subset_left.trans (hfW.trans hWU))
  -- Step 4: (H1) with `a = b`, `M = 1` gives `|T φ₁| ≤ |C| 𝓛ⁿ(spt b)^{1/n} ≤ ε`.
  have h₁ : |T φ₁| ≤ ε := by
    set v : ℝ := ((volume (tsupport b)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))
    have hv0 : 0 ≤ v := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hvε : v ≤ ε / (|C| + 1) :=
      calc v ≤ ((ε / (|C| + 1)) ^ (m + 1)) ^ ((1 : ℝ) / ((m : ℝ) + 1)) :=
            Real.rpow_le_rpow ENNReal.toReal_nonneg hbδ (by positivity)
        _ = ε / (|C| + 1) := by
            rw [show (1 : ℝ) / ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ)⁻¹ by push_cast; ring]
            exact Real.pow_rpow_inv_natCast (by positivity) (Nat.succ_ne_zero m)
    calc |T φ₁| ≤ C * 1 * v :=
          hC b hb hbc 1 (fun y => (abs_of_nonneg (hb01 y).1).trans_le (hb01 y).2) φ₁ hφ₁
      _ ≤ |C| * (ε / (|C| + 1)) := by
          rw [mul_one]
          exact mul_le_mul (le_abs_self C) hvε hv0 (abs_nonneg C)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hA]
          nlinarith [abs_nonneg C]
  -- Step 5: `φ₂ = ζ - φ₁ = h θ_L` with `h = f · (1 - b ∘ L)`.
  have hφ₂ : ∀ x, ((ζ - φ₁ : TestFormOn U (m + 1)) : DifferentialForm (Eucl P) (m + 1)) x =
      (f x * (1 - b (L x))) • θ := by
    intro x
    rw [Submodule.coe_sub, Pi.sub_apply, hζ x, hφ₁ x]
    ext v
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  -- Step 6: `|h| ≤ c`, `h = 0` off `W` and `h = 0` on `K`.
  have hh_le : ∀ x, |f x * (1 - b (L x))| ≤ c := by
    intro x
    have h01 := hb01 (L x)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr h01.2)]
    calc |f x| * (1 - b (L x)) ≤ |f x| * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [h01.1]) (abs_nonneg _)
      _ ≤ c := by rw [mul_one]; exact hfle x
  have hh_W : ∀ x, x ∉ W → f x * (1 - b (L x)) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (hfW hx'), zero_mul]
  have hh_K : ∀ x ∈ K, f x * (1 - b (L x)) = 0 := by
    intro x hx
    rw [hbK (L x) (mem_image_of_mem L hx), sub_self, mul_zero]
  -- Step 7: the remainder bound for `φ₂`.
  have h₂ : |T (ζ - φ₁)| ≤ c * c' * (μ (W \ K)).toReal :=
    Submission.rpn_moc_abs_apply_le_mul_measure_diff P (m + 1) U W K T μ ξ hrep hW hK hμK θ
      (fun x => f x * (1 - b (L x))) c c' hh_le hh_W hh_K hξ (ζ - φ₁) hφ₂
  -- Step 8: `T ζ = T φ₁ + T φ₂` and the triangle inequality.
  have hsplit : T ζ = T φ₁ + T (ζ - φ₁) := by
    rw [show T (ζ - φ₁) = T ζ - T φ₁ from map_sub T.toCurrent ζ φ₁]
    ring
  calc |T ζ| ≤ |T φ₁| + |T (ζ - φ₁)| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ c * c' * (μ (W \ K)).toReal + ε := by linarith
/-- Polar coordinates for an integrable `g` on `ℝ^{m+1}`, with `σ = (Lᵐ⁺¹).toSphere`:
`∫ g = ∫_{S^m} ∫_0^∞ r^m g(rθ) dr dσ(θ)`.  As in Mathlib's `integral_fun_norm_addHaar`,
`homeomorphUnitSphereProd` carries Lebesgue measure on `ℝ^{m+1} ∖ {0}` to `σ ⊗ volumeIoiPow m`,
Fubini splits the product, and `volumeIoiPow m` is `r^m dr` on `(0, ∞)`. -/
theorem Submission.rpn_pe_integral_eq_polar :
    ∀ (m : ℕ) (g : Eucl (m + 1) → ℝ), Integrable g → ∫ x, g x =
      ∫ θ : sphere (0 : Eucl (m + 1)) 1, (∫ r in Ioi (0 : ℝ), r ^ m * g (r • (θ : Eucl (m + 1))))
        ∂(volume : Measure (Eucl (m + 1))).toSphere := by
  intro m g hg
  -- `Φ = homeomorphUnitSphereProd` is measure preserving onto `σ ⊗ volumeIoiPow m`.
  have hdim : Module.finrank ℝ (Eucl (m + 1)) - 1 = m := by simp
  have hmp : MeasurePreserving (homeomorphUnitSphereProd (Eucl (m + 1)))
      ((volume : Measure (Eucl (m + 1))).comap (↑))
      ((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    have := (volume : Measure (Eucl (m + 1))).measurePreserving_homeomorphUnitSphereProd
    rwa [hdim] at this
  -- `G(θ, r) = g(rθ)` satisfies `G ∘ Φ = g` on `ℝ^{m+1} ∖ {0}`.
  set G : sphere (0 : Eucl (m + 1)) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => g ((p.2 : ℝ) • (p.1 : Eucl (m + 1))) with hG
  have hGΦ : ∀ x : ({0}ᶜ : Set (Eucl (m + 1))), G (homeomorphUnitSphereProd _ x) = g x := by
    intro x
    have hx : ‖(x : Eucl (m + 1))‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    simp only [hG, homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
    rw [smul_smul, mul_inv_cancel₀ hx, one_smul]
  -- Remove the null point `0`, then change variables along `Φ`.
  have h3 : ∫ x, g x = ∫ x : ({0}ᶜ : Set (Eucl (m + 1))), g x
      ∂((volume : Measure (Eucl (m + 1))).comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]
  have h4 : ∫ x : ({0}ᶜ : Set (Eucl (m + 1))), g x
      ∂((volume : Measure (Eucl (m + 1))).comap (↑)) =
      ∫ p, G p ∂((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) G]
    simp only [hGΦ]
  have h5 : Integrable G
      ((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : G ∘ homeomorphUnitSphereProd (Eucl (m + 1)) = g ∘ Subtype.val := funext hGΦ
    rw [this, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hg.integrableOn
  -- Fubini, then unfold `volumeIoiPow m = r^m dr` on `(0, ∞)` for each `θ`.
  rw [h3, h4, integral_prod G h5]
  congr 1
  funext θ
  simp only [hG, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ m) • g (a • (θ : Eucl (m + 1)))),
    setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal
/-- The radial integral `∫_{B_ρ(0)} |w|^{1-n} dw = n ω_n ρ` in `ℝⁿ`, `n = m + 1`, `ρ > 0`,
`ω_n = Lⁿ(B_1(0))` (formula (R) of the potential estimate in the proof of Simon Ch. 6, 8.1);
`|w|^{1-n}` is written `(‖w‖ ^ m)⁻¹`.  In polar coordinates (`integrableOn_fun_norm_addHaar`,
`integral_fun_norm_addHaar`) the radial profile `r^{n-1} (r^{n-1})⁻¹` is `1` on `(0, ρ)`: this
gives integrability, and with `1_{B_ρ(0)}(w) = 1_{(-∞, ρ)}(|w|)` the value `n ω_n ρ`. -/
theorem Submission.rpn_pe_inv_norm_pow_ball :
    ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) (ball (0 : Eucl (m + 1)) ρ) ∧ ∫ t in ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ = ((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ρ := by
  intro m ρ hρ
  have hdim : Module.finrank ℝ (Eucl (m + 1)) - 1 = m := by
    rw [finrank_euclideanSpace_fin, Nat.add_sub_cancel]
  constructor
  · -- Integrability: `r ^ m • (r ^ m)⁻¹ = 1` is integrable on `(0, ρ)`.
    rw [integrableOn_fun_norm_addHaar (volume : Measure (Eucl (m + 1)))
      (f := fun r : ℝ => (r ^ m)⁻¹), hdim]
    refine (integrableOn_congr_fun (g := fun _ => (1 : ℝ)) (fun r hr => ?_) measurableSet_Ioo).2
      (integrableOn_const measure_Ioo_lt_top.ne)
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hr.1))
  · -- `h = 1_{(-∞, ρ)} · (r ↦ (r ^ m)⁻¹)`, so `1_{B_ρ(0)}(w) (‖w‖ ^ m)⁻¹ = h ‖w‖`.
    set h : ℝ → ℝ := (Iio ρ).indicator fun r => (r ^ m)⁻¹ with hh
    have hind : (ball (0 : Eucl (m + 1)) ρ).indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) =
        fun t => h ‖t‖ := by
      ext t
      simp [hh, indicator]
    -- For `r > 0`, `r ^ m • h r = 1_{(-∞, ρ)}(r)`, so the radial integral is `L¹((0, ρ)) = ρ`.
    have hrad : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Eucl (m + 1)) - 1) • h y = ρ := by
      rw [hdim, setIntegral_congr_fun measurableSet_Ioi
        (g := (Iio ρ).indicator fun _ => (1 : ℝ)) (fun y hy => ?_)]
      · rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          setIntegral_const, Iio_inter_Ioi, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one, sub_zero]
      · by_cases hy' : y < ρ
        · simp [hh, indicator, hy', mul_inv_cancel₀ (pow_ne_zero m (ne_of_gt (mem_Ioi.1 hy)))]
        · simp [hh, indicator, hy']
    rw [← integral_indicator measurableSet_ball, hind,
      integral_fun_norm_addHaar (volume : Measure (Eucl (m + 1))) h, hrad,
      finrank_euclideanSpace_fin, measureReal_def, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-- Potential estimate over a set of finite measure (Gilbarg–Trudinger, proof of Lemma 7.12, with
the cruder constant `n + 1`): for measurable `S ⊆ ℝⁿ`, `n = m + 1`, with `Lⁿ(S) < ∞`, the kernel
`|w|^{1-n} = (|w|^m)⁻¹` is integrable on `S` and
`∫_S |w|^{1-n} dw ≤ (n + 1) ω^{(n-1)/n} Lⁿ(S)^{1/n}`, `ω = Lⁿ(B_1(0))`.  Split `S` at the radius
`ρ = (Lⁿ(S)/ω)^{1/n}`: the part inside `B_ρ(0)` contributes at most `∫_{B_ρ(0)} |w|^{1-n} = nωρ`,
the part outside at most `ρ^{1-n} Lⁿ(S) = ωρ`. -/
theorem Submission.rpn_pe_inv_norm_pow_set_bound : ∀ (m : ℕ) (S : Set (Eucl (m + 1))), MeasurableSet S → volume S ≠ ⊤ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) S ∧ ∫ t in S, (‖t‖ ^ m)⁻¹ ≤ ((m : ℝ) + 2) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal ^ ((m : ℝ) / ((m : ℝ) + 1)) * (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro m S hS hSfin
  -- Step 1: `f = (‖·‖ ^ m)⁻¹` is measurable and nonnegative.
  have hf_meas : Measurable (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) :=
    (measurable_norm.pow_const m).inv
  have hf_nonneg : ∀ t : Eucl (m + 1), 0 ≤ (‖t‖ ^ m)⁻¹ := fun t => by positivity
  -- Step 2: off `B_ρ(0)`, `f ≤ (ρ ^ m)⁻¹`; as `Lⁿ(S \ B_ρ(0)) < ∞`, `f` is integrable there.
  have hfar_le : ∀ ρ : ℝ, 0 < ρ → ∀ t ∈ S \ ball (0 : Eucl (m + 1)) ρ,
      (‖t‖ ^ m)⁻¹ ≤ (ρ ^ m)⁻¹ := by
    intro ρ hρ t ht
    have hρt : ρ ≤ ‖t‖ := by simpa using ht.2
    exact inv_anti₀ (pow_pos hρ m) (pow_le_pow_left₀ hρ.le hρt m)
  have hfar_fin : ∀ ρ : ℝ, volume (S \ ball (0 : Eucl (m + 1)) ρ) ≠ ⊤ := fun ρ =>
    ne_top_of_le_ne_top hSfin (measure_mono sdiff_subset)
  have hfar_int : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) (S \ ball (0 : Eucl (m + 1)) ρ) := by
    intro ρ hρ
    refine Measure.integrableOn_of_bounded (M := (ρ ^ m)⁻¹) (hfar_fin ρ)
      hf_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (hS.diff measurableSet_ball)] with t ht
    rw [Real.norm_of_nonneg (hf_nonneg t)]
    exact hfar_le ρ hρ t ht
  -- Step 3: with the ball integral, `f` is integrable on `S = (S ∩ B_ρ(0)) ∪ (S \ B_ρ(0))`.
  have hint : ∀ ρ : ℝ, 0 < ρ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) S := by
    intro ρ hρ
    have h : IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹)
        (S ∩ ball (0 : Eucl (m + 1)) ρ ∪ S \ ball (0 : Eucl (m + 1)) ρ) :=
      ((Submission.rpn_pe_inv_norm_pow_ball m ρ hρ).1.mono_set inter_subset_right).union
        (hfar_int ρ hρ)
    rwa [inter_union_sdiff] at h
  refine ⟨hint 1 one_pos, ?_⟩
  set ω := (volume (ball (0 : Eucl (m + 1)) 1)).toReal
  set L := (volume S).toReal
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hL_nonneg : 0 ≤ L := ENNReal.toReal_nonneg
  rcases hL_nonneg.eq_or_lt with hL0 | hL_pos
  · -- Step 4: if `Lⁿ(S) = 0`, both sides vanish.
    have hS0 : volume S = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 hL0.symm).resolve_right hSfin
    rw [Measure.restrict_eq_zero.2 hS0, integral_zero_measure, ← hL0,
      Real.zero_rpow (by positivity), mul_zero]
  · -- Step 5: the radius `ρ = (L / ω) ^ (1/(m+1))`, so that `L = ω ρ ^ (m + 1)`.
    set p : ℝ := 1 / ((m : ℝ) + 1) with hp
    set ρ : ℝ := (L / ω) ^ p with hρ
    have hLω : 0 < L / ω := div_pos hL_pos hω_pos
    have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hLω p
    have hL_eq : L = ω * ρ ^ (m + 1) := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hLω.le,
        show p * ((m + 1 : ℕ) : ℝ) = 1 by rw [hp]; push_cast; field_simp, Real.rpow_one]
      field_simp
    obtain ⟨hball_int, hball_eq⟩ := Submission.rpn_pe_inv_norm_pow_ball m ρ hρ_pos
    -- Step 6: split `∫_S f` along `B_ρ(0)`.
    rw [← integral_inter_add_sdiff (measurableSet_ball : MeasurableSet (ball (0 : Eucl (m + 1)) ρ))
      (hint ρ hρ_pos)]
    -- Step 7: the near part is at most `∫_{B_ρ(0)} f = (m + 1) ω ρ`.
    have hnear : ∫ t in S ∩ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ ≤ ((m : ℝ) + 1) * ω * ρ := by
      rw [← hball_eq]
      exact setIntegral_mono_set hball_int (ae_of_all _ hf_nonneg)
        (ae_of_all _ fun t ht => ht.2)
    -- Step 8: the far part is at most `Lⁿ(S \ B_ρ(0)) (ρ ^ m)⁻¹ ≤ L (ρ ^ m)⁻¹ = ω ρ`.
    have hfar : ∫ t in S \ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ ≤ ω * ρ := by
      calc ∫ t in S \ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹
          ≤ ∫ _ in S \ ball (0 : Eucl (m + 1)) ρ, (ρ ^ m)⁻¹ :=
            setIntegral_mono_on (hfar_int ρ hρ_pos) (integrableOn_const (hfar_fin ρ))
              (hS.diff measurableSet_ball) (hfar_le ρ hρ_pos)
        _ = volume.real (S \ ball (0 : Eucl (m + 1)) ρ) * (ρ ^ m)⁻¹ := by
            rw [setIntegral_const, smul_eq_mul]
        _ ≤ L * (ρ ^ m)⁻¹ := by
            gcongr
            exact measureReal_mono sdiff_subset hSfin
        _ = ω * ρ := by
            rw [hL_eq, pow_succ]
            field_simp
    -- Steps 9–10: the sum is `(m + 2) ω ρ = (m + 2) ω ^ (m/(m+1)) L ^ (1/(m+1))`.
    have hωρ : ω * ρ = ω ^ ((m : ℝ) / ((m : ℝ) + 1)) * L ^ p := by
      rw [hρ, Real.div_rpow hL_pos.le hω_pos.le,
        show (m : ℝ) / ((m : ℝ) + 1) = 1 - p by rw [hp]; field_simp; ring,
        Real.rpow_sub hω_pos, Real.rpow_one]
      ring
    calc _ ≤ ((m : ℝ) + 1) * ω * ρ + ω * ρ := add_le_add hnear hfar
      _ = ((m : ℝ) + 2) * (ω * ρ) := by ring
      _ = ((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) * L ^ p := by
        rw [hωρ, mul_assoc]
/-- The kernels `K(w) = w_j / (c|w|^{m+1})` on `ℝ^{m+1}` are locally integrable. This is Step 2 of
the potential estimate (Gilbarg–Trudinger §7.8) that replaces the BV argument of Simon Ch. 6,
Remark 2.35 in the proof of 8.1; there `c = nωₙ`. With `x / 0 = 0`, `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹`
everywhere, and `(|w|^m)⁻¹` is integrable on every ball about `0`
(`Submission.rpn_pe_inv_norm_pow_ball`). -/
theorem Submission.rpn_pe_kernel_locallyIntegrable : ∀ (m : ℕ) (j : Fin (m + 1)) (c : ℝ), LocallyIntegrable (fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1))) := by
  intro m j c
  -- Step 1: `K` is Borel measurable.
  have hmeas : Measurable fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1)) := by fun_prop
  -- Step 2: `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹`. If `c = 0` or `w = 0` the left side is `0`; otherwise
  -- `|w_j| ≤ |w|`.
  have hbound : ∀ t : Eucl (m + 1), ‖t j / (c * ‖t‖ ^ (m + 1))‖ ≤ |c|⁻¹ * (‖t‖ ^ m)⁻¹ := by
    intro t
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [PiLp.zero_apply, zero_div, norm_zero]
      positivity
    have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht
    rw [norm_div, norm_mul, norm_pow, norm_norm, Real.norm_eq_abs c]
    calc ‖t j‖ / (|c| * ‖t‖ ^ (m + 1)) ≤ ‖t‖ / (|c| * ‖t‖ ^ (m + 1)) := by
          gcongr
          exact PiLp.norm_apply_le t j
      _ = |c|⁻¹ * (‖t‖ ^ m)⁻¹ := by
          field_simp
          ring
  -- Step 3: around `x` use the ball `B_{|x|+1}(0)`, where `(|w|^m)⁻¹` is integrable.
  intro x
  refine ⟨ball (0 : Eucl (m + 1)) (‖x‖ + 1), isOpen_ball.mem_nhds (by simp), ?_⟩
  exact ((Submission.rpn_pe_inv_norm_pow_ball m (‖x‖ + 1) (by positivity)).1.const_mul |c|⁻¹).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ hbound)
/-- Convolution of a locally integrable kernel with a `C^∞` compactly supported function:
`ψ(y) = ∫ K(t) a(y - t) dt` is `C^∞`, and for all `y, v`, `t ↦ K(t) Da(y - t)v` is integrable with
`Dψ(y)v = ∫ K(t) Da(y - t)v dt`.  Here `ψ = K ⋆ a` for the pairing `lsmul ℝ ℝ`, so
`HasCompactSupport.contDiff_convolution_right` gives smoothness, `convolutionExists_right`
applied to the continuous compactly supported `z ↦ Da(z)v` gives integrability, and
`hasFDerivAt_convolution_right` with `convolution_precompR_apply` gives the derivative. -/
theorem Submission.rpn_pe_convolution_contDiff_fderiv :
    ∀ (n : ℕ) (K a : Eucl n → ℝ), LocallyIntegrable K → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a →
      HasCompactSupport a → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t, K t * a (y - t)) ∧
      ∀ y v : Eucl n, Integrable (fun t => K t * fderiv ℝ a (y - t) v) ∧
        fderiv ℝ (fun y => ∫ t, K t * a (y - t)) y v = ∫ t, K t * fderiv ℝ a (y - t) v := by
  intro n K a hK ha hsupp
  -- `ψ = K ⋆ a` for the scalar multiplication pairing (`convolution_lsmul`).
  have hψ : (fun y => ∫ t, K t * a (y - t)) =
      convolution K a (ContinuousLinearMap.lsmul ℝ ℝ) volume := rfl
  -- `a` is `C¹`, so `Da` is continuous.
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast le_top)
  have hDa : Continuous (fderiv ℝ a) := ha.continuous_fderiv (by simp)
  refine ⟨hψ ▸ hsupp.contDiff_convolution_right _ hK ha, fun y v => ⟨?_, ?_⟩⟩
  · -- `z ↦ Da(z)v` is continuous with compact support, so the convolution integrand is integrable.
    exact (hsupp.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hK (hDa.clm_apply continuous_const) y
  · -- `Dψ(y) = (K ⋆[precompR] Da)(y)`, evaluated at `v` by `convolution_precompR_apply`.
    rw [hψ, (hsupp.hasFDerivAt_convolution_right _ hK ha1 y).fderiv,
      convolution_precompR_apply _ hK (hsupp.fderiv (𝕜 := ℝ)) hDa]
    rfl
/-- The fundamental theorem of calculus along a ray: for `a` of class `C¹` with compact support
and `θ ≠ 0`, `∫_{(0,∞)} Da(y - rθ)θ dr = a(y)`.  The function `h(r) = a(y - rθ)` is `C¹` with
`h'(r) = -Da(y - rθ)θ`.  It has compact support because `r ↦ y - rθ` is a closed embedding.
So `HasCompactSupport.integral_Ioi_deriv_eq` gives `∫_{(0,∞)} h' = -h(0) = -a(y)`. -/
theorem Submission.rpn_pe_ray_ftc :
    ∀ (n : ℕ) (a : Eucl n → ℝ), ContDiff ℝ 1 a → HasCompactSupport a → ∀ y θ : Eucl n, θ ≠ 0 →
      ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • θ) θ = a y := by
  intro n a ha hsupp y θ hθ
  -- `h(r) = a(y - rθ)` is `C¹` and compactly supported (the line is a closed embedding as `θ ≠ 0`).
  have hh : ContDiff ℝ 1 (fun r : ℝ => a (y - r • θ)) :=
    ha.comp (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have hhsupp : HasCompactSupport (fun r : ℝ => a (y - r • θ)) :=
    hsupp.comp_isClosedEmbedding
      ((Homeomorph.subLeft y).isClosedEmbedding.comp (isClosedEmbedding_smul_left hθ))
  -- Chain rule: `h'(r) = Da(y - rθ)(-θ)`.
  have hderiv : ∀ r : ℝ, deriv (fun r : ℝ => a (y - r • θ)) r = -fderiv ℝ a (y - r • θ) θ := by
    intro r
    have hline : HasDerivAt (fun r : ℝ => y - r • θ) (-θ) r := by
      simpa using ((hasDerivAt_id r).smul_const θ).const_sub y
    exact (((ha.differentiable one_ne_zero) (y - r • θ)).hasFDerivAt.comp_hasDerivAt r
      hline).deriv.trans (map_neg _ _)
  -- FTC on `(0, ∞)`: `∫_{(0,∞)} h' = -h(0) = -a(y)`.
  have key := HasCompactSupport.integral_Ioi_deriv_eq hh hhsupp 0
  simp_rw [hderiv, integral_neg, zero_smul, sub_zero] at key
  exact neg_injective key

/-- **Representation formula (Gilbarg–Trudinger, §7.8, proof of Lemma 7.14).**  For `n = m + 1`,
`ω = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)`, the kernels `K_j(t) = t_j / (n ω |t|ⁿ)` satisfy
`∑_j ∫ K_j(t) ∂_j a(y - t) dt = a(y)`.  Expanding `t` in the standard basis, the sum is `∫ G` with
`G(t) = Da(y - t) t / (n ω |t|ⁿ)`.  In polar coordinates `r^m G(rθ) = Da(y - rθ) θ / (n ω)`, so
each ray integral is `a(y) / (n ω)` (fundamental theorem of calculus along the ray), and the unit
sphere has measure `n ω`. -/
theorem Submission.rpn_pe_kernel_representation : ∀ (m : ℕ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ y : Eucl (m + 1), ∑ j : Fin (m + 1), ∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) = a y := by
  intro m a ha hca y
  -- Step 1: `ω = Lⁿ(B₁(0)) ∈ (0, ∞)`, so `c = (m + 1) ω > 0`.
  set ω : ℝ := (volume (ball (0 : Eucl (m + 1)) 1)).toReal with hω
  set c : ℝ := ((m : ℝ) + 1) * ω with hc
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hc_pos : 0 < c := by positivity
  -- Step 2: `K_j` is locally integrable, so `t ↦ K_j(t) ∂_j a(y - t)` is integrable.
  have hint : ∀ j : Fin (m + 1), Integrable fun t : Eucl (m + 1) =>
      t j / (c * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) := fun j =>
    ((Submission.rpn_pe_convolution_contDiff_fderiv (m + 1) _ a
      (Submission.rpn_pe_kernel_locallyIntegrable m j c) ha hca).2 y _).1
  -- Step 3: move the sum inside the integral.
  rw [← integral_finsetSum _ fun j _ => hint j]
  -- Step 4: `Λ v = ∑_j v_j Λ e_j`, so `∑_j K_j(t) ∂_j a(y - t) = G(t)`.
  have hexp : ∀ (Λ : Eucl (m + 1) →L[ℝ] ℝ) (v : Eucl (m + 1)),
      Λ v = ∑ j : Fin (m + 1), v j * Λ (EuclideanSpace.single j (1 : ℝ)) := by
    intro Λ v
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  set G : Eucl (m + 1) → ℝ := fun t => fderiv ℝ a (y - t) t / (c * ‖t‖ ^ (m + 1)) with hG
  have hsum : (fun t : Eucl (m + 1) => ∑ j : Fin (m + 1),
      t j / (c * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ))) = G := by
    funext t
    simp only [hG]
    rw [hexp (fderiv ℝ a (y - t)) t, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- Step 5: `G` is integrable and the left side is `∫ G`.
  have hG_int : Integrable G := by
    rw [← hsum]
    exact integrable_finsetSum _ fun j _ => hint j
  rw [hsum]
  -- Step 6: polar coordinates.
  rw [Submission.rpn_pe_integral_eq_polar m G hG_int]
  -- Step 7: for `|θ| = 1` and `r > 0`, `r^m G(rθ) = Da(y - rθ) θ / c`; integrate along the ray.
  have hray : ∀ θ : sphere (0 : Eucl (m + 1)) 1,
      ∫ r in Ioi (0 : ℝ), r ^ m * G (r • (θ : Eucl (m + 1))) = a y / c := by
    intro θ
    calc ∫ r in Ioi (0 : ℝ), r ^ m * G (r • (θ : Eucl (m + 1)))
        = ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • (θ : Eucl (m + 1))) θ / c := by
          refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
          simp only [hG]
          rw [norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_of_nonneg hr.le, map_smul,
            smul_eq_mul]
          field_simp
          ring
      _ = (∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • (θ : Eucl (m + 1))) θ) / c := integral_div c _
      _ = a y / c := by
          rw [Submission.rpn_pe_ray_ftc (m + 1) a (ha.of_le (by norm_cast)) hca y θ
            (ne_zero_of_mem_unit_sphere θ)]
  -- Step 8: the inner integral is the constant `a(y) / c`, and `σ(S) = (m + 1) ω = c`.
  rw [integral_congr_ae (Eventually.of_forall hray), integral_const, smul_eq_mul,
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, measureReal_def, ← hω,
    show ((m + 1 : ℕ) : ℝ) * ω = c by rw [hc]; push_cast; ring, mul_div_cancel₀ _ hc_pos.ne']

/-- Sup bound for the kernel potentials (Step 5 of the potential estimate).  With
`ω = Lⁿ(B₁(0))`, `c = (m + 1) ω` and `K_j(t) = t_j / (c |t|^{m+1})`, every compactly supported
`a` with `|a| ≤ M` satisfies `|∫ K_j(t) a(y - t) dt| ≤ C M Lⁿ(spt a)^{1/(m+1)}` with
`C = (m + 2) ω^{m/(m+1)} / c`.  Proof: `|K_j(t) a(y - t)| ≤ (M / c) 1_{S_y}(t) |t|^{-m}` on
`S_y = {t : y - t ∈ spt a}`, a translate of `spt a`; integrate and apply
`rpn_pe_inv_norm_pow_set_bound` to `S_y`.  No measurability of `a` is needed. -/
theorem Submission.rpn_pe_kernel_sup_bound : ∀ m : ℕ, ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ (j : Fin (m + 1)) (y : Eucl (m + 1)), |∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * a (y - t)| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro m
  set ω : ℝ := (volume (ball (0 : Eucl (m + 1)) 1)).toReal
  set c : ℝ := ((m : ℝ) + 1) * ω
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Eucl (m + 1)) one_pos).ne'
      measure_ball_lt_top.ne
  have hc_pos : 0 < c := mul_pos (by positivity) hω_pos
  refine ⟨((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) / c, ?_⟩
  intro a ha M hM j y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- The translated support `S_y = {t : y - t ∈ spt a}` has the measure of `spt a`.
  set S : Set (Eucl (m + 1)) := tsupport a
  set Sy : Set (Eucl (m + 1)) := (fun t => y - t) ⁻¹' S
  have hSy_meas : MeasurableSet Sy :=
    ((isClosed_tsupport a).preimage (continuous_const.sub continuous_id)).measurableSet
  have hvol : volume Sy = volume S :=
    (Measure.measurePreserving_sub_left volume y).measure_preimage
      (isClosed_tsupport a).measurableSet.nullMeasurableSet
  have hSy_fin : volume Sy ≠ ⊤ := by
    rw [hvol]
    exact (IsCompact.measure_lt_top ha).ne
  obtain ⟨hint, hbound⟩ := Submission.rpn_pe_inv_norm_pow_set_bound m Sy hSy_meas hSy_fin
  rw [hvol] at hbound
  -- Pointwise domination by `(M / c) 1_{S_y}(t) |t|^{-m}`.
  have hg_int : Integrable (fun t => M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t) :=
    ((integrable_indicator_iff hSy_meas).2 hint).const_mul (M / c)
  have hdom : ∀ t : Eucl (m + 1), ‖t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)‖ ≤
      M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t := by
    intro t
    by_cases ht : t ∈ Sy
    · rw [indicator_of_mem ht, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hK : |t j / (c * ‖t‖ ^ (m + 1))| ≤ (‖t‖ ^ m)⁻¹ / c := by
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * ‖t‖ ^ (m + 1))]
        rcases (norm_nonneg t).eq_or_lt with h0 | hpos
        · rw [← h0, zero_pow (Nat.succ_ne_zero m), mul_zero, div_zero]
          positivity
        · rw [div_le_iff₀ (by positivity)]
          calc |t j| = ‖t j‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖t‖ := PiLp.norm_apply_le t j
            _ = (‖t‖ ^ m)⁻¹ / c * (c * ‖t‖ ^ (m + 1)) := by
              field_simp
              ring
      calc |t j / (c * ‖t‖ ^ (m + 1))| * |a (y - t)| ≤ (‖t‖ ^ m)⁻¹ / c * M :=
            mul_le_mul hK (hM _) (abs_nonneg _) (by positivity)
        _ = M / c * (‖t‖ ^ m)⁻¹ := by ring
    · have hyt : y - t ∉ tsupport a := ht
      rw [indicator_of_notMem ht, image_eq_zero_of_notMem_tsupport hyt]
      simp
  calc |∫ t, t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)|
      = ‖∫ t, t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t :=
        norm_integral_le_of_norm_le hg_int (Eventually.of_forall hdom)
    _ = M / c * ∫ t in Sy, (‖t‖ ^ m)⁻¹ := by
        rw [integral_const_mul, integral_indicator hSy_meas]
    _ ≤ M / c * (((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) *
          (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hbound (div_nonneg hM0 hc_pos.le)
    _ = ((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) / c * M *
          (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
        ring

/-- **Potential estimate (replaces Simon Ch. 6, Remark 2.35; Gilbarg–Trudinger, Lemma 7.14 and
§7.8).**  For `n = m + 1`, `ω_n = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)` with `|a| ≤ M`, the potentials
`ψ_j(y) = ∫ K_j(t) a(y - t) dt` of the kernels `K_j(t) = t_j / (n ω_n |t|ⁿ)` are `C^∞`, satisfy
`∑_j ∂_j ψ_j = a` and `|ψ_j| ≤ C M Lⁿ(spt a)^{1/n}` with `C` depending only on `m`.  The kernels
are locally integrable, so `ψ_j` is smooth with `∂_k ψ_j = K_j ⋆ ∂_k a`; summing `∂_j ψ_j` over
`j` gives `a` by the representation formula, and the bound is the kernel sup estimate. -/
theorem Submission.rpn_potential_estimate : ∀ m : ℕ, ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∃ ψ : Fin (m + 1) → Eucl (m + 1) → ℝ, (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ j)) ∧ (∀ y, ∑ j : Fin (m + 1), fderiv ℝ (ψ j) y (EuclideanSpace.single j (1 : ℝ)) = a y) ∧ ∀ j y, |ψ j y| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  have hli := @Submission.rpn_pe_kernel_locallyIntegrable
  have hconv := @Submission.rpn_pe_convolution_contDiff_fderiv
  have hrep := @Submission.rpn_pe_kernel_representation
  have hsup := @Submission.rpn_pe_kernel_sup_bound
  intro m
  -- Step 1: the constant `C` of the kernel sup bound, chosen before `a` and `M`.
  obtain ⟨C, hC⟩ := hsup m
  refine ⟨C, fun a ha hca M hM => ?_⟩
  -- Steps 2–3: `K_j(t) = t_j / (n ω_n |t|ⁿ)` is locally integrable, so `ψ_j = K_j ⋆ a` is `C^∞`
  -- and `Dψ_j(y) v = ∫ K_j(t) Da(y - t) v dt`.
  have hψ := fun j : Fin (m + 1) => hconv (m + 1)
    (fun t : Eucl (m + 1) =>
      t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1))) a
    (hli m j (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal)) ha hca
  -- Step 5: `|ψ_j(y)| ≤ C M Lⁿ(spt a)^{1/n}` is the kernel sup bound.
  refine ⟨fun j y => ∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal *
      ‖t‖ ^ (m + 1)) * a (y - t), fun j => (hψ j).1, fun y => ?_, fun j y => hC a hca M hM j y⟩
  -- Step 4: `∑_j ∂_j ψ_j(y) = ∑_j ∫ K_j(t) ∂_j a(y - t) dt = a(y)` (representation formula).
  rw [← hrep m a ha hca y]
  exact Finset.sum_congr rfl fun j _ => ((hψ j).2 y (EuclideanSpace.single j 1)).2
/-- The wedge `γ ∧ β₀ ∧ ⋯ ∧ β_{m-1}` is linear in its first factor `γ`. -/
theorem Submission.rpn_pfd_wedge_cons_isLinearMap :
    ∀ (P m : ℕ) (β : Fin m → (Eucl P →L[ℝ] ℝ)), IsLinearMap ℝ (fun γ : Eucl P →L[ℝ] ℝ =>
      wedgeCovectors (m + 1) (Fin.cons γ β : Fin (m + 1) → (Eucl P →L[ℝ] ℝ))) := by
  intro P m β
  -- Unfolding, `wedgeCovectors (m + 1) (Fin.cons γ β)` is
  -- `alternatizeUncurryFin (γ.smulRight (wedgeCovectors m β))`; `alternatizeUncurryFin` is
  -- linear, so it remains to see that `γ ↦ γ.smulRight (wedgeCovectors m β)` is linear.
  constructor
  · intro γ δ
    simp only [wedgeCovectors, Fin.cons_zero, Fin.tail_cons]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFin_add]
    congr 1
    ext v w
    simp [add_smul]
  · intro c γ
    simp only [wedgeCovectors, Fin.cons_zero, Fin.tail_cons]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    congr 1
    ext v w
    simp [mul_smul]
/-- Sign lemma for wedges of one-covectors: moving the factor `l j` to the front costs
`(-1)^j`, while putting another factor `l i` (`i ≠ j`) in front repeats a factor. -/
theorem Submission.rpn_pfd_wedge_cons_succAbove_sign :
    ∀ (P m : ℕ) (l : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) (j : Fin (m + 1)),
      wedgeCovectors (m + 1) (Fin.cons (l j) (fun k => l (j.succAbove k)) :
          Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = ((-1 : ℝ) ^ (j : ℕ)) • wedgeCovectors (m + 1) l ∧
        ∀ i : Fin (m + 1), i ≠ j → wedgeCovectors (m + 1) (Fin.cons (l i)
          (fun k => l (j.succAbove k)) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = 0 := by
  intro P m l j
  refine ⟨?_, fun i hij => ?_⟩
  · -- `Fin.cons (l j) (l ∘ j.succAbove) = l ∘ σ` with `σ = (cycleRange j)⁻¹`, so its value
    -- matrix is that of `l` with rows permuted by `σ`.
    have hσ : (Fin.cons (l j) (fun k => l (j.succAbove k)) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) =
        fun a => l (j.cycleRange.symm a) := by
      funext a
      cases a using Fin.cases <;> simp
    ext v
    have h := Matrix.det_permute j.cycleRange.symm (Matrix.of fun a b => l a (v b))
    rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange] at h
    push_cast at h
    rw [hσ, ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_det,
      wedgeCovectors_apply_det, smul_eq_mul, ← h]
    rfl
  · -- `i = j.succAbove k` for some `k`, so rows `0` and `k.succ` of the value matrix coincide.
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    ext v
    rw [wedgeCovectors_apply_det, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    refine Matrix.det_zero_of_row_eq (Fin.succ_ne_zero k).symm ?_
    funext b
    simp [hk]
/-- `d(∑ⱼ gⱼ θⱼ) = ∑ⱼ dgⱼ ∧ θⱼ` for constant covectors `θⱼ = βⱼ,₀ ∧ ⋯ ∧ βⱼ,ₘ₋₁` (Simon Ch. 6,
(1.11), p. 134: `d(a dx^α) = da ∧ dx^α`, with general constant one-covectors `βⱼ` in place of the
coordinate differentials).  `extDeriv Φ x = Alt (DΦ(x))` only needs `gⱼ` differentiable at `x`. -/
theorem Submission.rpn_pfd_extDeriv_sum_smul_wedge : ∀ (P m : ℕ) (ι : Type) [Fintype ι] (g : ι → Eucl P → ℝ) (β : ι → Fin m → (Eucl P →L[ℝ] ℝ)) (x : Eucl P), (∀ j, DifferentiableAt ℝ (g j) x) → extDeriv (fun z => ∑ j : ι, g j z • wedgeCovectors m (β j)) x = ∑ j : ι, wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ (g j) x) (β j) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) := by
  intro P m ι _ g β x hg
  -- `z ↦ ∑ⱼ gⱼ(z) • θⱼ` has derivative `∑ⱼ Dgⱼ(x).smulRight θⱼ` at `x`.
  have hD : HasFDerivAt (fun z => ∑ j : ι, g j z • wedgeCovectors m (β j))
      (∑ j : ι, (fderiv ℝ (g j) x).smulRight (wedgeCovectors m (β j))) x :=
    HasFDerivAt.fun_sum fun j _ => (hg j).hasFDerivAt.smul_const (wedgeCovectors m (β j))
  -- `extDeriv Φ x = Alt (fderiv Φ x)`, and `Alt` is linear, so it commutes with the sum.
  rw [extDeriv, hD.fderiv, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum]
  -- Each term is the successor case of `wedgeCovectors` at `Fin.cons (Dgⱼ(x)) βⱼ`.
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, wedgeCovectors, Fin.cons_zero,
    Fin.tail_cons]

/-- One term of the divergence identity of Simon Ch. 6, 2.35 (`dω = div a dx¹ ∧ ⋯ ∧ dxⁿ`),
pulled back by a linear `L : ℝ^P → ℝ^{m+1}`: for `λᵢ = yⁱ ∘ L` and `ℓ ∈ (ℝ^{m+1})*`,
`(ℓ ∘ L) ∧ λ₀ ∧ ⋯ ∧ λ̂ⱼ ∧ ⋯ ∧ λₘ = (-1)ʲ ℓ(eⱼ) λ₀ ∧ ⋯ ∧ λₘ`.  Expand `ℓ ∘ L = ∑ᵢ ℓ(eᵢ) λᵢ`; the
wedge is linear in its first factor, and by the sign lemma only the term `i = j` survives. -/
theorem Submission.rpn_pfd_wedge_cons_comp_succAbove :
    ∀ (P m : ℕ) (L : Eucl P →L[ℝ] Eucl (m + 1)) (ℓ : Eucl (m + 1) →L[ℝ] ℝ) (j : Fin (m + 1)),
      wedgeCovectors (m + 1) (Fin.cons (ℓ.comp L)
          (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) :
          Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) =
        ((-1 : ℝ) ^ (j : ℕ) * ℓ (EuclideanSpace.single j (1 : ℝ))) •
          wedgeCovectors (m + 1)
            (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) := by
  intro P m L ℓ j
  -- `λᵢ = yⁱ ∘ L`; `Λ γ = γ ∧ λ_{j.succAbove 0} ∧ ⋯ ∧ λ_{j.succAbove (m - 1)}` is linear in `γ`.
  let lam : Fin (m + 1) → (Eucl P →L[ℝ] ℝ) := fun i =>
    (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L
  let Λ := IsLinearMap.mk' _
    (Submission.rpn_pfd_wedge_cons_isLinearMap P m fun k => lam (j.succAbove k))
  have hΛ : ∀ γ, Λ γ = wedgeCovectors (m + 1)
      (Fin.cons γ fun k => lam (j.succAbove k) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) :=
    fun _ => rfl
  -- `ℓ ∘ L = ∑ᵢ ℓ(eᵢ) λᵢ`: expand `L v` in the standard basis of `ℝ^{m+1}`.
  have hexp : ℓ.comp L = ∑ i, ℓ (EuclideanSpace.single i (1 : ℝ)) • lam i := by
    ext v
    have hv := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr (L v)
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hv
    conv_lhs => rw [ContinuousLinearMap.comp_apply, ← hv]
    simp [lam, mul_comm]
  -- Sign lemma for `l = λ`: the term `i = j` is `(-1)ʲ λ₀ ∧ ⋯ ∧ λₘ`, the others vanish.
  obtain ⟨hj, hne⟩ := Submission.rpn_pfd_wedge_cons_succAbove_sign P m lam j
  calc wedgeCovectors (m + 1)
        (Fin.cons (ℓ.comp L) fun k => lam (j.succAbove k) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ))
      = Λ (∑ i, ℓ (EuclideanSpace.single i (1 : ℝ)) • lam i) := by rw [hΛ, hexp]
    _ = ∑ i, ℓ (EuclideanSpace.single i (1 : ℝ)) • Λ (lam i) := by
        simp only [map_sum, map_smul]
    _ = ℓ (EuclideanSpace.single j (1 : ℝ)) • Λ (lam j) := by
        refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h)
        rw [hΛ, hne i hij, smul_zero]
    _ = ((-1 : ℝ) ^ (j : ℕ) * ℓ (EuclideanSpace.single j (1 : ℝ))) •
          wedgeCovectors (m + 1) lam := by
        rw [hΛ, hj, smul_smul, mul_comm]

/-- Exterior derivative of the pulled-back potential form (Simon Ch. 6, 1.14 and the divergence
identity `dψ̂ = (div ψ) dy` of Remark 2.35).  For `λᵢ = yⁱ ∘ L`, `θⱼ = λ₀ ∧ ⋯ ∧ λ̂ⱼ ∧ ⋯ ∧ λₘ` and
`Φ(z) = ∑ⱼ (-1)ʲ f(z) ψⱼ(Lz) θⱼ`,
`dΦ(x) = f(x) (∑ⱼ ∂ⱼψⱼ(Lx)) λ₀ ∧ ⋯ ∧ λₘ + ∑ⱼ (-1)ʲ ψⱼ(Lx) Df(x) ∧ θⱼ`. -/
theorem Submission.rpn_extDeriv_potential_form :
    ∀ (P m : ℕ) (L : Eucl P →L[ℝ] Eucl (m + 1)) (f : Eucl P → ℝ)
      (ψ : Fin (m + 1) → Eucl (m + 1) → ℝ) (x : Eucl P),
      DifferentiableAt ℝ f x → (∀ j, DifferentiableAt ℝ (ψ j) (L x)) →
      extDeriv (fun z => ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) •
          wedgeCovectors m
            (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L)) x =
        (f x * ∑ j : Fin (m + 1), fderiv ℝ (ψ j) (L x) (EuclideanSpace.single j (1 : ℝ))) •
            wedgeCovectors (m + 1)
              (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) +
          ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) •
            wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ f x)
              (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) :
              Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) := by
  intro P m L f ψ x hf hψ
  -- Chain and product rules: `gⱼ(z) = (-1)ʲ f(z) ψⱼ(Lz)` has derivative
  -- `(-1)ʲ (f(x) Dψⱼ(Lx) ∘ L + ψⱼ(Lx) Df(x))` at `x`.
  have hg : ∀ j : Fin (m + 1), HasFDerivAt (fun z => (-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z)))
      ((-1 : ℝ) ^ (j : ℕ) • (f x • (fderiv ℝ (ψ j) (L x)).comp L + ψ j (L x) • fderiv ℝ f x))
      x :=
    fun j => (hf.hasFDerivAt.fun_mul ((hψ j).hasFDerivAt.comp x L.hasFDerivAt)).const_mul _
  -- `dΦ(x) = ∑ⱼ Dgⱼ(x) ∧ θⱼ`; compare with the right side term by term.
  rw [Submission.rpn_pfd_extDeriv_sum_smul_wedge P m (Fin (m + 1))
      (fun j z => (-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z)))
      (fun j i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) x
      fun j => (hg j).differentiableAt,
    Finset.mul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- The wedge is linear in its first factor, the `Dψⱼ(Lx) ∘ L` part is
  -- `(-1)ʲ ∂ⱼψⱼ(Lx) λ₀ ∧ ⋯ ∧ λₘ`, and `(-1)ʲ (-1)ʲ = 1`.
  have hlin := Submission.rpn_pfd_wedge_cons_isLinearMap P m
    fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L
  have hsq : (-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [(hg j).fderiv, hlin.map_smul, hlin.map_add, hlin.map_smul, hlin.map_smul,
    Submission.rpn_pfd_wedge_cons_comp_succAbove P m L (fderiv ℝ (ψ j) (L x)) j, smul_add,
    smul_smul, smul_smul, smul_smul]
  congr 2
  linear_combination (f x * fderiv ℝ (ψ j) (L x) (EuclideanSpace.single j (1 : ℝ))) * hsq
/-- The Euclidean coefficient norm of an `n`-covector on `ℝ^P` is at most `√(P^n)` times its
operator norm: each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` (`b` the standard
orthonormal basis) is bounded by `‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.fiw_ims_sc_covectorNorm_le_opNorm :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
  intro P n α
  -- Every coefficient is at most `‖α‖`, since the standard basis vectors are unit vectors.
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
        -- The sum has `P ^ n` terms, each at most `‖α‖ ^ 2`.
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

/-- Mass estimate with the operator norm: if `M_W(T) ≤ B` and `ω` is supported in `W` with
`‖ω(x)‖ ≤ C` everywhere (operator norm), then `|T(ω)| ≤ P^n · B · C`, because the Euclidean
coefficient norm is at most `√(P^n) · ‖·‖ ≤ P^n · ‖·‖`. -/
theorem Submission.rpn_abs_apply_le_opNorm_mul_massOn :
    ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B C : ℝ),
      0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, ‖(ω : DifferentialForm (Eucl P) n) x‖ ≤ C) →
      |T ω| ≤ (P : ℝ) ^ n * B * C := by
  intro P n U W T ω B C hB hM hW hC
  -- `C ≥ 0`, by evaluating the pointwise bound at `0`.
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- `√(P^n) ≤ P^n`, since `P^n` is a natural number.
  have hsqrt : Real.sqrt ((P : ℝ) ^ n) ≤ (P : ℝ) ^ n := by
    rw [Real.sqrt_le_self_iff]
    rcases (P ^ n).eq_zero_or_pos with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  -- Hence the Euclidean coefficient norm of `ω(x)` is at most `P^n · C`.
  have hE : ∀ x,
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ (P : ℝ) ^ n * C := by
    intro x
    calc covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)
        ≤ Real.sqrt ((P : ℝ) ^ n) * ‖(ω : DifferentialForm (Eucl P) n) x‖ :=
          Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
      _ ≤ (P : ℝ) ^ n * C := mul_le_mul hsqrt (hC x) (norm_nonneg _) (by positivity)
  calc |T ω| ≤ B * ((P : ℝ) ^ n * C) :=
        Submission.cmb_abs_apply_le_of_massOn_le P n U W T ω B _ hB hM hW hE
    _ = (P : ℝ) ^ n * B * C := by ring

/-- Simon Ch. 6, the estimate behind Lemma 2.36 (via Remark 2.35), for a linear map
`L : ℝ^P → ℝⁿ`, `n = m + 1`: if `M_W(T), M_W(∂T) < ∞` and `f` is a smooth compactly supported
cutoff with `tsupport f ⊆ W`, then every test form `φ = f · (a ∘ L) · L^*dy` satisfies
`|T(φ)| ≤ C · M · Lⁿ(spt a)^{1/n}` whenever `|a| ≤ M`, with `C` independent of `a`, `M`, `φ`.

Write `a = ∑ⱼ ∂ⱼψⱼ` with `|ψⱼ| ≤ R = C₁ M Lⁿ(spt a)^{1/n}` (`rpn_potential_estimate`) and
`Φ = ∑ⱼ (-1)ʲ f (ψⱼ ∘ L) θⱼ`, `θⱼ = ⋀_{i ≠ j} (yⁱ ∘ L)`.  Then `dΦ = φ + Ξ` with
`Ξ = ∑ⱼ (-1)ʲ (ψⱼ ∘ L) Df ∧ θⱼ` (`rpn_extDeriv_potential_form`), so `T(φ) = ∂T(Φ) - T(Ξ)`,
and both terms are bounded through `M_W(∂T)` and `M_W(T)`
(`rpn_abs_apply_le_opNorm_mul_massOn`). -/
theorem Submission.rpn_pullback_top_form_bound :
    ∀ (P m : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)), W ⊆ U →
      T.massOn W < ∞ → T.boundary.massOn W < ∞ → ∀ f : Eucl P → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ W →
      ∀ L : Eucl P →L[ℝ] Eucl (m + 1), ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ,
      (∀ y, |a y| ≤ M) → ∀ φ : TestFormOn U (m + 1),
      (∀ x, (φ : DifferentialForm (Eucl P) (m + 1)) x = (f x * a (L x)) •
        wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) →
      |T φ| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro P m U W T hWU hT hbT f hf hfc hfW L
  /- Step 1: constants depending only on `T`, `W`, `f` and `L`. -/
  obtain ⟨C₁, hC₁⟩ := Submission.rpn_potential_estimate m
  -- `θⱼ = ⋀_{i ≠ j} (yⁱ ∘ L)`, an `m`-covector.
  let θ : Fin (m + 1) → Covector (Eucl P) m := fun j =>
    wedgeCovectors m (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L)
  -- `ηⱼ(x) = Df(x) ∧ θⱼ = Λⱼ(Df(x))`, where `Λⱼ γ = Alt(γ ⊗ θⱼ)` is continuous linear.
  let η : Fin (m + 1) → DifferentialForm (Eucl P) (m + 1) := fun j x =>
    wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ f x)
      (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) :
        Fin (m + 1) → (Eucl P →L[ℝ] ℝ))
  have hηΛ : ∀ j, η j = fun x =>
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        ((ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)).flip (θ j)))
          (fderiv ℝ f x) := by
    intro j
    funext x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    rfl
  -- `Df` is continuous and vanishes off `tsupport f`, so each `ηⱼ` is continuous with compact
  -- support, hence bounded by some `Hⱼ`.
  have hηbdd : ∀ j, ∃ H : ℝ, ∀ x, ‖η j x‖ ≤ H := by
    intro j
    rw [hηΛ j]
    exact (ContinuousLinearMap.continuous _).comp (hf.continuous_fderiv (by simp))
      |>.bounded_above_of_compact_support ((hfc.fderiv ℝ).comp_left (map_zero _))
  choose H hH using hηbdd
  have hηzero : ∀ j x, x ∉ tsupport f → η j x = 0 := by
    intro j x hx
    rw [hηΛ j]
    simp only [fderiv_of_notMem_tsupport ℝ hx, map_zero]
  -- `F₀ = sup |f|`, `B₀ = M_W(T)`, `B₁ = M_W(∂T)`.
  obtain ⟨F₀, hF₀⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hF₀nn : 0 ≤ F₀ := (norm_nonneg _).trans (hF₀ 0)
  set B₀ : ℝ := (T.massOn W).toReal
  set B₁ : ℝ := (T.boundary.massOn W).toReal
  have hTB₀ : T.massOn W ≤ ENNReal.ofReal B₀ := (ENNReal.ofReal_toReal hT.ne).ge
  have hbTB₁ : T.boundary.massOn W ≤ ENNReal.ofReal B₁ := (ENNReal.ofReal_toReal hbT.ne).ge
  refine ⟨C₁ * ((P : ℝ) ^ m * B₁ * F₀ * ∑ j, ‖θ j‖ + (P : ℝ) ^ (m + 1) * B₀ * ∑ j, H j), ?_⟩
  intro a ha hac M hM φ hφ
  /- Step 2: the potential `ψ`, with `∑ⱼ ∂ⱼψⱼ = a` and `|ψⱼ| ≤ R`. -/
  obtain ⟨ψ, hψ, hdiv, hψb⟩ := hC₁ a ha hac M hM
  set R : ℝ := C₁ * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) with hR
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hψb 0 0)
  /- Step 3: the test `m`-form `Φ = ∑ⱼ (-1)ʲ f (ψⱼ ∘ L) θⱼ`, supported in `tsupport f ⊆ W`. -/
  let Φf : DifferentialForm (Eucl P) m := fun z =>
    ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) • θ j
  have hΦsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φf :=
    ContDiff.sum fun j _ =>
      (contDiff_const.mul (hf.mul ((hψ j).comp L.contDiff))).smul contDiff_const
  have hΦsupp : Function.support Φf ⊆ Function.support f := by
    intro z hz
    rw [Function.mem_support] at hz ⊢
    contrapose! hz
    simp [Φf, hz]
  have hΦts : tsupport Φf ⊆ tsupport f := closure_mono hΦsupp
  let Φ : TestFormOn U m := ⟨Φf, ⟨⟨hΦsmooth, hfc.mono hΦsupp⟩, hΦts.trans (hfW.trans hWU)⟩⟩
  /- Step 4: `dΦ = φ + Ξ` with `Ξ = ∑ⱼ (-1)ʲ (ψⱼ ∘ L) ηⱼ`. -/
  let dΦ : TestFormOn U (m + 1) := exteriorDerivativeTestOn U m Φ
  have hdΦ : ∀ x, (dΦ : DifferentialForm (Eucl P) (m + 1)) x =
      (f x * a (L x)) •
        wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) • η j x := by
    intro x
    have hd := Submission.rpn_extDeriv_potential_form P m L f ψ x
      (hf.differentiable (by simp) x) (fun j => (hψ j).differentiable (by simp) (L x))
    rw [hdiv (L x)] at hd
    exact hd
  let Ξ : TestFormOn U (m + 1) := dΦ - φ
  have hΞ : ∀ x, (Ξ : DifferentialForm (Eucl P) (m + 1)) x =
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) • η j x := by
    intro x
    change (dΦ : DifferentialForm (Eucl P) (m + 1)) x -
      (φ : DifferentialForm (Eucl P) (m + 1)) x = _
    rw [hdΦ x, hφ x, add_sub_cancel_left]
  -- `Ξ` vanishes off `tsupport f`, because every `ηⱼ` does.
  have hΞts : tsupport (Ξ : DifferentialForm (Eucl P) (m + 1)) ⊆ W := by
    refine (closure_minimal (fun x hx => ?_) (isClosed_tsupport f)).trans hfW
    by_contra hxf
    exact hx (by rw [hΞ x]; simp [hηzero _ x hxf])
  /- Step 5: `T(φ) = T(dΦ) - T(Ξ) = ∂T(Φ) - T(Ξ)`. -/
  have hsplit : T φ = T.boundary Φ - T Ξ := by
    rw [GeometricCurrentOn.boundary_apply]
    change T.toCurrent φ = T.toCurrent dΦ - T.toCurrent (dΦ - φ)
    rw [T.toCurrent.map_sub dΦ φ]
    ring
  /- Step 6: pointwise bounds `‖Φ‖ ≤ F₀ R ∑ⱼ ‖θⱼ‖` and `‖Ξ‖ ≤ R ∑ⱼ Hⱼ`. -/
  have hΦbound : ∀ z, ‖(Φ : DifferentialForm (Eucl P) m) z‖ ≤ F₀ * R * ∑ j, ‖θ j‖ := by
    intro z
    change ‖∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) • θ j‖ ≤ _
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul]
    have hfz : |f z| ≤ F₀ := by simpa only [Real.norm_eq_abs] using hF₀ z
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hfz (hψb j (L z)) (abs_nonneg _) hF₀nn) (norm_nonneg _)
  have hΞbound : ∀ x, ‖(Ξ : DifferentialForm (Eucl P) (m + 1)) x‖ ≤ R * ∑ j, H j := by
    intro x
    rw [hΞ x, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact mul_le_mul (hψb j (L x)) (hH j x) (norm_nonneg _) hR0
  /- Step 7: the mass bounds for `∂T(Φ)` and `T(Ξ)`. -/
  have hbΦ := Submission.rpn_abs_apply_le_opNorm_mul_massOn P m U W T.boundary Φ B₁
    (F₀ * R * ∑ j, ‖θ j‖) ENNReal.toReal_nonneg hbTB₁ (hΦts.trans hfW) hΦbound
  have hTΞ := Submission.rpn_abs_apply_le_opNorm_mul_massOn P (m + 1) U W T Ξ B₀
    (R * ∑ j, H j) ENNReal.toReal_nonneg hTB₀ hΞts hΞbound
  /- Step 8: conclusion. -/
  rw [hsplit]
  calc |T.boundary Φ - T Ξ| ≤ |T.boundary Φ| + |T Ξ| := abs_sub _ _
    _ ≤ (P : ℝ) ^ m * B₁ * (F₀ * R * ∑ j, ‖θ j‖) + (P : ℝ) ^ (m + 1) * B₀ * (R * ∑ j, H j) :=
      add_le_add hbΦ hTΞ
    _ = C₁ * ((P : ℝ) ^ m * B₁ * F₀ * ∑ j, ‖θ j‖ + (P : ℝ) ^ (m + 1) * B₀ * ∑ j, H j) * M *
        ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
      rw [hR]
      ring
/-- **Kronecker duality of coordinate wedges (Simon Ch. 6, 1.1–1.2).**  For an increasing
multi-index `I`, `dx^I = dx^{I₁} ∧ ⋯ ∧ dx^{Iₙ}` has coordinate `1` at `I` and `0` at every
increasing `J ≠ I`: by (1.1), `dx^I(e_{J₁}, …, e_{Jₙ}) = det [I i = J j]`.  For `J = I` this matrix
is the identity, as `I` is injective.  For `J ≠ I` some `I i ∉ range J` (otherwise the finite
ranges, of equal cardinality, coincide, and increasing enumerations with equal ranges are equal),
so row `i` vanishes. -/
theorem Submission.polyhedral_approx_pairing_wedge_kronecker : ∀ (P n : ℕ) (I : SimonMultiIndex n P), euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) I = 1 ∧ ∀ J : SimonMultiIndex n P, J ≠ I → euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J = 0 := by
  intro P n I
  -- (1)–(2) The coordinate at `J` is the determinant of the matrix `[I i = J j]`.
  have hdet : ∀ J : SimonMultiIndex n P,
      euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        Matrix.det (Matrix.of fun i j => if I i = J j then (1 : ℝ) else 0) := by
    intro J
    rw [euclideanCovectorCoordinate, wedgeCovectors_apply_det]
    congr 1
    ext i j
    simp [PiLp.single_apply]
  refine ⟨?_, fun J hJ => ?_⟩
  · -- (3) For `J = I` the matrix is the identity, as `I` is injective.
    have hone : (Matrix.of fun i j => if I i = I j then (1 : ℝ) else 0) = 1 := by
      ext i j
      simp [Matrix.one_apply, I.injective.eq_iff]
    rw [hdet, hone, Matrix.det_one]
  · -- (4) Some `I i` lies outside `range J`: otherwise `range I = range J` and `I = J`.
    obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
      by_contra h
      have hsub : range I ⊆ range J := by
        rintro _ ⟨i, rfl⟩
        by_contra hi
        exact h ⟨i, fun j hj => hi ⟨j, hj.symm⟩⟩
      have hrange : range I = range J :=
        Set.eq_of_subset_of_ncard_le hsub (by
          rw [Set.ncard_range_of_injective I.injective, Set.ncard_range_of_injective J.injective])
      exact hJ (OrderEmbedding.range_inj_of_wellFoundedLT.mp hrange).symm
    -- (5) Row `i` of the matrix vanishes, so the determinant is `0`.
    rw [hdet]
    exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [hi j]
/-- An `n`-covector on `ℝ^P` is determined by its coordinates on increasing multi-indices
(Simon Ch. 6, 1.2): if `α(e_{I(0)}, …, e_{I(n-1)}) = β(e_{I(0)}, …, e_{I(n-1)})` for every
increasing `I`, then `α = β`.  Alternating maps agreeing on injective tuples of basis vectors are
equal; sorting an injective tuple `v` by `σ = Tuple.sort v` gives the increasing `I = v ∘ σ`, and
`e_v = e_I ∘ σ⁻¹` gives `γ(e_v) = sign(σ⁻¹) γ(e_I)` for `γ = α, β`. -/
theorem Submission.polyhedral_approx_pairing_covector_ext : ∀ (P n : ℕ) (α β : Covector (Eucl P) n), (∀ I : SimonMultiIndex n P, euclideanCovectorCoordinate α I = euclideanCovectorCoordinate β I) → α = β := by
  intro P n α β h
  -- Reduce to the underlying alternating maps on injective tuples of standard basis vectors.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  -- Sorting `v` by `σ = Tuple.sort v` gives the increasing multi-index `I = v ∘ σ`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  let I : SimonMultiIndex n P := OrderEmbedding.ofStrictMono _ hsm
  -- `e_v = e_I ∘ σ⁻¹`.
  have he : (fun i => EuclideanSpace.single (v i) (1 : ℝ)) =
      (fun j => EuclideanSpace.single (I j) (1 : ℝ)) ∘ ⇑(Tuple.sort v)⁻¹ := by
    funext i
    simp [I]
  -- `γ(e_v) = sign(σ⁻¹) • γ(e_I)` for `γ = α, β`, and `α(e_I) = β(e_I)`.
  rw [he, AlternatingMap.map_perm, AlternatingMap.map_perm]
  congr 1
  exact h I

/-- **Rotated coordinate expansion of a covector (Simon Ch. 6, 1.2; Lemma 2.36, Remark 2.37(2)).**
For a linear isometry `Q` of `ℝ^P`, every `n`-covector expands as
`φ = ∑_α φ(Q⁻¹e_{α(0)}, …, Q⁻¹e_{α(n-1)}) Q^*dx^α`, where
`Q^*dx^α = (dx^{α(0)} ∘ Q) ∧ ⋯ ∧ (dx^{α(n-1)} ∘ Q)`.  The pull-back `φ' = (Q⁻¹)^*φ` has
coordinates `φ'(e_α) = φ(Q⁻¹e_α)`, so the Kronecker property `dx^α(e_I) = δ_{αI}` gives
`φ' = ∑_α φ'(e_α) dx^α` on increasing coordinates, hence everywhere.  Pulling back by `Q` gives
`φ = Q^*φ'`. -/
theorem Submission.rpn_covector_rotated_expansion : ∀ (P n : ℕ) (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (φ : Covector (Eucl P) n), φ = ∑ α : SimonMultiIndex n P, φ (fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ))) • wedgeCovectors n (fun i => (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P)) := by
  intro P n Q φ
  -- (2) Standard expansion of `φ' = (Q⁻¹)^*φ`: both sides have the same increasing coordinates.
  have hexp : covectorPullback n (Q.symm : Eucl P →L[ℝ] Eucl P) φ =
      ∑ α : SimonMultiIndex n P, φ (fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ))) •
        wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) := by
    refine Submission.polyhedral_approx_pairing_covector_ext P n _ _ fun I => ?_
    -- (1) By the Kronecker property only the `α = I` summand survives.
    have hK := Submission.polyhedral_approx_pairing_wedge_kronecker P n
    simp only [euclideanCovectorCoordinate] at hK ⊢
    rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single I]
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, (hK I).1, mul_one]
      rfl
    · intro α _ hα
      rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, (hK α).2 I (Ne.symm hα), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  -- (3) `φ = Q^*φ'` since `Q⁻¹ Q = id`, and `Q^*dx^α = wedgeCovectors n (fun i => dx^{α(i)} ∘ Q)`.
  have hφ : φ = covectorPullback n (Q : Eucl P →L[ℝ] Eucl P)
      (covectorPullback n (Q.symm : Eucl P →L[ℝ] Eucl P) φ) := by
    ext v
    simp [Function.comp_def]
  conv_lhs => rw [hφ, hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, covectorPullback_wedgeCovectors]
/-- Smooth cutoffs for a compact Lebesgue-null set (Simon Ch. 6, proof of Lemma 2.36, display
(2)): if `F ⊆ ℝ^N` is compact with `Lᴺ(F) = 0` and `δ > 0`, there is a `C^∞` function
`b : ℝ^N → [0, 1]` with compact support, `b = 1` on `F` and `Lᴺ(spt b) ≤ δ`.  By outer regularity
pick an open `G ⊇ F` with `Lᴺ(G) < δ`, then an open `V` with `F ⊆ V ⊆ closure V ⊆ G` and
`closure V` compact, and a smooth Urysohn function equal to `1` on `F` and to `0` off `V`. -/
theorem Submission.rpn_null_compact_cutoff : ∀ (N : ℕ) (F : Set (Eucl N)), IsCompact F → (volume : Measure (Eucl N)) F = 0 → ∀ δ : ℝ, 0 < δ → ∃ b : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∈ F, b y = 1) ∧ ((volume : Measure (Eucl N)) (tsupport b)).toReal ≤ δ := by
  intro N F hF hF0 δ hδ
  -- Step 1: outer regularity of `Lᴺ` gives an open `G ⊇ F` with `Lᴺ(G) < δ`.
  obtain ⟨G, hFG, hGo, hGδ⟩ := Set.exists_isOpen_lt_of_lt F (ENNReal.ofReal δ)
    (by rw [hF0]; exact ENNReal.ofReal_pos.mpr hδ)
  -- Step 2: an open `V` with `F ⊆ V`, `closure V ⊆ G` and `closure V` compact.
  obtain ⟨V, hVo, hFV, hVG, hVc⟩ := exists_open_between_and_isCompact_closure hF hGo hFG
  -- Step 3: a smooth Urysohn function `b : ℝ^N → [0, 1]` with `b = 0` off `V` and `b = 1` on `F`.
  obtain ⟨b, hb0, hb1, hb01⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ (Eucl N)) (n := ⊤) hVo.isClosed_compl hF.isClosed
    (Set.disjoint_compl_left_iff_subset.mpr hFV)
  -- Step 4: `spt b ⊆ closure V ⊆ G`, so `spt b` is compact and `Lᴺ(spt b) ≤ Lᴺ(G) < δ`.
  have hsupp : tsupport b ⊆ closure V :=
    closure_mono fun x hx => by_contra fun hxV => hx (hb0 hxV)
  refine ⟨b, contMDiff_iff_contDiff.mp b.contMDiff,
    hVc.of_isClosed_subset (isClosed_tsupport _) hsupp, fun y => hb01 y, fun y hy => hb1 hy, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hδ.le ((measure_mono (hsupp.trans hVG)).trans hGδ.le)

/-- **Mass off a compact set with null projections (Simon Ch. 6, proof of Lemma 2.36, displays
(1)–(3), run for `Q_#T` as in Remark 2.37(2)).**  Let `T ∈ 𝒟ₙ(U)` (`n = m + 1`) have
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and be represented by `(μ, ξ)` with
`Σ_β ξ(x)(dx^β)² = 1` for `μ`-a.e. `x`.  If `K` is compact and `Lⁿ(π_α(K)) = 0` for every
`α ∈ I(n, P)`, where `π_α(x) = ((Qx)_{α(0)}, …, (Qx)_{α(m)})`, then `M_W(T) ≤ C μ(W∖K)` for every
open `W ⊂⊂ U`.  Each admissible `ω` expands as `Σ_α ω_α θ_α` with `ω_α = ω(Q⁻¹e_α)` and
`θ_α = Q^*dx^α` (the top form of `π_α`).  For each `α` the cut-off estimate gives
`|T(ω_α θ_α)| ≤ c_α c'_α μ(W∖K)`, with `c_α = Σ_β |dx^β(Q⁻¹e_α)|` and `c'_α = Σ_β |θ_α(e_β)|`. -/
theorem Submission.rpn_massOn_le_mul_measure_diff : ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ (μ : Measure (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ ξ → (∀ᵐ x ∂μ, ∑ β : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) β) ^ 2 = 1) → ∀ (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (K : Set (Eucl P)), IsCompact K → (∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' K) = 0) → ∃ C : ℝ≥0, ∀ W, CompactlyContainedOpen W U → T.massOn W ≤ (C : ℝ≥0∞) * μ (W \ K) := by
  intro P m U T hmass μ ξ hrep hξ Q K hK hnull
  classical
  -- Step 1: `π_α x = ((Qx)_{α(0)}, …, (Qx)_{α(m)})` is linear and `y^i ∘ π_α = x^{α(i)} ∘ Q`, so
  -- the top form of `π_α` is `θ_α = Q^*dx^α`; `π_α(K)` is the null set of the hypothesis.
  let π : SimonMultiIndex (m + 1) P → Eucl P →L[ℝ] Eucl (m + 1) := fun α =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P))
  let θ : SimonMultiIndex (m + 1) P → Covector (Eucl P) (m + 1) := fun α =>
    wedgeCovectors (m + 1)
      (fun i => (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P))
  have hθπ : ∀ α, wedgeCovectors (m + 1)
      (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp (π α)) = θ α := fun α =>
    congrArg (wedgeCovectors (m + 1)) (funext fun i => ContinuousLinearMap.ext fun x => rfl)
  have hπK : ∀ α, (volume : Measure (Eucl (m + 1))) (π α '' K) = 0 := hnull
  -- Step 4: the constants `c_α = Σ_β |dx^β(e^Q_α)|` and `c'_α = Σ_β |θ_α(e_β)|`.
  let e : SimonMultiIndex (m + 1) P → Fin (m + 1) → Eucl P := fun α i =>
    Q.symm (EuclideanSpace.single (α i) (1 : ℝ))
  let c : SimonMultiIndex (m + 1) P → ℝ := fun α => ∑ β : SimonMultiIndex (m + 1) P,
    |wedgeCovectors (m + 1) (fun j => (EuclideanSpace.proj (β j) : Eucl P →L[ℝ] ℝ)) (e α)|
  let c' : SimonMultiIndex (m + 1) P → ℝ := fun α => ∑ β : SimonMultiIndex (m + 1) P,
    |euclideanCovectorCoordinate (θ α) β|
  have hc : ∀ α, 0 ≤ c α := fun α => Finset.sum_nonneg fun β _ => abs_nonneg _
  have hc' : ∀ α, 0 ≤ c' α := fun α => Finset.sum_nonneg fun β _ => abs_nonneg _
  set S : ℝ := ∑ α : SimonMultiIndex (m + 1) P, c α * c' α
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun α _ => mul_nonneg (hc α) (hc' α)
  -- Step 4(b): `|ξ(x)(θ_α)| ≤ c'_α` for `μ`-a.e. `x`.
  have hξθ : ∀ α, ∀ᵐ x ∂μ, |ξ x (θ α)| ≤ c' α := fun α =>
    hξ.mono fun x hx => Submission.rpn_moc_abs_nvector_apply_le P (m + 1) (ξ x) (θ α) hx
  refine ⟨Real.toNNReal (1 + S), fun W hW => ?_⟩
  -- Step 5: `W ⊆ U` with finite masses; the case `μ(W∖K) = ∞` is trivial.
  have hW' : IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U := hW
  have hWU : W ⊆ U := subset_closure.trans hW'.2.2
  have hfin := ENNReal.add_lt_top.mp (hmass W hW)
  have hC0 : ((Real.toNNReal (1 + S) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
    linarith
  by_cases hD : μ (W \ K) = ∞
  · rw [hD, ENNReal.mul_top hC0]
    exact le_top
  apply sSup_le
  rintro _ ⟨ω, hω, rfl⟩
  -- Step 6: `ω_α(x) = ω(x)(e^Q_α)` is smooth, supported in `W` and bounded by `c_α`.
  let f : SimonMultiIndex (m + 1) P → Eucl P → ℝ := fun α x =>
    (ω : DifferentialForm (Eucl P) (m + 1)) x (e α)
  have hf_smooth : ∀ α, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f α) := fun α =>
    (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (e α)).contDiff.comp ω.property.1.1
  have hf_cs : ∀ α, HasCompactSupport (f α) := fun α =>
    ω.property.1.2.comp_left (g := fun φ : Covector (Eucl P) (m + 1) => φ (e α)) rfl
  have hf_supp : ∀ α, tsupport (f α) ⊆ W := fun α =>
    (tsupport_comp_subset (g := fun φ : Covector (Eucl P) (m + 1) => φ (e α)) rfl _).trans hω.1
  have hf_bound : ∀ α x, |f α x| ≤ c α := fun α x =>
    (Submission.rpn_moc_abs_covector_apply_le P (m + 1) _ (e α)).trans
      (mul_le_of_le_one_right (hc α) (hω.2 x))
  -- The test forms `ζ_α = ω_α θ_α`; by the rotated expansion `ω = Σ_α ζ_α`.
  choose ζ hζ using fun α => Submission.rpn_moc_exists_testForm_smul P (m + 1) U (f α) (θ α)
    (hf_smooth α) (hf_cs α) ((hf_supp α).trans hWU)
  have hωζ : ω = ∑ α, ζ α := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [hζ]
    exact Submission.rpn_covector_rotated_expansion P (m + 1) Q _
  -- Step 7: `|T(ζ_α)| ≤ c_α c'_α μ(W∖K)`, cutting off near `π_α(K)` (printed display (2)).
  have hTζ : ∀ α, |T (ζ α)| ≤ c α * c' α * (μ (W \ K)).toReal := fun α =>
    Submission.rpn_moc_abs_apply_top_form_le P m U W K T μ ξ hrep hW'.1 hWU hK hD (π α) (f α)
      (c α) (c' α) (hf_smooth α) (hf_cs α) (hf_supp α) (hf_bound α)
      (by rw [hθπ α]; exact hξθ α)
      (Submission.rpn_pullback_top_form_bound P m U W T hWU hfin.1 hfin.2 (f α) (hf_smooth α)
        (hf_cs α) (hf_supp α) (π α))
      (fun δ hδ => Submission.rpn_null_compact_cutoff (m + 1) (π α '' K)
        (hK.image (π α).continuous) (hπK α) δ hδ)
      (ζ α) (fun x => by rw [hθπ α]; exact hζ α x)
  -- Step 8: sum over `α` (printed display (3)).
  have hTω : T ω ≤ (1 + S) * (μ (W \ K)).toReal := by
    calc T ω = ∑ α, T (ζ α) := by rw [hωζ]; exact map_sum T.toCurrent ζ Finset.univ
      _ ≤ ∑ α, |T (ζ α)| := Finset.sum_le_sum fun α _ => le_abs_self _
      _ ≤ ∑ α, c α * c' α * (μ (W \ K)).toReal := Finset.sum_le_sum fun α _ => hTζ α
      _ = S * (μ (W \ K)).toReal := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + S) * (μ (W \ K)).toReal :=
        mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
  calc ENNReal.ofReal (T ω) ≤ ENNReal.ofReal ((1 + S) * (μ (W \ K)).toReal) :=
        ENNReal.ofReal_le_ofReal hTω
    _ = ((Real.toNNReal (1 + S) : ℝ≥0) : ℝ≥0∞) * μ (W \ K) := by
      rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hD]
      rfl

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
