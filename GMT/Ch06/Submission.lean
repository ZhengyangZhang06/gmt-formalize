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

/-- Simon Ch. 6, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of an integer multiplicity
`Y = τ(M, θ, ξ) ∈ 𝒟ₖ(U)` to an open `W ⊆ U` is the integer multiplicity current
`τ(M ∩ W, θ, ξ)`. -/
theorem Submission.br_restrictDomain_isIntegerMultiplicity :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U), IsOpen W →
      ∀ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y →
        IsIntegerMultiplicity (Y.restrictDomain hWU) := by
  rintro P k U W hWU hW Y ⟨M, θ, ξ, hM, hθ, hY⟩
  have hMW : NullMeasurableSet (M ∩ W) (μHE[k] : Measure (Eucl P)) :=
    hM.nullMeasurableSet.inter hW.measurableSet.nullMeasurableSet
  refine ⟨M ∩ W, θ, ξ,
    { subset := inter_subset_right
      nullMeasurableSet := hMW
      countablyRectifiable := hM.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => hM.pos x hx.1
      integrableOn := fun K hK hKW =>
        (hM.integrableOn K hK (hKW.trans hWU)).mono_set fun y hy => ⟨hy.1.1, hy.2⟩
      aestronglyMeasurable := hM.aestronglyMeasurable.mono_set inter_subset_left
      orients := ?_ }, fun x hx => hθ x hx.1, fun ω => ?_⟩
  · -- `M` and `M ∩ W` agree in the open set `W`, so they have the same weighted approximate
    -- tangent spaces at points of `W`.
    have hnull : symmDiff M (M ∩ W) ∩ W = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_symmDiff, mem_empty_iff_false, iff_false]
      tauto
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hM.orients,
      ae_restrict_mem₀ hMW] with x hxM hx
    obtain ⟨τ, hτ, hTx, hξ⟩ := hxM
    exact ⟨τ, hτ, Submission.br_weightedTangent_congr P k M (M ∩ W) θ θ x W hW hx.2
      (by rw [hnull, measure_empty]) (ae_of_all _ fun _ => rfl) rfl _ hTx, hξ⟩
  · -- A test form on `W` vanishes off `W`, so the integrals over `M` and `M ∩ W` agree.
    have h0 : ∀ x, x ∉ W → θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (ω.property.2 h), map_zero, mul_zero]
    rw [GeometricCurrentOn.restrictDomain_apply, hY]
    simp only [tauAction, testFormOnInclusion_coe]
    rw [inter_comm M W, ← Measure.restrict_restrict hW.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero h0]
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
/-- Simon Ch. 6, 2.23 (p. 139), cut-off construction: if `f` is `C^∞` and proper on `A ⊆ U`, every
`ω ∈ 𝒟ʲ(V)` has a pull-back `η = ζ f^#ω ∈ 𝒟ʲ(U)` with `0 ≤ ζ ≤ 1`, `η = f^#ω` on an open
`N ⊇ A`, and `spt η ⊆ f⁻¹(spt ω)`. -/
theorem Submission.iwl_sp_exists_compatible_testForm :
    ∀ (P Q j : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (A : Set (Eucl P)) (f : Eucl P → Eucl Q),
      IsOpen U → A ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ A)) →
      ∀ ω : TestFormOn V j, ∃ (η : TestFormOn U j) (ζ : Eucl P → ℝ) (N : Set (Eucl P)),
        IsOpen N ∧ A ⊆ N ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
        (∀ x, (η : DifferentialForm (Eucl P) j) x =
          ζ x • ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap
            (fderiv ℝ f x)) ∧
        (∀ x ∈ N, (η : DifferentialForm (Eucl P) j) x =
          ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∧
        tsupport (η : DifferentialForm (Eucl P) j) ⊆
          f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) := by
  intro P Q j U V A f hU hAU hf hprop ω
  obtain ⟨⟨hωs, hωc⟩, hωV⟩ := ω.property
  have hωs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl Q) j) := hωs
  -- 1. `K = f⁻¹(spt ω) ∩ A` is compact, by properness.
  have hK : IsCompact (f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) ∩ A) :=
    hprop _ hωc.isCompact hωV
  set K := f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) ∩ A
  -- 2. A closed `δ`-thickening of `K` lies in `U`.
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU fun x hx => hAU hx.2
  -- 3. Smooth Urysohn: `support ζ = thickening δ K`, and `ζ = 1` exactly on `cthickening (δ/2) K`.
  obtain ⟨ζ, hζs, hζr, hζsupp, hζone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  have hζt : tsupport ζ ⊆ cthickening δ K := by
    rw [tsupport, hζsupp]
    exact closure_thickening_subset_cthickening δ K
  -- 4. The pull-back `p = f^# ω` is smooth, since `B ↦ B^#` is analytic.
  set p : DifferentialForm (Eucl P) j := fun x =>
    ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p := by
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin j) (F := ℝ)
          (fderiv ℝ f x)) :=
      (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff.comp hD
    exact hC.clm_apply (hωs'.comp hf)
  -- `p` vanishes wherever `ω ∘ f` does.
  have hp0 : ∀ x, f x ∉ tsupport (ω : DifferentialForm (Eucl Q) j) → p x = 0 := by
    intro x hx
    show ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x) = 0
    rw [image_eq_zero_of_notMem_tsupport hx,
      ← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, map_zero]
  -- 5. The test form `η = ζ p`.
  have hηs : IsSmoothForm (fun x => ζ x • p x) := hζs.smul hp
  have hηt : tsupport (fun x => ζ x • p x) ⊆ U :=
    (tsupport_smul_subset_left ζ p).trans (hζt.trans hδU)
  have hηc : HasCompactSupport (fun x => ζ x • p x) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_smul_subset_left ζ p).trans hζt)
  let η : TestFormOn U j := ⟨fun x => ζ x • p x, ⟨hηs, hηc⟩, hηt⟩
  refine ⟨η, ζ, thickening (δ / 2) K ∪ f ⁻¹' (tsupport (ω : DifferentialForm (Eucl Q) j))ᶜ,
    isOpen_thickening.union ((isClosed_tsupport _).isOpen_compl.preimage hf.continuous), ?_,
    fun x => hζr (mem_range_self x), fun x => rfl, ?_, ?_⟩
  · -- 7. `A ⊆ N`.
    intro x hx
    by_cases hfx : f x ∈ tsupport (ω : DifferentialForm (Eucl Q) j)
    · exact Or.inl (self_subset_thickening (half_pos hδ) K ⟨hfx, hx⟩)
    · exact Or.inr hfx
  · -- 8. `η = p` on `N`.
    rintro x (hx | hx)
    · have h1 : ζ x = 1 := (hζone x).1 (thickening_subset_cthickening _ _ hx)
      show ζ x • p x = p x
      rw [h1, one_smul]
    · show ζ x • p x = p x
      rw [hp0 x hx, smul_zero]
  · -- 6. `spt η ⊆ f⁻¹(spt ω)`, a closed set.
    refine closure_minimal ?_ ((isClosed_tsupport _).preimage hf.continuous)
    intro x hx
    by_contra hfx
    exact hx (show ζ x • p x = 0 by rw [hp0 x hfx, smul_zero])
/-- Simon Ch. 6, proof of 8.2 (p. 179), `p_# S̃_j` and display (10): if `p` is linear with
`‖p‖ ≤ 1` and proper on `F`, integer multiplicity `X_k ∈ 𝒟_{m+1}(U)` with `spt X_k ⊆ F` push
forward (by the smooth push-forward, `f := p`) to integer multiplicity `S_k ∈ 𝒟_{m+1}(V)` with
`S_k(ω) = X_k(p^#ω)`, `M_W(S_k) ≤ M(X_k)` and `M_W(∂S_k) ≤ M(∂X_k)`. -/
theorem Submission.ind_pi_pl_linear_pushforward_family :
    LipschitzPushforwardIntegerMultiplicity →
    (LipschitzPushforwardIntegerMultiplicity →
      ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
      ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q),
        IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V →
        (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) →
        ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧
          (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)),
            (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
              (η : DifferentialForm (Eucl P) (k + 1)) x =
                ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap
                  (fderiv ℝ f x)) →
            S ω = X η) ∧
          (∀ (ω : TestFormOn V k) (η : TestFormOn U k),
            (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
              (η : DifferentialForm (Eucl P) k) x =
                ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap
                  (fderiv ℝ f x)) →
            S.boundary ω = X.boundary η) ∧
          ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q),
            S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧
            S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) →
    ∀ (P Q m : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (F : Set (Eucl P))
      (p : Eucl P →L[ℝ] Eucl Q) (X : ℕ → GeometricCurrentOn U (m + 1)),
      IsOpen U → IsOpen V → ‖p‖ ≤ 1 → MapsTo p U V →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (p ⁻¹' K ∩ F) ∧ p ⁻¹' K ∩ F ⊆ U) →
      (∀ k, IsIntegerMultiplicity (X k)) → (∀ k, (X k).support ⊆ F) →
      ∃ S : ℕ → GeometricCurrentOn V (m + 1), (∀ k, IsIntegerMultiplicity (S k)) ∧
        (∀ (k : ℕ) (ω : TestFormOn V (m + 1)) (η : TestFormOn U (m + 1)),
          (∃ N : Set (Eucl P), IsOpen N ∧ (X k).support ⊆ N ∧ ∀ x ∈ N,
            (η : DifferentialForm (Eucl P) (m + 1)) x =
              ((ω : DifferentialForm (Eucl Q) (m + 1)) (p x)).compContinuousLinearMap p) →
          S k ω = X k η) ∧
        ∀ (k : ℕ) (W : Set (Eucl Q)),
          (S k).massOn W ≤ (X k).mass ∧ (S k).boundary.massOn W ≤ (X k).boundary.mass := by
  intro hLPF hSPF P Q m U V F p X hU hV hp hpUV hprop hX hXF
  -- 1. `p` is `C^∞` and `fderiv ℝ p x = p`, so `‖fderiv ℝ p x‖ ≤ 1`.
  have hpd : ∀ x, fderiv ℝ p x = p := fun x => p.fderiv
  have hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p := p.contDiff
  -- 2. `p` is proper on `spt X_k`: `p⁻¹(K) ∩ spt X_k = (p⁻¹(K) ∩ F) \ zeroRegion X_k`.
  have hpk : ∀ k, ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      IsCompact (p ⁻¹' K ∩ (X k).support) := by
    intro k K hK hKV
    obtain ⟨hKc, hKU⟩ := hprop K hK hKV
    have heq : p ⁻¹' K ∩ (X k).support = (p ⁻¹' K ∩ F) \ (X k).zeroRegion := by
      ext y
      constructor
      · rintro ⟨hy, hys⟩
        exact ⟨⟨hy, hXF k hys⟩, hys.2⟩
      · rintro ⟨hyF, hyZ⟩
        exact ⟨hyF.1, hKU hyF, hyZ⟩
    rw [heq]
    exact hKc.diff (X k).isOpen_zeroRegion
  -- 3. The smooth push-forward by `p` of each `X_k`; choose `S_k`.
  choose S hSi hSa _ hSm using fun k => hSPF hLPF P Q m U V hU hV (X k) p (hX k) hps hpUV (hpk k)
  refine ⟨S, hSi, ?_, ?_⟩
  · -- 4. `S_k(ω) = X_k(η)` when `η = p^#ω` near `spt X_k`, as `fderiv ℝ p x = p`.
    rintro k ω η ⟨N, hN, hXN, hη⟩
    exact hSa k ω η ⟨N, hN, hXN, fun x hx => by rw [hpd x]; exact hη x hx⟩
  · -- 5. The mass bounds at `c = 1`, then `M_{p⁻¹(W) ∩ U} ≤ M_U = M`.
    intro k W
    obtain ⟨hm, hbm⟩ := hSm k 1 zero_le_one (fun x => by rw [hpd x]; exact hp) W
    simp only [one_pow, ENNReal.ofReal_one, one_mul] at hm hbm
    exact ⟨hm.trans ((X k).massOn_mono inter_subset_right),
      hbm.trans ((X k).boundary.massOn_mono inter_subset_right)⟩
/-- Geometry of an orthonormal frame `τ` in `ℝ^P`: with `π y = ∑ ⟪τᵢ, y⟫ τᵢ`, `p y = (⟪τᵢ, y⟫)ᵢ`
and `d y = ‖y − π y‖`, Pythagoras gives `‖y‖² = ‖p y‖² + d(y)²`; hence `‖p‖ ≤ 1`, `d` is
`1`-Lipschitz, `p` inverts `a ↦ ∑ aᵢ τᵢ`, `d = 0` on `span τ`, the cylinder
`{‖p‖ < 1, d < 3/4}` lies in `closedBall 0 (5/4) ⊆ B₂(0)`, and `p⁻¹(K) ∩ {d ≤ γ}` is a compact
subset of it for compact `K ⊆ B₁(0)` and `γ < 3/4`. -/
theorem Submission.ind_pi_frame_geometry :
    ∀ (P n : ℕ) (τ : Fin n → Eucl P) (p : Eucl P →L[ℝ] Eucl n) (d : Eucl P → ℝ), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → LipschitzWith 1 d ∧ (∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2) ∧ ‖p‖ ≤ 1 ∧ (∀ a : Eucl n, p (∑ i, a i • τ i) = a) ∧ (∀ i, p (τ i) = EuclideanSpace.single i (1 : ℝ)) ∧ (∀ z ∈ Submodule.span ℝ (Set.range τ), d z = 0) ∧ CompactlyContainedOpen {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (ball (0 : Eucl P) 2) ∧ ∀ γ : ℝ, γ < 3 / 4 → ∀ K : Set (Eucl n), IsCompact K → K ⊆ ball (0 : Eucl n) 1 → IsCompact (p ⁻¹' K ∩ {y | d y ≤ γ}) ∧ p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} := by
  intro P n τ p d hτ hp hd
  -- The orthogonal projection `π y = ∑ ⟪τᵢ, y⟫ τᵢ` onto `span τ`, so `d y = ‖y − π y‖`.
  obtain ⟨π, hπ⟩ : ∃ π : Eucl P → Eucl P, ∀ y, π y = ∑ i, inner ℝ (τ i) y • τ i :=
    ⟨_, fun _ => rfl⟩
  have hdπ : ∀ y, d y = ‖y - π y‖ := fun y => by rw [hd, hπ]
  -- Step 1: `⟪τⱼ, π y⟫ = ⟪τⱼ, y⟫`.
  have h1 : ∀ y j, inner ℝ (τ j) (π y) = inner ℝ (τ j) y := fun y j => by
    rw [hπ]
    exact hτ.inner_right_fintype (fun i => inner ℝ (τ i) y) j
  have hπinner : ∀ y v, inner ℝ (π y) v = ∑ i, inner ℝ (τ i) y * inner ℝ (τ i) v := by
    intro y v
    rw [hπ, sum_inner]
    simp only [real_inner_smul_left]
  -- Step 2: `π y ⊥ y − π y`.
  have h2 : ∀ y, inner ℝ (π y) (y - π y) = 0 := by
    intro y
    rw [hπinner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sub_right, h1, sub_self, mul_zero]
  -- Step 3: `‖p y‖² = ‖π y‖² = ∑ ⟪τᵢ, y⟫²` and Pythagoras.
  have hpπ : ∀ y, ‖p y‖ ^ 2 = ‖π y‖ ^ 2 := by
    intro y
    rw [EuclideanSpace.real_norm_sq_eq, ← real_inner_self_eq_norm_sq, hπinner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, hp, sq]
  have hb : ∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2 := by
    intro y
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (h2 y)
    rw [add_sub_cancel] at h
    rw [hpπ, hdπ, sq, sq, sq, h]
  -- Step 4: `0 ≤ d y ≤ ‖y‖` and `‖p y‖ ≤ ‖y‖`.
  have hd0 : ∀ y, 0 ≤ d y := fun y => by rw [hdπ]; exact norm_nonneg _
  have hdle : ∀ y, d y ≤ ‖y‖ := by
    intro y
    have := hb y
    nlinarith [hd0 y, norm_nonneg y, sq_nonneg ‖p y‖]
  have hple : ∀ y, ‖p y‖ ≤ ‖y‖ := by
    intro y
    have := hb y
    nlinarith [norm_nonneg (p y), norm_nonneg y, sq_nonneg (d y)]
  -- Step 5: `π` is additive, so `d x ≤ d y + d (x − y) ≤ d y + dist x y`.
  have hπsub : ∀ x y, π (x - y) = π x - π y := by
    intro x y
    simp only [hπ, inner_sub_right, sub_smul, Finset.sum_sub_distrib]
  have hLip : LipschitzWith 1 d := by
    refine LipschitzWith.of_le_add fun x y => ?_
    have e : x - π x = (y - π y) + ((x - y) - π (x - y)) := by rw [hπsub]; abel
    calc d x = ‖(y - π y) + ((x - y) - π (x - y))‖ := by rw [hdπ, e]
      _ ≤ ‖y - π y‖ + ‖(x - y) - π (x - y)‖ := norm_add_le _ _
      _ = d y + d (x - y) := by rw [hdπ, hdπ]
      _ ≤ d y + ‖x - y‖ := by gcongr; exact hdle _
      _ = d y + dist x y := by rw [dist_eq_norm]
  -- The cylinder `{‖p‖ ≤ 1, d ≤ 3/4}` lies in `closedBall 0 (5/4)`.
  have hball : ∀ y, ‖p y‖ ≤ 1 → d y ≤ 3 / 4 → y ∈ closedBall (0 : Eucl P) (5 / 4) := by
    intro y hpy hdy
    rw [mem_closedBall_zero_iff]
    have h := hb y
    have hp0 := norm_nonneg (p y)
    have hd0' := hd0 y
    nlinarith [norm_nonneg y]
  refine ⟨hLip, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (c) `‖p‖ ≤ 1`.
  · exact p.opNorm_le_bound zero_le_one fun y => by rw [one_mul]; exact hple y
  -- (d) `p (∑ aᵢ τᵢ) = a`.
  · intro a
    ext j
    rw [hp]
    exact hτ.inner_right_fintype (fun i => a i) j
  -- (e) `p τᵢ = eᵢ`.
  · intro i
    ext j
    rw [hp, PiLp.single_apply, orthonormal_iff_ite.mp hτ j i]
  -- (f) `d = 0` on `span τ`.
  · intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
    have hc : ∀ i, inner ℝ (τ i) (∑ j, c j • τ j) = c i := fun i => hτ.inner_right_fintype c i
    rw [hd]
    simp only [hc, sub_self, norm_zero]
  -- (g) `{‖p‖ < 1, d < 3/4} ⊂⊂ B₂(0)`.
  · have hcl : closure {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ⊆ closedBall (0 : Eucl P) (5 / 4) := by
      refine (closure_minimal (t := {y : Eucl P | ‖p y‖ ≤ 1 ∧ d y ≤ 3 / 4})
        (fun y hy => ⟨hy.1.le, hy.2.le⟩) ?_).trans fun y hy => hball y hy.1 hy.2
      exact (isClosed_le p.continuous.norm continuous_const).inter
        (isClosed_le hLip.continuous continuous_const)
    refine ⟨?_, ?_, ?_⟩
    · exact (isOpen_lt p.continuous.norm continuous_const).inter
        (isOpen_lt hLip.continuous continuous_const)
    · exact (isCompact_closedBall (0 : Eucl P) (5 / 4)).of_isClosed_subset isClosed_closure hcl
    · exact hcl.trans (closedBall_subset_ball (by norm_num))
  -- (h) `p⁻¹(K) ∩ {d ≤ γ}` is compact and lies in the cylinder.
  · intro γ hγ K hK hKB
    have hsub : p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} := by
      intro y hy
      exact ⟨mem_ball_zero_iff.mp (hKB hy.1), lt_of_le_of_lt hy.2 hγ⟩
    refine ⟨?_, hsub⟩
    refine (isCompact_closedBall (0 : Eucl P) (5 / 4)).of_isClosed_subset ?_
      fun y hy => hball y (hsub hy).1.le (hsub hy).2.le
    exact (hK.isClosed.preimage p.continuous).inter (isClosed_le hLip.continuous continuous_const)
/-- Simon Ch. 6, proof of 8.2: for an orthonormal frame `τ₁, …, τₙ` of `Q = span τ ⊆ ℝ^P`, the
parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is a linear isometry `ℝⁿ → ℝ^P` with range `Q`, so it pushes
Lebesgue measure on `ℝⁿ` (`= Hⁿ`) forward to `Hⁿ ⌞ Q`.  As a closed, hence measurable, embedding
it gives `∫_Q h dHⁿ = ∫_{ℝⁿ} h(ι(a)) da` for every `h`, and `(Hⁿ ⌞ Q)(K) = Lⁿ(ι⁻¹ K) < ∞` for
compact `K`. -/
theorem Submission.ind_pi_span_integral :
    ∀ (P n : ℕ) (τ : Fin n → Eucl P), Orthonormal ℝ τ → (∀ h : Eucl P → ℝ, ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), h z ∂(μHE[n] : Measure (Eucl P)) = ∫ a : Eucl n, h (∑ i, a i • τ i)) ∧ ∀ K : Set (Eucl P), IsCompact K → ((μHE[n] : Measure (Eucl P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Eucl P))) K < ∞ := by
  intro P n τ hτ
  -- The parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is linear.
  let ι : Eucl n →ₗ[ℝ] Eucl P :=
    { toFun := fun a => ∑ i, a i • τ i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.smul_sum, smul_smul] }
  have hι : ∀ a : Eucl n, ι a = ∑ i, a i • τ i := fun a => rfl
  -- `ι` is an isometry: `‖ι a‖² = ∑ᵢ aᵢ² = ‖a‖²` by orthonormality.
  have hiso : Isometry ι := by
    refine AddMonoidHomClass.isometry_of_norm ι fun a => ?_
    have hsq : ‖ι a‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [hι, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  -- `range ι = span τ`.
  have hrange : Set.range ι = (Submodule.span ℝ (Set.range τ) : Set (Eucl P)) := by
    ext z
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨fun i => a i, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨WithLp.toLp 2 c, by simp [hι]⟩
  -- `ι` is a closed, hence measurable, embedding.
  have hemb : MeasurableEmbedding ι := hiso.isClosedEmbedding.measurableEmbedding
  -- `ι` pushes Lebesgue measure `= Hⁿ` on `ℝⁿ` forward to `Hⁿ ⌞ span τ`.
  have hmap : (volume : Measure (Eucl n)).map ι =
      (μHE[n] : Measure (Eucl P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Eucl P)) := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, hiso.map_euclideanHausdorffMeasure,
      hrange]
  refine ⟨fun h => ?_, fun K hK => ?_⟩
  · rw [← hmap, hemb.integral_map]
    rfl
  · rw [← hmap, hemb.map_apply]
    exact (hiso.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
/-- Simon Ch. 6, (2.7) (p. 136) for a constant `n`-vector: if `μ` is finite on compact sets and
`w ∈ Λₙ(ℝ^P)`, then `T(ω) = ∫ ⟨ω(x), w⟩ dμ(x)` defines a current `T ∈ 𝒟ₙ(U)` with
representation `(μ, w)`. -/
theorem Submission.ind_pi_constant_vector_current :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (w : NVector (Eucl P) n),
      (∀ K : Set (Eucl P), IsCompact K → μ K < ∞) →
      ∃ T : GeometricCurrentOn U n, IsMeasureRepresentation T μ (fun _ => w) := by
  intro P n U μ w hμ
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ K hK⟩
  -- `x ↦ ⟨ω(x), w⟩` is continuous with compact support (`w 0 = 0`), hence `μ`-integrable.
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => w ((ω : DifferentialForm (Eucl P) n) x)) μ := fun ω =>
    (w.continuous.comp ω.property.1.1.continuous).integrable_of_hasCompactSupport
      (ω.property.1.2.comp_left (map_zero w))
  -- The linear functional `L(ω) = ∫ ⟨ω, w⟩ dμ`.
  let L : CurrentOn U n :=
    { toFun := fun ω => ∫ x, w ((ω : DifferentialForm (Eucl P) n) x) ∂μ
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => ⟨hint ω, rfl⟩⟩
  -- Sequential continuity: the `ω_j` are supported in one compact `K` and `ω_j → 0` uniformly
  -- on `K`, so `|L(ω_j)| ≤ ‖w‖ · sup_K ‖ω_j‖ · μ(K) → 0`.
  obtain ⟨K, hK, -, hsupp, -, hderiv⟩ := hωs
  have hunif := Metric.tendstoUniformlyOn_iff.1 (hderiv 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hm : 0 ≤ μ.real K := measureReal_nonneg
  have hC : 0 < ‖w‖ * μ.real K + 1 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / (‖w‖ * μ.real K + 1)) (div_pos hε hC))
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_zero_right]
  change ‖∫ x, w ((ωs j : DifferentialForm (Eucl P) n) x) ∂μ‖ < ε
  -- The integrand vanishes off `K ⊇ tsupport ω_j`.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h), map_zero]]
  -- On `K`, `|⟨ω_j(x), w⟩| ≤ ‖w‖ ‖ω_j(x)‖ ≤ ‖w‖ · ε / (‖w‖ μ(K) + 1)`.
  have hbound : ∀ x ∈ K, ‖w ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
      ‖w‖ * (ε / (‖w‖ * μ.real K + 1)) := by
    intro x hx
    have h := (hN j hj x hx).le
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      Function.comp_apply, LinearIsometryEquiv.dist_map, ZeroMemClass.coe_zero, Pi.zero_apply,
      dist_zero_left] at h
    exact (w.le_opNorm _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg w))
  refine (norm_setIntegral_le_of_norm_le_const (hμ K hK) hbound).trans_lt ?_
  rw [show ‖w‖ * (ε / (‖w‖ * μ.real K + 1)) * μ.real K =
      ε * (‖w‖ * μ.real K / (‖w‖ * μ.real K + 1)) by ring]
  exact mul_lt_of_lt_one_right hε ((div_lt_one hC).2 (lt_add_one _))
/-- **Restriction of an integer multiplicity current to an open set** (Simon Ch. 6, (2.9) and 3.1,
pp. 136, 146; used for the restrictions to open sets in the proof of 8.2, pp. 176–179).  If
`X = τ(M, θ, ξ)` is integer multiplicity and `R = X ⌞ A` with `A` open, then
`R = τ(M ∩ A, θ, ξ)` is integer multiplicity.  With smooth cutoffs `φ_j → 1_A` pointwise,
`X(φ_j ω)` tends both to `∫_A ⟨ω, v⟩ dμ = R(ω)` and to `τ(M ∩ A, θ, ξ)(ω)` (dominated
convergence); and the weighted tangent planes of `(M, θ)` at `x ∈ A` are those of `(M ∩ A, θ)`,
since the blow-ups of `M` and `M ∩ A` agree near the origin. -/
theorem Submission.ind_pi_restriction_open_im :
    ∀ (P k : ℕ) (U A : Set (Eucl P)) (X R : GeometricCurrentOn U k), IsOpen U → IsOpen A →
      IsIntegerMultiplicity X → IsRestriction X A R → IsIntegerMultiplicity R := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k U A X R hU hA hX hR
  obtain ⟨M, θ, ξ, hT, hθN, hXτ⟩ := hX
  obtain ⟨hAm, μ, v, hrep, hRv⟩ := hR
  -- `|⟨α, ξ(x)⟩| ≤ ‖α‖` for `Hᵏ⌞M`-a.e. `x`, since `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ` orthonormal.
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
  -- `θ ⟨ω, ξ⟩` is `Hᵏ`-integrable on `M` for every test form `ω`: on `M ∩ spt ω` it is `θ` times
  -- a measurable function bounded by `sup ‖ω‖`, and it vanishes on `M \ spt ω`.
  have hint : ∀ ω : TestFormOn U k, IntegrableOn
      (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)) M
      (μHE[k] : Measure (Eucl P)) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Eucl P) k) := ContDiff.continuous ω.2.1.1
    have hωs : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
    obtain ⟨C, hC⟩ := hωc.bounded_above_of_compact_support hωs
    have hle : (μHE[k] : Measure (Eucl P)).restrict
        (M ∩ tsupport (ω : DifferentialForm (Eucl P) k)) ≤
        (μHE[k] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono Set.inter_subset_left le_rfl
    have hmeas : AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Eucl P) k) x))
        ((μHE[k] : Measure (Eucl P)).restrict M) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hT.aestronglyMeasurable.prodMk hωc.aestronglyMeasurable)
    have hK : IntegrableOn (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x))
        (M ∩ tsupport (ω : DifferentialForm (Eucl P) k)) (μHE[k] : Measure (Eucl P)) := by
      refine (hT.integrableOn _ hωs ω.2.2).mul_bdd (c := C) (hmeas.mono_measure hle) ?_
      filter_upwards [ae_mono hle hunit] with x hx
      exact (hx _).trans (hC x)
    refine hK.of_ae_sdiff_eq_zero hT.nullMeasurableSet
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ∉ tsupport (ω : DifferentialForm (Eucl P) k) := fun h => hx.2 ⟨hx.1, h⟩
    rw [image_eq_zero_of_notMem_tsupport hx', map_zero, mul_zero]
  -- Smooth cutoffs `φ_j → 1_A` pointwise, `0 ≤ φ_j ≤ 1`: `φ_j = s(j f)` with `f ≥ 0` smooth,
  -- `{f ≠ 0} = A`, and `s` the smooth transition (`s = 0` on `(-∞, 0]`, `s = 1` on `[1, ∞)`).
  obtain ⟨φ, hφs, hφb, hφlim⟩ : ∃ φ : ℕ → Eucl P → ℝ,
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ j)) ∧
      (∀ j x, ‖φ j x‖ ≤ 1) ∧ ∀ (g : Eucl P → ℝ) (x : Eucl P),
        Tendsto (fun j => φ j x * g x) atTop (𝓝 (A.indicator g x)) := by
    obtain ⟨f, hfA, hfs, hfr⟩ := hA.exists_contDiff_support_eq (n := ⊤)
    refine ⟨fun j x => Real.smoothTransition (j * f x), fun j =>
      Real.smoothTransition.contDiff.comp (contDiff_const.mul hfs), fun j x => ?_, fun g x => ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    by_cases hx : x ∈ A
    · have hfx : 0 < f x := by
        have hne : f x ≠ 0 := by rw [← Function.mem_support, hfA]; exact hx
        exact lt_of_le_of_ne (hfr ⟨x, rfl⟩).1 (Ne.symm hne)
      rw [Set.indicator_of_mem hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈(f x)⁻¹⌉₊] with j hj
      rw [Real.smoothTransition.one_of_one_le, one_mul]
      calc (1 : ℝ) = (f x)⁻¹ * f x := (inv_mul_cancel₀ hfx.ne').symm
        _ ≤ j * f x :=
          mul_le_mul_of_nonneg_right ((Nat.le_ceil _).trans (by exact_mod_cast hj)) hfx.le
    · have hfx : f x = 0 := by rw [← Function.notMem_support, hfA]; exact hx
      rw [Set.indicator_of_notMem hx]
      simp only [hfx, mul_zero, Real.smoothTransition.zero, zero_mul]
      exact tendsto_const_nhds
  -- `R = τ(M ∩ A, θ, ξ)`: with `ω_j = φ_j ω`, `X(ω_j) → ∫_A ⟨ω, v⟩ dμ = R(ω)` and
  -- `X(ω_j) = τ(M, θ, ξ)(ω_j) → τ(M ∩ A, θ, ξ)(ω)` by dominated convergence.
  have hRτ : ∀ ω : TestFormOn U k, R ω = tauAction k (M ∩ A) θ ξ ω := by
    intro ω
    have hωsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) := ω.2.1.1
    have hωcs : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
    have hωU : tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U := ω.2.2
    have hcut : ∀ j : ℕ, ∃ ω' : TestFormOn U k, (ω' : DifferentialForm (Eucl P) k) =
        fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x := by
      intro j
      have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x) := (hφs j).smul hωsm
      have hcs : HasCompactSupport (fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x) :=
        hωcs.mono fun x hx h0 => hx (by simp only [h0, smul_zero])
      have hsU : tsupport (fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x) ⊆ U :=
        (tsupport_smul_subset_right _ _).trans hωU
      exact ⟨⟨_, ⟨⟨hsm, hcs⟩, hsU⟩⟩, rfl⟩
    choose ωj hωj using hcut
    have hval : ∀ j x, (ωj j : DifferentialForm (Eucl P) k) x =
        φ j x • (ω : DifferentialForm (Eucl P) k) x := fun j x => congrFun (hωj j) x
    have h1 : Tendsto (fun j => X (ωj j)) atTop (𝓝 (R ω)) := by
      rw [hRv ω, ← integral_indicator hAm]
      have hX1 : (fun j => X (ωj j)) =
          fun j => ∫ x, v x ((ωj j : DifferentialForm (Eucl P) k) x) ∂μ :=
        funext fun j => (hrep (ωj j)).2
      rw [hX1]
      refine tendsto_integral_of_dominated_convergence
        (fun x => ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖)
        (fun j => (hrep (ωj j)).1.aestronglyMeasurable) (hrep ω).1.norm
        (fun j => Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => ?_)
      · rw [hval, map_smul, smul_eq_mul, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφb j x)
      · refine (hφlim (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) x).congr
          (fun j => ?_)
        rw [hval, map_smul, smul_eq_mul]
    have h2 : Tendsto (fun j => X (ωj j)) atTop (𝓝 (tauAction k (M ∩ A) θ ξ ω)) := by
      have hX2 : (fun j => X (ωj j)) = fun j => ∫ x in M,
          θ x * ξ x ((ωj j : DifferentialForm (Eucl P) k) x) ∂(μHE[k] : Measure (Eucl P)) :=
        funext fun j => hXτ (ωj j)
      rw [hX2, tauAction, ← setIntegral_indicator hAm]
      refine tendsto_integral_of_dominated_convergence
        (fun x => ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)‖)
        (fun j => (hint (ωj j)).aestronglyMeasurable) (hint ω).norm
        (fun j => Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => ?_)
      · rw [hval, map_smul, smul_eq_mul, mul_left_comm, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφb j x)
      · refine (hφlim (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)) x).congr
          (fun j => ?_)
        rw [hval, map_smul, smul_eq_mul, mul_left_comm]
    exact tendsto_nhds_unique h1 h2
  -- Locality of weighted tangent planes (Simon Ch. 3, 1.7): for `x ∈ A`, if `g = 0` off
  -- `B_ρ(0)` and `B_δ(x) ⊆ A`, then for `0 < r < δ / ρ` the blow-up integrands vanish off
  -- `W = η_{x,r}(A)`, and `W ∩ η_{x,r}(M) = W ∩ η_{x,r}(M ∩ A)`.
  have htan : ∀ x ∈ A, ∀ L : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x L := by
    intro x hxA L hL
    refine ⟨hL.1, fun g => (hL.2 g).congr' ?_⟩
    obtain ⟨ρ, hρ, hgρ⟩ := g.hasCompactSupport.exists_pos_le_norm
    obtain ⟨δ, hδ, hδA⟩ := Metric.isOpen_iff.mp hA x hxA
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hρ)] with r hr
    obtain ⟨hr0, hrρ⟩ := hr
    have hcont : Continuous fun y : Eucl P => x + r • y :=
      continuous_const.add (continuous_const_smul r)
    set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' A with hW
    have hWm : MeasurableSet W := (hA.preimage hcont).measurableSet
    have hvan : ∀ y, y ∉ W → g y * θ (x + r • y) = 0 := by
      intro y hy
      have hgy : g y = 0 := by
        apply hgρ
        have h1 : x + r • y ∉ ball x δ := fun h => hy (hδA h)
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0, not_lt] at h1
        rw [lt_div_iff₀ hρ] at hrρ
        exact le_of_lt (lt_of_mul_lt_mul_left (hrρ.trans_le h1) hr0.le)
      rw [hgy, zero_mul]
    have hcutW : ∀ S : Set (Eucl P),
        ∫ y in blowUpMap x r '' S, g y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
          ∫ y in W ∩ blowUpMap x r '' S, g y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
      intro S
      rw [← Measure.restrict_restrict hWm, setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
    have hset : W ∩ blowUpMap x r '' M = W ∩ blowUpMap x r '' (M ∩ A) := by
      ext y
      constructor
      · rintro ⟨hyW, z, hzM, rfl⟩
        refine ⟨hyW, z, ⟨hzM, ?_⟩, rfl⟩
        have hz : x + r • blowUpMap x r z = z := by
          simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel]
        have hzW : x + r • blowUpMap x r z ∈ A := hyW
        rwa [hz] at hzW
      · rintro ⟨hyW, z, ⟨hzM, -⟩, rfl⟩
        exact ⟨hyW, z, hzM, rfl⟩
    rw [hcutW M, hcutW (M ∩ A), hset]
  -- `(M ∩ A, θ, ξ)` is a rectifiable triple with integer multiplicity representing `R`.
  refine ⟨M ∩ A, θ, ξ, ⟨Set.inter_subset_left.trans hT.subset,
    hT.nullMeasurableSet.inter hAm.nullMeasurableSet,
    hT.countablyRectifiable.mono Set.inter_subset_left,
    fun x hx => hT.pos x hx.1,
    fun K hK hKU => (hT.integrableOn K hK hKU).mono_set
      (Set.inter_subset_inter_left K Set.inter_subset_left),
    hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl),
    ?_⟩, fun x hx => hθN x hx.1, hRτ⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hT.orients,
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (ae_restrict_mem hAm)]
    with x hx hxA
  obtain ⟨τ, hτ, hτL, hξ⟩ := hx
  exact ⟨τ, hτ, htan x hxA _ hτL, hξ⟩
theorem Submission.ind_pi_ss_cycle_slice_boundary : ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ) (t : ℝ) (S : GeometricCurrentOn U m), IsOpen U → T.boundary = 0 → IsSlice T f t S → ∃ A : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ f x < t} A ∧ A.boundary = S := by
  intro P m U T f t S hU hT hSl
  -- Unfold `IsSlice` (4.6): `S = ∂A − B` with `A = T ⌞ Aₜ`, `B = (∂T) ⌞ Aₜ`, where
  -- `Aₜ = {x ∈ U : f x < t}` and `B ω = ∫_{Aₜ} ⟨ω, v⟩ dμ` for a representation `(μ, v)` of `∂T`.
  obtain ⟨A, B, hA, ⟨hmeas, μ, v, hrep, hB⟩, hS⟩ := hSl
  -- `B = 0`, i.e. uniqueness of restrictions for the zero current `∂T`: testing `∂T = 0` with
  -- `g ω` (`g ∈ C_c^∞(U)`) shows that `⟨ω, v⟩` integrates to zero against every such `g`, so it
  -- vanishes `μ`-a.e. on `U ⊇ Aₜ`.
  have hB0 : ∀ ω : TestFormOn U m, B ω = 0 := by
    intro ω
    have hae : ∀ᵐ x ∂μ, x ∈ U → v x ((ω : DifferentialForm (Eucl P) m) x) = 0 := by
      refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hrep ω).1.locallyIntegrable.locallyIntegrableOn U) (fun g hg hgc hgU => ?_)
      let gω : TestFormOn U m := ⟨fun x => g x • (ω : DifferentialForm (Eucl P) m) x,
        ⟨hg.smul ω.property.1.1, hgc.smul_right⟩,
        (tsupport_smul_subset_left _ _).trans hgU⟩
      calc ∫ x, g x • v x ((ω : DifferentialForm (Eucl P) m) x) ∂μ
          = ∫ x, v x ((gω : DifferentialForm (Eucl P) m) x) ∂μ := by
            congr 1
            funext x
            exact (map_smul (v x) (g x) _).symm
        _ = T.boundary gω := ((hrep gω).2).symm
        _ = 0 := by rw [hT, GeometricCurrentOn.zero_apply]
    rw [hB ω]
    exact integral_eq_zero_of_ae
      ((ae_restrict_iff' hmeas).2 (hae.mono fun x hx hxA => hx hxA.1))
  -- Hence `S = ∂A − 0 = ∂A`, with `A` the restriction of `T` to `Aₜ`.
  refine ⟨A, hA, GeometricCurrentOn.ext fun ω => ?_⟩
  rw [hS ω, hB0 ω, sub_zero]
/-- Simon Ch. 6, (2.8)–(2.9): for `W ⊂⊂ U` and `S = X ⌞ A`, `M_W(S) ≤ M_W(X)`.  For an
admissible `ω`, `S(ω) = ∫_A ⟨ω, v⟩ dμ`.  By regularity of the finite measure `|⟨ω, v⟩| μ` there
are a closed `F ⊆ A` and an open `G ⊇ A` with `∫_{G \ F} |⟨ω, v⟩| dμ < ε`; a smooth
`ψ : ℝ^P → [0, 1]` equal to `1` on `F` with support `G` makes `ψ ω` admissible and
`S(ω) ≤ X(ψ ω) + ε ≤ M_W(X) + ε`. -/
theorem Submission.ind_pi_ss_restriction_massOn_le : ∀ (P k : ℕ) (U W A : Set (Eucl P)) (X S : GeometricCurrentOn U k), IsOpen U → CompactlyContainedOpen W U → IsRestriction X A S → S.massOn W ≤ X.massOn W := by
  intro P k U W A X S _ _ hR
  obtain ⟨hA, μ, v, hrep, hS⟩ := hR
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  set f : Eucl P → ℝ := fun x => v x ((ω : DifferentialForm (Eucl P) k) x)
  have hfi : Integrable f μ := (hrep ω).1
  -- The finite measure `ν = |f| μ`.
  set ν : Measure (Eucl P) := μ.withDensity (fun x => ‖f x‖ₑ) with hν_def
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfi.2.ne
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by simp [hε.ne']
  obtain ⟨F, hFA, hFc, hνF⟩ := hA.exists_isClosed_sdiff_lt (μ := ν) (measure_ne_top ν A) hε2
  obtain ⟨G, hAG, hGo, -, hνG⟩ := hA.exists_isOpen_sdiff_lt (μ := ν) (measure_ne_top ν A) hε2
  obtain ⟨ψ, hψs, hψr, hψsupp, hψ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hGo hFc (hFA.trans hAG)
  -- The cut-off test form `ψ ω`.
  have hω_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) :=
    ω.2.1.1
  have hω_cpt : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
  let ω' : TestFormOn U k := ⟨fun x => ψ x • (ω : DifferentialForm (Eucl P) k) x,
    ⟨hψs.smul hω_smooth, HasCompactSupport.smul_left (f := ψ) hω_cpt⟩,
    (tsupport_smul_subset_right _ _).trans ω.2.2⟩
  have hω' : ω' ∈ massAdmissibleOn U k W := by
    refine ⟨(tsupport_smul_subset_right _ _).trans hω.1, fun x => ?_⟩
    change covectorEuclideanNorm (ψ x • (ω : DifferentialForm (Eucl P) k) x) ≤ 1
    have h0 := hψr ⟨x, rfl⟩
    rw [hsmul, abs_of_nonneg h0.1]
    calc ψ x * covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ 1 * 1 :=
          mul_le_mul h0.2 (hω.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hω'f : ∀ x, v x ((ω' : DifferentialForm (Eucl P) k) x) = ψ x * f x := by
    intro x
    change v x (ψ x • (ω : DifferentialForm (Eucl P) k) x) = ψ x * f x
    rw [map_smul, smul_eq_mul]
  have hψf : Integrable (fun x => ψ x * f x) μ := by
    simpa only [hω'f] using (hrep ω').1
  have hXω' : X ω' = ∫ x, ψ x * f x ∂μ := by
    simpa only [hω'f] using (hrep ω').2
  have hGF : MeasurableSet (G \ F) := hGo.measurableSet.diff hFc.measurableSet
  -- Pointwise: `1_A f - ψ f ≤ 1_{G \ F} |f|`.
  have hpt : ∀ x, A.indicator f x - ψ x * f x ≤ (G \ F).indicator (fun x => |f x|) x := by
    intro x
    have h0 := hψr ⟨x, rfl⟩
    have hnn : 0 ≤ (G \ F).indicator (fun x => |f x|) x :=
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
    by_cases hxF : x ∈ F
    · rw [Set.indicator_of_mem (hFA hxF), (hψ1 x).1 hxF, one_mul, sub_self]
      exact hnn
    · by_cases hxG : x ∈ G
      · rw [Set.indicator_of_mem (show x ∈ G \ F from ⟨hxG, hxF⟩)]
        by_cases hxA : x ∈ A
        · rw [Set.indicator_of_mem hxA]
          nlinarith [le_abs_self (f x), abs_nonneg (f x), h0.1, h0.2]
        · rw [Set.indicator_of_notMem hxA]
          nlinarith [neg_abs_le (f x), abs_nonneg (f x), h0.1, h0.2]
      · have hψ0 : ψ x = 0 := by
          by_contra h
          exact hxG (hψsupp ▸ (Function.mem_support.mpr h))
        rw [Set.indicator_of_notMem (fun h => hxG (hAG h)), hψ0, zero_mul, sub_zero]
        exact hnn
  have hνGF : ν (G \ F) < ε := by
    calc ν (G \ F) ≤ ν ((G \ A) ∪ (A \ F)) := measure_mono fun x hx => by
          by_cases hxA : x ∈ A
          · exact Or.inr ⟨hxA, hx.2⟩
          · exact Or.inl ⟨hx.1, hxA⟩
      _ ≤ ν (G \ A) + ν (A \ F) := measure_union_le _ _
      _ < (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := ENNReal.add_lt_add hνG hνF
      _ = ε := ENNReal.add_halves _
  have hint : ∫ x in G \ F, |f x| ∂μ ≤ ε := by
    have h1 : ∫ x in G \ F, |f x| ∂μ = (ν (G \ F)).toReal := by
      rw [hν_def, withDensity_apply _ hGF]
      simp_rw [← Real.norm_eq_abs]
      exact integral_norm_eq_lintegral_enorm hfi.aestronglyMeasurable.restrict
    rw [h1]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hνGF.le
  have hest : S ω ≤ X ω' + ε := by
    have hdiff : S ω - X ω' = ∫ x, (A.indicator f x - ψ x * f x) ∂μ := by
      rw [hS ω, hXω', integral_sub (hfi.indicator hA) hψf, integral_indicator hA]
    have hle : ∫ x, (A.indicator f x - ψ x * f x) ∂μ ≤
        ∫ x, (G \ F).indicator (fun x => |f x|) x ∂μ :=
      integral_mono ((hfi.indicator hA).sub hψf) (hfi.abs.indicator hGF) hpt
    rw [integral_indicator hGF] at hle
    linarith
  calc ENNReal.ofReal (S ω) ≤ ENNReal.ofReal (X ω' + ε) := ENNReal.ofReal_le_ofReal hest
    _ ≤ ENNReal.ofReal (X ω') + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (X ω') + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ X.massOn W + ε := by gcongr; exact X.le_massOn hω'
/-- **Slices of a cycle (Simon Ch. 6, 4.5(1)–(2), 4.6, 4.10).**  For `X ∈ 𝒟_{m+1}(U)` with
`∂X = 0` and locally finite mass, `d` `L`-Lipschitz and `a < b`, there are restrictions
`A_t = X ⌞ {d < t}` and a measurable `g` with `M_W(∂A_t) ≤ g(t)` on `(a, b)` and
`∫⁻_{(a,b)} g ≤ L · M_W(X)`.  As `M_V(∂X) = M_V(0) = 0`, `SlicingTheorem` gives slices
`S_t = ⟨X, d, t⟩`, and `∂A_t = S_t` by `ind_pi_ss_cycle_slice_boundary`.  The band
`{a < d < b} = {|d - (a + b)/2| < (b - a)/2}` is a sublevel set of an `L`-Lipschitz function, so
the same lemma gives the restriction `R = X ⌞ {a < d < b}` used by the mass clause of 4.10
(`‖Dd‖ ≤ L`); finally `M_W(R) ≤ M_W(X)` by `ind_pi_ss_restriction_massOn_le`. -/
theorem Submission.ind_pi_ss_cycle_slice_family : SlicingTheorem → ∀ (P m : ℕ) (U W : Set (Eucl P)) (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ), IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b → X.boundary = 0 → (∀ V, CompactlyContainedOpen V U → X.massOn V < ∞) → ∃ (A : ℝ → GeometricCurrentOn U (m + 1)) (g : ℝ → ℝ≥0∞), Measurable g ∧ (∀ t, IsRestriction X {x | x ∈ U ∧ d x < t} (A t)) ∧ (∀ t ∈ Ioo a b, (A t).boundary.massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * X.massOn W := by
  intro hST P m U W X d L a b hU hW hd hab hX0 hXfin
  -- Step 1: `M_V(∂X) = M_V(0) = 0`, so `X` satisfies the hypotheses of `SlicingTheorem`.
  have hfin : ∀ V, CompactlyContainedOpen V U →
      X.massOn V < ∞ ∧ X.boundary.massOn V < ∞ := by
    intro V hV
    have h0 : (0 : GeometricCurrentOn U m).massOn V = 0 := by
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, -, rfl⟩
      simp
    rw [hX0, h0]
    exact ⟨hXfin V hV, ENNReal.zero_lt_top⟩
  -- Step 2: the slices `S_t = ⟨X, d, t⟩` and the mass clause of 4.10 for `d`.
  obtain ⟨S, hS, -, -, hSmass⟩ := hST P m U hU X hfin d L hd.lipschitzOnWith
  -- Step 3: `A_t = X ⌞ {d < t}` with `∂A_t = S_t`.
  choose A hAres hAbd using fun t =>
    Submission.ind_pi_ss_cycle_slice_boundary P m U X d t (S t) hU hX0 (hS t)
  -- Step 4: `R = X ⌞ {a < d < b}`, as the band is the sublevel set `{|d - c| < r}` of the
  -- `L`-Lipschitz function `|d - c|`, `c = (a + b)/2`, `r = (b - a)/2`.
  have hc : LipschitzWith L fun x => |d x - (a + b) / 2| := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    calc dist |d x - (a + b) / 2| |d y - (a + b) / 2|
        = |(|d x - (a + b) / 2| - |d y - (a + b) / 2|)| := Real.dist_eq _ _
      _ ≤ |(d x - (a + b) / 2) - (d y - (a + b) / 2)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = dist (d x) (d y) := by rw [sub_sub_sub_cancel_right, Real.dist_eq]
      _ ≤ L * dist x y := hd.dist_le_mul x y
  obtain ⟨S', hS', -⟩ := hST P m U hU X hfin (fun x => |d x - (a + b) / 2|) L hc.lipschitzOnWith
  obtain ⟨R, hR, -⟩ := Submission.ind_pi_ss_cycle_slice_boundary P m U X
    (fun x => |d x - (a + b) / 2|) ((b - a) / 2) (S' ((b - a) / 2)) hU hX0 (hS' _)
  have hRband : IsRestriction X {x | x ∈ U ∧ a < d x ∧ d x < b} R := by
    have hband : {x | x ∈ U ∧ a < d x ∧ d x < b} =
        {x | x ∈ U ∧ |d x - (a + b) / 2| < (b - a) / 2} := by
      ext x
      simp only [mem_ofPred_eq, abs_sub_lt_iff]
      constructor
      · rintro ⟨hx, h₁, h₂⟩
        exact ⟨hx, by linarith, by linarith⟩
      · rintro ⟨hx, h₁, h₂⟩
        exact ⟨hx, by linarith, by linarith⟩
    rw [hband]
    exact hR
  -- Step 5: the mass clause of 4.10 on `W`, with `‖Dd‖ ≤ L` everywhere.
  have hDd : ∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ d x‖₊ ≤ L :=
    ae_of_all _ fun x _ => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_fderiv_le_of_lipschitz ℝ hd
  obtain ⟨g, hg, hgS, hgint⟩ :=
    hSmass W hW.1 (subset_closure.trans hW.2.2) L hDd a b hab R hRband
  -- Step 6: `M_W(∂A_t) = M_W(S_t) ≤ g(t)` and `∫⁻ g ≤ L · M_W(R) ≤ L · M_W(X)`.
  refine ⟨A, g, hg, hAres, fun t ht => ?_, ?_⟩
  · rw [hAbd t]
    exact hgS t ht
  · calc ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * R.massOn W := hgint
      _ ≤ (L : ℝ≥0∞) * X.massOn W := by
        gcongr
        exact Submission.ind_pi_ss_restriction_massOn_le P (m + 1) U W _ X R hU hW hRband
/-- Fatou selection of a good level (the "selection argument as in 6.7(2) of Ch. 2" in the proof
of Simon Ch. 6, 8.2): if `∫⁻_{(a,b)} g_k ≤ C < ∞` for all `k` and `E` is countable, there are
`γ ∈ (a, b) \ E`, a subsequence `σ` and `G < ∞` with `g_{σ(k)}(γ) ≤ G` for all `k`.  By Fatou,
`∫⁻_{(a,b)} liminf_k g_k ≤ C`, so `liminf_k g_k(γ) < ∞` for some `γ ∈ (a, b) \ E` (`E` is
Lebesgue-null); with `G = liminf_k g_k(γ) + 1`, `g_k(γ) < G` for infinitely many `k`. -/
theorem Submission.ind_pi_ss_fatou_level_selection :
    ∀ (g : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (C : ℝ≥0∞) (E : Set ℝ), a < b → (∀ k, Measurable (g k)) →
      C < ∞ → (∀ k, ∫⁻ t in Ioo a b, g k t ≤ C) → E.Countable →
      ∃ (γ : ℝ) (σ : ℕ → ℕ) (G : ℝ≥0∞), γ ∈ Ioo a b ∧ γ ∉ E ∧ StrictMono σ ∧ G < ∞ ∧
        ∀ k, g (σ k) γ ≤ G := by
  intro g a b C E hab hg hC hgC hE
  -- Fatou: `F = liminf_k g_k` is measurable and `∫⁻_{(a,b)} F ≤ liminf_k ∫⁻_{(a,b)} g_k ≤ C`.
  have hF : Measurable fun t => liminf (fun k => g k t) atTop := Measurable.liminf hg
  have hFC : ∫⁻ t in Ioo a b, liminf (fun k => g k t) atTop ≤ C :=
    (lintegral_liminf_le hg).trans (liminf_le_of_frequently_le' (Frequently.of_forall hgC))
  -- For a.e. `t` w.r.t. `volume⌞(a, b)`: `F t < ∞`, `t ∉ E` (`E` is Lebesgue-null), `t ∈ (a, b)`.
  have h₁ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), liminf (fun k => g k t) atTop < ∞ :=
    ae_lt_top hF (hFC.trans_lt hC).ne
  have h₂ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∉ E :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hE.measure_zero volume))
  have h₃ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∈ Ioo a b := ae_restrict_mem measurableSet_Ioo
  -- `volume (a, b) = b - a > 0`, so the a.e. filter is nontrivial and a good `γ` exists.
  have hne : (ae (volume.restrict (Ioo a b))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.2 hab
  obtain ⟨γ, hγF, hγE, hγ⟩ := (h₁.and (h₂.and h₃)).exists
  -- `G = F(γ) + 1 > liminf_k g_k(γ)`, so `g_k(γ) < G` frequently: extract `σ`.
  have hG : liminf (fun k => g k γ) atTop < liminf (fun k => g k γ) atTop + 1 :=
    ENNReal.lt_add_right hγF.ne one_ne_zero
  obtain ⟨σ, hσ, hσG⟩ := extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (h := hG))
  exact ⟨γ, σ, _, hγ, hγE, hσ, ENNReal.add_lt_top.2 ⟨hγF, ENNReal.one_lt_top⟩,
    fun k => (hσG k).le⟩

/-- Simon Ch. 6, proof of 8.2, display (8) ("by 4.5(1) and a selection argument as in 6.7(2) of
Ch. 2"): for cycles `X_k ⇀ X` with `sup_k M_W(X_k) < ∞` there are a level `γ ∈ (a, b)` and a
subsequence `κ` such that the restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` satisfy
`M_W(R_k) ≤ M_W(X_{κ(k)})`, `sup_k M_W(∂R_k) < ∞` and `R_k(ω) → (X ⌞ {d < γ})(ω)` for
`spt ω ⊆ W`. -/
theorem Submission.ind_pi_good_slice_selection :
    SlicingTheorem → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P))
        (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U →
        (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U →
        ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E,
          ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k),
            (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) →
            IsRestriction X {x | x ∈ U ∧ φ x < s} R →
            (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
              Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧
            (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K →
              WeaklyConvergesOn Rj R)) →
    ∀ (P m : ℕ) (U W : Set (Eucl P)) (Xk : ℕ → GeometricCurrentOn U (m + 1))
      (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ),
      IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b →
      (∀ k, (Xk k).boundary = 0) →
      (∀ k V, CompactlyContainedOpen V U → (Xk k).massOn V < ∞) →
      (⨆ k, (Xk k).massOn W) < ∞ → WeaklyConvergesOn Xk X →
      ∃ (γ : ℝ) (κ : ℕ → ℕ) (Rk : ℕ → GeometricCurrentOn U (m + 1)) (G : ℝ≥0∞),
        γ ∈ Ioo a b ∧ StrictMono κ ∧ G < ∞ ∧
        (∀ k, IsRestriction (Xk (κ k)) {x | x ∈ U ∧ d x < γ} (Rk k)) ∧
        (∀ k, (Rk k).massOn W ≤ (Xk (κ k)).massOn W) ∧
        (∀ k, (Rk k).boundary.massOn W ≤ G) ∧
        ∀ R : GeometricCurrentOn U (m + 1), IsRestriction X {x | x ∈ U ∧ d x < γ} R →
          ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ W →
            Tendsto (fun k => Rk k ω) atTop (𝓝 (R ω)) := by
  intro hSlice hRWL P m U W Xk X d L a b hU hW hd hab hcycle hmass hsup hconv
  -- Steps 1–4 for each cycle `X_k`: restrictions `A k t` of `X_k` to `{d < t}` with
  -- `M_W(∂(A k t)) ≤ g k t` for `t ∈ (a, b)` and `∫⁻_{(a,b)} g k ≤ L · M_W(X_k)`.
  choose A g hg hA hAg hgi using fun k =>
    Submission.ind_pi_ss_cycle_slice_family hSlice P m U W (Xk k) d L a b hU hW hd hab
      (hcycle k) (hmass k)
  -- Step 5: (RWL) with `φ := d` gives `ψ` and a countable exceptional set `E` of levels.
  obtain ⟨ψ, E, hψ, hE, hlim⟩ := hRWL P (m + 1) U hU Xk X W d hconv hW.1
    (subset_closure.trans hW.2.2) hsup hd.continuous.continuousOn
  -- `∫⁻_{(a,b)} g (ψ k) ≤ L · M_W(X_{ψ k}) ≤ L · sup_j M_W(X_j) < ∞`.
  have hgψ : ∀ k, ∫⁻ t in Ioo a b, g (ψ k) t ≤ (L : ℝ≥0∞) * ⨆ j, (Xk j).massOn W := fun k =>
    (hgi (ψ k)).trans (mul_le_mul_right (le_iSup (fun j => (Xk j).massOn W) (ψ k)) _)
  -- Steps 6–8: a level `γ ∈ (a, b) \ E` and a subsequence `σ` with `g (ψ (σ k)) γ ≤ G`.
  obtain ⟨γ, σ, G, hγ, hγE, hσ, hG, hgG⟩ :=
    Submission.ind_pi_ss_fatou_level_selection (fun k => g (ψ k)) a b
      ((L : ℝ≥0∞) * ⨆ j, (Xk j).massOn W) E hab (fun k => hg (ψ k))
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hsup) hgψ hE
  -- Step 9: `κ := ψ ∘ σ` and `R_k := A (κ k) γ`; convergence passes to the subsequence `σ`.
  refine ⟨γ, ψ ∘ σ, fun k => A (ψ (σ k)) γ, G, hγ, hψ.comp hσ, hG, fun k => hA (ψ (σ k)) γ,
    fun k => Submission.ind_pi_ss_restriction_massOn_le P (m + 1) U W _ _ _ hU hW
      (hA (ψ (σ k)) γ), fun k => (hAg (ψ (σ k)) γ hγ).trans (hgG k), fun R hR ω hω => ?_⟩
  exact ((hlim γ hγE (fun j => A (ψ j) γ) R (fun j => hA (ψ j) γ) hR).1 ω hω).comp
    hσ.tendsto_atTop

/-- Simon Ch. 6, proof of 8.2, displays (8)–(9): localization of the cycles `Y_k ⇀ c [[Q]]`,
`Q = span τ`, to the thin cylinder `W' = {‖p‖ < 1, d < 3/4} ⊂⊂ B₂(0)`.  The current
`X = c [[Q]] ∈ 𝒟ₙ(B₂(0))` has the representation `(Hⁿ ⌞ Q, c τ₁ ∧ ⋯ ∧ τₙ)`, and
`X_k = Y_k|_{B₂(0)}` are integer multiplicity cycles with `X_k ⇀ X`.  A good level
`γ ∈ (1/4, 1/2)` of `d` gives restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` with bounded
`M_{W'}(R_k) + M_{W'}(∂R_k)` and `R_k → X ⌞ {d < γ} = X` on forms supported in `W'` (the
measure of `X` lives on `Q ⊆ {d = 0}`).  Then `Z_k = R_k|_{W'}` are integer multiplicity,
supported in `{d ≤ γ}`, and converge to `c [[Q]]` in `W'`. -/
theorem Submission.ind_pi_localized_cycles :
    SlicingTheorem → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P)) (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U → (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k), (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) → IsRestriction X {x | x ∈ U ∧ φ x < s} R → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K → WeaklyConvergesOn Rj R)) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c : ℝ) (Y : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (p : Eucl P →L[ℝ] Eucl (m + 1)) (d : Eucl P → ℝ), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → (∀ k, IsIntegerMultiplicity (Y k)) → (∀ k, (Y k).boundary = 0) → (⨆ k, (Y k).massOn (ball (0 : Eucl P) 2)) < ∞ → (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ ball (0 : Eucl P) 2 → Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → ∃ (γ : ℝ) (Z : ℕ → GeometricCurrentOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1)), 0 ≤ γ ∧ γ < 3 / 4 ∧ (∀ k, IsIntegerMultiplicity (Z k)) ∧ (∀ k, (Z k).support ⊆ {y | d y ≤ γ}) ∧ (⨆ k, ((Z k).mass + (Z k).boundary.mass)) < ∞ ∧ ∀ ω : TestFormOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1), Tendsto (fun k => Z k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P)))) := by
  intro hSlicing hRWL P m τ c Y p d hτ hp hd hYim hYb hYmass hYlim
  -- Step 0: `d` is `1`-Lipschitz and vanishes on `Q`, `W' ⊂⊂ B = B₂(0)`, `Hⁿ ⌞ Q` is finite on
  -- compact sets, and the finite-dimensional subspace `Q` is closed, hence measurable.
  obtain ⟨hLip, -, -, -, -, hdQ, hW', -⟩ :=
    Submission.ind_pi_frame_geometry P (m + 1) τ p d hτ hp hd
  obtain ⟨-, hQfin⟩ := Submission.ind_pi_span_integral P (m + 1) τ hτ
  set B : Set (Eucl P) := ball (0 : Eucl P) 2
  set W' : Set (Eucl P) := {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4}
  set Q : Set (Eucl P) := (Submodule.span ℝ (Set.range τ) : Set (Eucl P))
  have hW'B : W' ⊆ B := subset_closure.trans hW'.2.2
  have hQmeas : MeasurableSet Q := (Submodule.closed_of_finiteDimensional _).measurableSet
  -- Step 1: `X = c [[Q]] ∈ 𝒟ₙ(B)` with representation `(Hⁿ ⌞ Q, c τ₁ ∧ ⋯ ∧ τₙ)`.
  obtain ⟨X, hX⟩ := Submission.ind_pi_constant_vector_current P (m + 1) B
    ((μHE[m + 1] : Measure (Eucl P)).restrict Q) (c • simpleNVector τ) hQfin
  have hXω : ∀ ω : TestFormOn B (m + 1), X ω = c * ∫ z in Q,
      (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P)) := by
    intro ω
    rw [(hX ω).2, ← integral_const_mul]
    rfl
  -- Step 2: restricting the domain does not increase `M_V` and commutes with `∂`.
  have hmassRD : ∀ {k : ℕ} {U₁ U₂ : Set (Eucl P)} (T : GeometricCurrentOn U₂ k) (h : U₁ ⊆ U₂)
      (V : Set (Eucl P)), (T.restrictDomain h).massOn V ≤ T.massOn V := by
    intro k U₁ U₂ T h V
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    exact T.le_massOn (omega := testFormOnInclusion h k ω) hω
  have hbdRD : ∀ {k : ℕ} {U₁ U₂ : Set (Eucl P)} (T : GeometricCurrentOn U₂ (k + 1))
      (h : U₁ ⊆ U₂), (T.restrictDomain h).boundary = T.boundary.restrictDomain h :=
    fun _ _ => GeometricCurrentOn.ext fun _ => rfl
  -- Step 3: `X_k = Y_k|_B` are integer multiplicity cycles, `M_V(X_k) ≤ C₀ = sup_j M_B(Y_j)` for
  -- `V ⊆ B`, and `X_k ⇀ X` in `B`.
  set Xk : ℕ → GeometricCurrentOn B (m + 1) := fun k => (Y k).restrictDomain (subset_univ B)
  have hXim : ∀ k, IsIntegerMultiplicity (Xk k) := fun k =>
    Submission.br_restrictDomain_isIntegerMultiplicity P (m + 1) univ B (subset_univ B)
      isOpen_ball (Y k) (hYim k)
  have hXb : ∀ k, (Xk k).boundary = 0 := fun k => GeometricCurrentOn.ext fun ω => by
    change (Y k).boundary (testFormOnInclusion (subset_univ B) m ω) = 0
    rw [hYb k]
    rfl
  have hXmass : ∀ k (V : Set (Eucl P)), V ⊆ B → (Xk k).massOn V ≤ ⨆ j, (Y j).massOn B :=
    fun k V hV => ((hmassRD (Y k) (subset_univ B) V).trans ((Y k).massOn_mono hV)).trans
      (le_iSup (fun j => (Y j).massOn B) k)
  have hXloc : ∀ k V, CompactlyContainedOpen V B → (Xk k).massOn V < ∞ :=
    fun k V hV => (hXmass k V (subset_closure.trans hV.2.2)).trans_lt hYmass
  have hXsup : (⨆ k, (Xk k).massOn W') < ∞ :=
    (iSup_le fun k => hXmass k W' hW'B).trans_lt hYmass
  have hXlim : WeaklyConvergesOn Xk X := fun ω => by
    rw [hXω]
    exact hYlim (testFormOnInclusion (subset_univ B) (m + 1) ω) ω.property.2
  -- Step 4: a good level `γ ∈ (1/4, 1/2)` of `d`, restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` with
  -- `M_{W'}(R_k) ≤ M_{W'}(X_{κ(k)})`, `M_{W'}(∂R_k) ≤ G < ∞` and `R_k → X ⌞ {d < γ}` in `W'`.
  obtain ⟨γ, κ, Rk, G, hγ, -, hG, hRres, hRmass, hRbd, hRlim⟩ :=
    Submission.ind_pi_good_slice_selection hSlicing hRWL P m B W' Xk X d 1 (1 / 4) (1 / 2)
      isOpen_ball hW' hLip (by norm_num) hXb hXloc hXsup hXlim
  have hγ0 : 0 < γ := lt_trans (by norm_num) hγ.1
  -- Step 5: `X ⌞ A_γ = X` for the open set `A_γ = {x ∈ B : d x < γ}`: the measure `Hⁿ ⌞ Q` of `X`
  -- lives on `Q ⊆ {d = 0}`, and test forms in `B` vanish on `Q \ A_γ ⊆ Q \ B`.
  have hA : IsOpen {x | x ∈ B ∧ d x < γ} := by
    have h : IsOpen (B ∩ {x | d x < γ}) :=
      isOpen_ball.inter (isOpen_lt hLip.continuous continuous_const)
    exact h
  have hXX : IsRestriction X {x | x ∈ B ∧ d x < γ} X := by
    refine ⟨hA.measurableSet, _, _, hX, fun ω => ?_⟩
    rw [(hX ω).2]
    refine (setIntegral_eq_integral_of_ae_compl_eq_zero
      (ae_restrict_of_forall_mem hQmeas fun x hxQ hxA => ?_)).symm
    have hxB : x ∉ B := fun hxB => hxA ⟨hxB, by rw [hdQ x hxQ]; exact hγ0⟩
    rw [image_eq_zero_of_notMem_tsupport fun h => hxB (ω.property.2 h)]
    exact map_zero _
  -- Step 6: the restrictions `R_k` of the integer multiplicity `X_{κ(k)}` to the open set `A_γ`
  -- are integer multiplicity.
  have hRim : ∀ k, IsIntegerMultiplicity (Rk k) := fun k =>
    Submission.ind_pi_restriction_open_im P (m + 1) B {x | x ∈ B ∧ d x < γ} (Xk (κ k)) (Rk k)
      isOpen_ball hA (hXim (κ k)) (hRres k)
  -- Step 7: `Z_k = R_k|_{W'}`.
  refine ⟨γ, fun k => (Rk k).restrictDomain hW'B, hγ0.le, hγ.2.trans (by norm_num),
    fun k => Submission.br_restrictDomain_isIntegerMultiplicity P (m + 1) B W' hW'B hW'.1 (Rk k)
      (hRim k), fun k => ?_, ?_, fun ω => ?_⟩
  · -- `spt Z_k ⊆ {d ≤ γ}`: `R_k(ω) = ∫_{A_γ} ⟨ω, v⟩ dμ` vanishes if `spt ω ∩ {d ≤ γ} = ∅`.
    refine Submission.fiw_tb_ext_support_subset P (m + 1) W' {y | d y ≤ γ} _ hW'.1
      (isClosed_le hLip.continuous continuous_const) fun ω hω => ?_
    obtain ⟨-, μ, v, -, hRv⟩ := hRres k
    change Rk k (testFormOnInclusion hW'B (m + 1) ω) = 0
    rw [hRv]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hxω : x ∉ tsupport (ω : DifferentialForm (Eucl P) (m + 1)) :=
      fun h => Set.disjoint_left.mp hω h (le_of_lt hx.2)
    rw [testFormOnInclusion_coe, image_eq_zero_of_notMem_tsupport hxω]
    exact map_zero _
  · -- `M(Z_k) ≤ M_{W'}(R_k) ≤ M_{W'}(X_{κ(k)}) ≤ C₀` and `M(∂Z_k) ≤ M_{W'}(∂R_k) ≤ G`.
    have hbound : ∀ k, ((Rk k).restrictDomain hW'B).mass +
        ((Rk k).restrictDomain hW'B).boundary.mass ≤ (⨆ j, (Y j).massOn B) + G := by
      intro k
      refine add_le_add ?_ ?_
      · exact ((hmassRD (Rk k) hW'B W').trans (hRmass k)).trans (hXmass (κ k) W' hW'B)
      · rw [hbdRD]
        exact (hmassRD (Rk k).boundary hW'B W').trans (hRbd k)
    exact (iSup_le hbound).trans_lt (ENNReal.add_lt_top.2 ⟨hYmass, hG⟩)
  · -- `Z_k(ω) = R_k(ω) → X(ω) = c ∫_Q ⟨ω, τ₁ ∧ ⋯ ∧ τₙ⟩ dHⁿ`.
    have h := hRlim X hXX (testFormOnInclusion hW'B (m + 1) ω) ω.property.2
    rw [hXω] at h
    exact h

/-- Simon Ch. 6, proof of 8.2 (display (10) and `p_# S̃_j ⇀ θ [[ℝⁿ]]`): push the localized
currents `Z_k ⇀ c [[Q]]` (`Q = span τ`) in the cylinder `W′ = {‖p‖ < 1, d < 3/4}` forward by
the frame coordinates `p`.  The push-forwards `S′_k = p_# Z_k` are integer multiplicity currents in
`B₁(0) ⊆ ℝⁿ` with `M_W(S′_k) ≤ M(Z_k)` and `M_W(∂S′_k) ≤ M(∂Z_k)`, and `S′_k(ω) = Z_k(η)` for a
cut-off pull-back `η = ζ p^#ω ∈ 𝒟ⁿ(W′)` independent of `k`.  On `Q`, `η(τ) = ω(p ·)(e)`, so
`S′_k(ω) → c ∫_Q ω(p z)(e) dHⁿ(z) = c ∫_{B₁(0)} ω(e) dx = S(ω)`. -/
theorem Submission.ind_pi_projected_limit : LipschitzPushforwardIntegerMultiplicity → (LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c γ : ℝ) (p : Eucl P →L[ℝ] Eucl (m + 1)) (d : Eucl P → ℝ) (Z : ℕ → GeometricCurrentOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1)) (S : GeometricCurrentOn (ball (0 : Eucl (m + 1)) 1) (m + 1)), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → 0 ≤ γ → γ < 3 / 4 → (∀ k, IsIntegerMultiplicity (Z k)) → (∀ k, (Z k).support ⊆ {y | d y ≤ γ}) → (⨆ k, ((Z k).mass + (Z k).boundary.mass)) < ∞ → (∀ ω : TestFormOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1), Tendsto (fun k => Z k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → (∀ ω : TestFormOn (ball (0 : Eucl (m + 1)) 1) (m + 1), S ω = c * ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ S' : ℕ → GeometricCurrentOn (ball (0 : Eucl (m + 1)) 1) (m + 1), (∀ k, IsIntegerMultiplicity (S' k)) ∧ (∀ W, CompactlyContainedOpen W (ball (0 : Eucl (m + 1)) 1) → (⨆ k, ((S' k).massOn W + (S' k).boundary.massOn W)) < ∞) ∧ WeaklyConvergesOn S' S := by
  intro hLPF hSPF P m τ c γ p d Z S hτ hp hd hγ0 hγ hZim hZspt hZmass hZlim hS
  -- 0. Frame geometry: `W′` is open, `‖p‖ ≤ 1`, `p (∑ aᵢ τᵢ) = a`, `p τᵢ = eᵢ`, `d = 0` on `Q`,
  -- and `p⁻¹(K) ∩ {d ≤ γ}` is a compact subset of `W′` for every compact `K ⊆ B₁(0)`.
  obtain ⟨-, -, hpn, hpι, hpτ, hdQ, hW', hprop⟩ :=
    Submission.ind_pi_frame_geometry P (m + 1) τ p d hτ hp hd
  -- 1–3. The push-forwards `S′_k = p_# Z_k`, with `M_W(S′_k) ≤ M(Z_k)`, `M_W(∂S′_k) ≤ M(∂Z_k)`.
  obtain ⟨S', hS'im, hS'act, hS'mass⟩ :=
    Submission.ind_pi_pl_linear_pushforward_family hLPF hSPF P (m + 1) m _
      (ball (0 : Eucl (m + 1)) 1) {y | d y ≤ γ} p Z hW'.1 isOpen_ball hpn
      (fun y hy => mem_ball_zero_iff.mpr hy.1) (hprop γ hγ) hZim hZspt
  refine ⟨S', hS'im, fun W _ => lt_of_le_of_lt (iSup_mono fun k =>
    add_le_add (hS'mass k W).1 (hS'mass k W).2) hZmass, fun ω => ?_⟩
  obtain ⟨-, hωV⟩ := ω.property
  -- 4–6. A cut-off pull-back `η = ζ p^#ω ∈ 𝒟ⁿ(W′)` equal to `p^#ω` on an open `N ⊇ W′ ∩ {d ≤ γ}`;
  -- as `spt Z_k ⊆ W′ ∩ {d ≤ γ}`, `S′_k(ω) = Z_k(η)` for every `k`.
  obtain ⟨η, -, N, hN, hAN, -, -, hηN, hηt⟩ :=
    Submission.iwl_sp_exists_compatible_testForm P (m + 1) (m + 1) _ (ball (0 : Eucl (m + 1)) 1)
      ({y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ∩ {y | d y ≤ γ}) p hW'.1 inter_subset_left
      p.contDiff (fun K hK hKV => by
        obtain ⟨hKc, hKW⟩ := hprop γ hγ K hK hKV
        rwa [inter_left_comm, inter_eq_right.mpr hKW]) ω
  have hact : ∀ k, S' k ω = Z k η := fun k => hS'act k ω η ⟨N, hN,
    fun y hy => hAN ⟨(Z k).support_subset_domain hy, hZspt k hy⟩,
    fun x hx => by rw [hηN x hx, p.fderiv]⟩
  -- 7. On `Q`: `η(∑ aᵢ τᵢ)(τ) = ω(a)(e)`, since `ζ = 1` there when `a ∈ spt ω`, and both sides
  -- vanish otherwise.
  have hηQ : ∀ a : Eucl (m + 1), (η : DifferentialForm (Eucl P) (m + 1)) (∑ i, a i • τ i) τ =
      (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) a
        (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    intro a
    by_cases ha : a ∈ tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1))
    · have hdz : d (∑ i, a i • τ i) = 0 :=
        hdQ _ ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨fun i => a i, rfl⟩)
      have hz : ∑ i, a i • τ i ∈ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ∩ {y | d y ≤ γ} := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hpι]
          exact mem_ball_zero_iff.mp (hωV ha)
        · rw [hdz]
          norm_num
        · show d (∑ i, a i • τ i) ≤ γ
          rw [hdz]
          exact hγ0
      rw [hηN _ (hAN hz), p.fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply, hpι]
      congr 1
      funext i
      exact hpτ i
    · have hz : ∑ i, a i • τ i ∉ tsupport (η : DifferentialForm (Eucl P) (m + 1)) := fun hz =>
        ha (by simpa only [mem_preimage, hpι] using hηt hz)
      simp only [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport ha,
        ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  -- `c ∫_Q η(τ) dHⁿ = c ∫ η(∑ aᵢ τᵢ)(τ) da = c ∫ ω(a)(e) da = c ∫_{B₁(0)} ω(e) dx = S(ω)`.
  have hV : ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
      (fun i => EuclideanSpace.single i (1 : ℝ)) =
      ∫ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) := fun h => hx (hωV h)
    simp only [image_eq_zero_of_notMem_tsupport hx', ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply]
  have hlim : c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)),
      (η : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P)) = S ω := by
    rw [hS ω, hV, (Submission.ind_pi_span_integral P (m + 1) τ hτ).1]
    simp only [hηQ]
  -- 8. `S′_k(ω) = Z_k(η) → S(ω)`.
  have h := hZlim η
  rw [hlim] at h
  exact h.congr fun k => (hact k).symm
/-- An orthonormal `n`-frame in `ℝⁿ` has simple `n`-vector `±e₁ ∧ ⋯ ∧ eₙ` (Simon Ch. 6, 3.1 in top
dimension: an orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` is `±e₁ ∧ ⋯ ∧ eₙ`, so `⟨ω, ξ⟩ = ±a` for
`ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, as in the proof of 8.2, p. 179).  `τ` is linearly independent with
`n = dim ℝⁿ` members, hence an orthonormal basis of `ℝⁿ`, as is the standard basis `e`.  An
`n`-covector `α` is an alternating `n`-form on `ℝⁿ`, so `α(τ) = α(e) det_e(τ)`
(`AlternatingMap.eq_smul_basis_det`), and `det_e(τ) = ±1` because the change of basis between
orthonormal bases is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.ind_top_orthonormal_frame_sign :
    ∀ (n : ℕ) (τ : Fin n → Eucl n), Orthonormal ℝ τ →
      simpleNVector τ = simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) ∨
        simpleNVector τ = -simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro n τ hτ
  -- Step 1: `τ` spans `ℝⁿ` (`n = 0` included).
  have hspan : Submodule.span ℝ (range τ) = ⊤ :=
    hτ.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  -- Step 2: `τ` and the standard basis `e` are orthonormal bases `bτ`, `be` of `ℝⁿ`.
  let bτ : OrthonormalBasis (Fin n) ℝ (Eucl n) := OrthonormalBasis.mk hτ hspan.ge
  let be : OrthonormalBasis (Fin n) ℝ (Eucl n) := EuclideanSpace.basisFun (Fin n) ℝ
  have hbτ : ⇑bτ = τ := OrthonormalBasis.coe_mk hτ hspan.ge
  have hbe : ⇑be.toBasis = fun i => EuclideanSpace.single i (1 : ℝ) := by
    funext i
    simp [be]
  -- Step 3: `det_e(τ) = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : be.toBasis.det τ = 1 ∨ be.toBasis.det τ = -1 := by
    simpa only [hbτ] using be.det_to_matrix_orthonormalBasis_real bτ
  -- Step 4: an `n`-covector `α` is `α(e) • det_e`, so `α(τ) = α(e) * det_e(τ)`.
  have key : ∀ α : Covector (Eucl n) n,
      α τ = α (fun i => EuclideanSpace.single i (1 : ℝ)) * be.toBasis.det τ := by
    intro α
    have h := DFunLike.congr_fun (α.toAlternatingMap.eq_smul_basis_det be.toBasis) τ
    rw [AlternatingMap.smul_apply, smul_eq_mul, hbe] at h
    exact h
  -- Step 5: extensionality, as `simpleNVector v α = α v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun α => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key α, hd, mul_one]
  · right
    refine ContinuousLinearMap.ext fun α => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key α, hd, mul_neg_one]
/-- Densities of top-degree test-form functionals on an open set are unique a.e. (Simon Ch. 6, end
of the Proof of 8.2, p. 179: `θ ≡ θ(x)` in `B₁ⁿ(0)`, top-dimensional currents acting by
`ω = a dx¹ ∧ ⋯ ∧ dxⁿ ↦ ∫ a θ dLⁿ` as in 2.35 (∗)).  For `a ∈ C_c^∞(U)`, the form `ω = a • vol`
with `vol = dx¹ ∧ ⋯ ∧ dxⁿ` is a test form on `U` with `ω(x)(e₁, …, eₙ) = a(x)`
(`wedgeCovectors_apply_det`: `vol(e) = det 1 = 1`), so the hypothesis gives
`∫ a (u - v) = ∫_U u a - ∫_U v a = 0`.  As `u - v` is locally integrable on the open set `U`, the
fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `u = v` a.e. on `U`. -/
theorem Submission.ind_top_form_density_ae_unique :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (u v : Eucl (m + 1) → ℝ), IsOpen U →
      (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) →
      (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn v K volume) →
      (∀ ω : TestFormOn U (m + 1),
        ∫ x in U, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume =
        ∫ x in U, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) →
      ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x = v x := by
  intro m U u v hU hu hv h
  -- Step 1: the volume covector `vol = dx¹ ∧ ⋯ ∧ dxⁿ` has `vol(e) = det 1 = 1`.
  obtain ⟨vol, hvol⟩ : ∃ vol : Covector (Eucl (m + 1)) (m + 1),
      vol (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), ?_⟩
    rw [wedgeCovectors_apply_det]
    have hI : (Matrix.of fun i j =>
        (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ) (EuclideanSpace.single j (1 : ℝ))) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    rw [hI, Matrix.det_one]
  -- Step 2: `u - v` is integrable on compact subsets of the open set `U`, so it is locally
  -- integrable on `U`.
  have hloc : LocallyIntegrableOn (fun x => u x - v x) U volume := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    exact (hu K hK hKU).sub (hv K hK hKU)
  -- Step 3: the fundamental lemma; it remains to show `∫ a • (u - v) = 0` for `a ∈ C_c^∞(U)`.
  have key : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x - v x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun a ha ha_cs ha_sub => ?_
    -- Step 4: `ω = a • vol` is a test form on `U` with `ω(x)(e) = a(x)`.
    let ω : TestFormOn U (m + 1) :=
      ⟨fun x => a x • vol,
        ⟨⟨ha.smul contDiff_const, ha_cs.smul_right⟩,
          (tsupport_smul_subset_left _ _).trans ha_sub⟩⟩
    have hω : ∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) = a x := by
      intro x
      simp [ω, hvol]
    -- Step 5: the hypothesis for `ω` reads `∫_U u a = ∫_U v a`.
    have hua := h ω
    simp only [hω] at hua
    -- Step 6: `w a` is integrable for `w ∈ {u, v}`: it is integrable on the compact set
    -- `tsupport a ⊆ U` and vanishes outside it.
    have hK : IsCompact (tsupport a) := ha_cs
    have hint : ∀ w : Eucl (m + 1) → ℝ,
        (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn w K volume) →
        IntegrableOn (fun x => w x * a x) U volume := by
      intro w hw
      have h1 : IntegrableOn (fun x => w x * a x) (tsupport a) volume :=
        (hw _ hK ha_sub).mul_continuousOn ha.continuous.continuousOn hK
      have h2 : Integrable (fun x => w x * a x) volume := by
        rw [← integrableOn_iff_integrable_of_support_subset]
        · exact h1
        · intro x hx
          apply subset_tsupport
          intro hax
          apply hx
          simp [hax]
      exact h2.integrableOn
    -- Step 7: `a = 0` off `U`, so `∫ a • (u - v) = ∫_U u a - ∫_U v a = 0`.
    have hzero : ∀ x, x ∉ U → a x • (u x - v x) = 0 := by
      intro x hx
      have : a x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (ha_sub hx'))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hsplit : ∀ x, a x • (u x - v x) = u x * a x - v x * a x := by
      intro x
      simp only [smul_eq_mul]
      ring
    simp only [hsplit]
    rw [integral_sub (hint u hu) (hint v hv), hua, sub_self]
  -- Step 8: conclusion.
  filter_upwards [key] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-- A top-dimensional integer multiplicity current has an integer density (Simon Ch. 6, 2.35 (∗),
`T(ω) = ∫ aθ dLⁿ` for `ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, with `θ` integer-valued as at the end of the Proof of
8.2, p. 179).  Write `X = τ(M, θ, ξ)` in `U ⊆ ℝⁿ`, `n = m + 1`, and `e = (e₁, …, eₙ)`; on `ℝⁿ`,
`Hⁿ = μHE[n]` is Lebesgue measure.  By `Submission.ind_top_orthonormal_frame_sign`,
`ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`, so `ξ(x)(α) = σ(x) α(e)` with the sign
`σ(x) = ξ(x)(dx¹ ∧ ⋯ ∧ dxⁿ) = ±1`.  The density is `u = θσ` on `M` and `u = 0` off `M`. -/
theorem Submission.ind_top_dim_integer_density :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (X : GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity X → ∃ u : Eucl (m + 1) → ℝ,
        (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∃ k : ℤ, u x = k) ∧
        (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) ∧
        ∀ ω : TestFormOn U (m + 1), X ω = ∫ x in U, u x *
          (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
            (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume := by
  intro m U X hX
  -- Step 1: `X = τ(M, θ, ξ)` with `θ` integer-valued on `M`; `μHE[m + 1]` is `volume`.
  obtain ⟨M, θ, ξ, hT, hθ, hXω⟩ := hX
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  have hM : NullMeasurableSet M volume := by
    simpa only [hvol] using hT.nullMeasurableSet
  have hξ : AEStronglyMeasurable ξ (volume.restrict M) := by
    simpa only [hvol] using hT.aestronglyMeasurable
  have horients := hT.orients
  rw [hvol] at horients
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- Step 2: the volume covector `vol = dx¹ ∧ ⋯ ∧ dxⁿ` has `vol(e) = det 1 = 1`.
  set vol : Covector (Eucl (m + 1)) (m + 1) :=
    wedgeCovectors (m + 1) fun j => EuclideanSpace.proj j with hvol_def
  have hvol_e : vol e = 1 := by
    rw [hvol_def, wedgeCovectors_apply_det]
    convert Matrix.det_one (n := Fin (m + 1)) (R := ℝ)
    ext i j
    simp [he, Matrix.one_apply]
  -- Step 3: `ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`.
  have hsign : ∀ᵐ x ∂volume.restrict M, ξ x = simpleNVector e ∨ ξ x = -simpleNVector e := by
    filter_upwards [horients] with x hx
    obtain ⟨τ, hτ, -, hξτ⟩ := hx
    rcases Submission.ind_top_orthonormal_frame_sign (m + 1) τ hτ with h | h <;>
      rcases hξτ with hξτ | hξτ
    · exact Or.inl (hξτ.trans h)
    · exact Or.inr (by rw [hξτ, h])
    · exact Or.inr (hξτ.trans h)
    · refine Or.inl (ContinuousLinearMap.ext fun α => ?_)
      rw [hξτ, _root_.neg_apply, h, _root_.neg_apply, neg_neg]
  -- Step 4: the sign `σ(x) = ξ(x)(vol)`; a.e. on `M`, `σ = ±1` and `ξ(x)(α) = σ(x) α(e)`.
  set σ : Eucl (m + 1) → ℝ := fun x => ξ x vol
  have hσm : AEStronglyMeasurable σ (volume.restrict M) :=
    (continuous_eval_const vol).comp_aestronglyMeasurable hξ
  have hσ : ∀ᵐ x ∂volume.restrict M, (σ x = 1 ∨ σ x = -1) ∧
      ∀ α : Covector (Eucl (m + 1)) (m + 1), ξ x α = σ x * α e := by
    filter_upwards [hsign] with x hx
    rcases hx with hx | hx
    · have h1 : σ x = 1 := by
        show ξ x vol = 1
        rw [hx, simpleNVector_apply, hvol_e]
      exact ⟨Or.inl h1, fun α => by rw [h1, one_mul, hx, simpleNVector_apply]⟩
    · have h1 : σ x = -1 := by
        show ξ x vol = -1
        rw [hx, _root_.neg_apply, simpleNVector_apply, hvol_e]
      exact ⟨Or.inr h1, fun α => by
        rw [h1, neg_one_mul, hx, _root_.neg_apply, simpleNVector_apply]⟩
  -- Step 5: `u = θσ` on `M` and `u = 0` off `M`.
  refine ⟨M.indicator fun x => θ x * σ x, ?_, ?_, ?_⟩
  · -- Step 6: `u` is integer-valued a.e.
    filter_upwards [(ae_restrict_iff'₀ hM).1 hσ] with x hx
    by_cases hxM : x ∈ M
    · obtain ⟨k, hk⟩ := hθ x hxM
      rcases (hx hxM).1 with h1 | h1
      · exact ⟨k, by simp [Set.indicator_of_mem hxM, hk, h1]⟩
      · exact ⟨-k, by simp [Set.indicator_of_mem hxM, hk, h1]⟩
    · exact ⟨0, by simp [Set.indicator_of_notMem hxM]⟩
  · -- Step 7: `θ` is integrable on `M ∩ K` and `|σ| ≤ 1`, so `u` is integrable on `K`.
    intro K hK hKU
    rw [integrableOn_indicator_iff hM]
    have hθK : IntegrableOn θ (M ∩ K) volume := by
      simpa only [hvol] using hT.integrableOn K hK hKU
    refine Integrable.mul_bdd (c := 1) hθK
      (hσm.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Set.inter_subset_left : M ∩ K ⊆ M) hσ] with x hx
    rcases hx.1 with h1 | h1 <;> simp [h1]
  · -- Step 8: `X(ω) = ∫_M θσ ω(e) dx = ∫_U u ω(e) dx`.
    intro ω
    have hMU : NullMeasurableSet M (volume.restrict U) := hM.mono Measure.restrict_le_self
    rw [hXω ω, tauAction, hvol]
    calc ∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) ∂volume
        = ∫ x in M, θ x * σ x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hσ] with x hx
          rw [hx.2]
          ring
      _ = ∫ x in U, M.indicator (fun x =>
            θ x * σ x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e) x ∂volume := by
          rw [integral_indicator₀ hMU, Measure.restrict_restrict₀ hMU,
            Set.inter_eq_left.2 hT.subset]
      _ = ∫ x in U, M.indicator (fun x => θ x * σ x) x *
            (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e ∂volume := by
          congr 1
          funext x
          by_cases hx : x ∈ M <;> simp [hx]

/-- A constant multiple `c [[U]]` of a nonempty open `U ⊆ ℝⁿ` is integer multiplicity only if
`c ∈ ℤ` (Simon Ch. 6, end of the proof of 8.2, p. 179: "`θ ≡ θ(x)` in `B₁ⁿ(0)`; thus
`θ(x) ∈ ℤ`").  An integer multiplicity `X ∈ 𝒟ₙ(U)` acts as `X(ω) = ∫_U u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`
with `u` a.e. integer-valued and integrable on compact subsets of `U`; the constant `c` is a
second such density of `X`, so `c = u` a.e. on `U`, and `Lⁿ(U) > 0`. -/
theorem Submission.ind_const_multiple_integer :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (c : ℝ) (X : GeometricCurrentOn U (m + 1)), IsOpen U →
      U.Nonempty → IsIntegerMultiplicity X →
      (∀ ω : TestFormOn U (m + 1),
        X ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ k : ℤ, c = k := by
  intro m U c X hU hne hX hXc
  -- `X(ω) = ∫_U u ω(e) dx` with `u` a.e. integer-valued and integrable on compacts of `U`.
  obtain ⟨u, hu_int, hu_loc, hu_rep⟩ := Submission.ind_top_dim_integer_density m U X hX
  -- The constant `c` is another density of `X`, hence `c = u` a.e. on `U`.
  have hcu : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → c = u x :=
    Submission.ind_top_form_density_ae_unique m U (fun _ => c) u hU
      (fun K hK _ => integrableOn_const hK.measure_ne_top) hu_loc
      (fun ω => by rw [integral_const_mul, ← hXc]; exact hu_rep ω)
  -- If `c ∉ ℤ`, a.e. point lies outside `U`, contradicting `Lⁿ(U) > 0` for open `U ≠ ∅`.
  by_contra hc
  have hnull : (volume : Measure (Eucl (m + 1))) U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcu, hu_int] with x hx ⟨k, hk⟩ hxU
    exact hc ⟨k, (hx hxU).trans hk⟩
  exact (hU.measure_pos volume hne).ne' hnull

/-- **Integrality of a planar weak limit of integer multiplicity cycles** (Simon Ch. 6, Proof of
8.2, displays (8)–(10), and Remark 3.12).  Let `Q = span τ` be the `(m + 1)`-plane spanned by an
orthonormal `τ`, and let `Y_k` be integer multiplicity cycles with `sup_k M_{B_2(0)}(Y_k) < ∞` and
`Y_k ⇀ c[[Q]]` on forms supported in `B_2(0)`.  Then `c ∈ ℤ`.  Take the coordinates
`p(y) = (⟪τ_i, y⟫)_i` and the distance `d` to `Q`.  Slicing by `d` localizes the `Y_k` to integer
multiplicity currents `Z_k` with bounded mass and boundary mass on the cylinder
`{|p| < 1, d < 3/4}` (`ind_pi_localized_cycles`).  Their push-forwards by `p` converge weakly to
`c[[B_1(0)]]` in `ℝ^{m+1}` (`ind_pi_projected_limit`).  So `c[[B_1(0)]]` is integer multiplicity by
the top-dimensional case of 8.2, and `c ∈ ℤ` (`ind_const_multiple_integer`). -/
theorem Submission.ind_plane_multiplicity_integer : SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P)) (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U → (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k), (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) → IsRestriction X {x | x ∈ U ∧ φ x < s} R → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K → WeaklyConvergesOn Rj R)) → (LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) → (∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c : ℝ) (Y : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), Orthonormal ℝ τ → (∀ k, IsIntegerMultiplicity (Y k)) → (∀ k, (Y k).boundary = 0) → (⨆ k, (Y k).massOn (ball (0 : Eucl P) 2)) < ∞ → (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ ball (0 : Eucl P) 2 → Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → ∃ k : ℤ, c = k := by
  intro hST hLPF hRWL hSPF hTOP P m τ c Y hτ hYim hYbd hYmass hYlim
  -- Coordinates `p(y) = (⟪τ_i, y⟫)_i` with respect to `τ`, and the distance `d` to `Q = span τ`.
  obtain ⟨p, hp⟩ : ∃ p : Eucl P →L[ℝ] Eucl (m + 1), ∀ y i, p y i = inner ℝ (τ i) y :=
    ⟨(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun i => innerSL ℝ (τ i), fun y i => by simp⟩
  obtain ⟨d, hd⟩ : ∃ d : Eucl P → ℝ, ∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖ :=
    ⟨_, fun _ => rfl⟩
  -- Steps 1–7 (printed (8)–(9)): slicing by `d` localizes the `Y_k` to the cylinder.
  obtain ⟨γ, Z, hγ0, hγ, hZim, hZsupp, hZmass, hZlim⟩ :=
    Submission.ind_pi_localized_cycles hST hRWL P m τ c Y p d hτ hp hd hYim hYbd hYmass hYlim
  -- The current `S = c[[B_1(0)]]` in `ℝ^{m+1}`, represented by `(Lᵐ⁺¹ ⌞ B_1(0), c e₁ ∧ ⋯ ∧ eₘ₊₁)`.
  obtain ⟨S, hS⟩ := Submission.ind_pi_constant_vector_current (m + 1) (m + 1)
    (ball (0 : Eucl (m + 1)) 1) (volume.restrict (ball (0 : Eucl (m + 1)) 1))
    (c • simpleNVector fun i => EuclideanSpace.single i (1 : ℝ))
    fun K hK => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top
  have hSval : ∀ ω : TestFormOn (ball (0 : Eucl (m + 1)) 1) (m + 1), S ω =
      c * ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume := by
    intro ω
    rw [(hS ω).2, ← integral_const_mul]
    simp only [smul_apply, simpleNVector_apply, smul_eq_mul]
  -- Steps 8–9 (printed (10)): the push-forwards `p_# Z_k` converge weakly to `S`.
  obtain ⟨S', hS'im, hS'mass, hS'conv⟩ := Submission.ind_pi_projected_limit hLPF hSPF P m τ c γ
    p d Z S hτ hp hd hγ0 hγ hZim hZsupp hZmass hZlim hSval
  -- Step 10 (Remark 3.12): by the top-dimensional case of 8.2, `S` is integer multiplicity.
  have hSim : IsIntegerMultiplicity S :=
    hTOP m (ball (0 : Eucl (m + 1)) 1) isOpen_ball S' S hS'im hS'mass hS'conv
  -- Step 11: an integer multiplicity `c[[B_1(0)]]` has `c ∈ ℤ`.
  exact Submission.ind_const_multiple_integer m (ball (0 : Eucl (m + 1)) 1) c S isOpen_ball
    ⟨0, mem_ball_self one_pos⟩ hSim hSval

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
