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

/-- Integrals over a lattice face as integrals over the parameter cube: for every `g`,
`∫_{latticeFace ρ G} g dHᵈ = ∫_{[0,ρ]^d} g(∑_l ρ w_l e_l + ∑_j s_j e_{γ(j)}) ds`, `G = (w, γ)`.
The map `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` is an isometry (`(e_{γ(j)})_j` is orthonormal)
whose range contains the face, so `L_* Hᵈ = Hᵈ ⌞ range L` and the integral is pulled back along
`L` and then along the volume-preserving `toLp : (Fin d → ℝ) → ℝᵈ`; the face pulls back to
`[0,ρ]^d`. -/
theorem Submission.br_latticeFace_setIntegral_eq_cube :
    ∀ (P d : ℕ) (ρ : ℝ) (G : LatticeFaceIndex d P) (g : Eucl P → ℝ),
      ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P)) =
        ∫ s in Set.Icc (0 : Fin d → ℝ) (fun _ => ρ),
          g (∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (G.2 j) (1 : ℝ)) := by
  intro P d ρ G g
  -- The parametrization `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` of the face.
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin d) → Eucl P, ∀ t, L t =
      ∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
        ∑ j, t j • EuclideanSpace.single (G.2 j) (1 : ℝ) := ⟨_, fun _ => rfl⟩
  -- Coordinates: `L(t)_{γ(j)} = ρ w_{γ(j)} + t_j` and `L(t)_l = ρ w_l` for `l ∉ range γ`.
  have hcoord : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P),
      L t l = ρ * (G.1 l : ℝ) + ∑ j, if l = G.2 j then t j else 0 := by
    intro t l
    rw [hL]
    simp [Pi.single_apply]
  have hcoord₁ : ∀ (t : EuclideanSpace ℝ (Fin d)) (j : Fin d),
      L t (G.2 j) = ρ * (G.1 (G.2 j) : ℝ) + t j := by
    intro t j
    rw [hcoord]
    simp
  have hcoord₂ : ∀ (t : EuclideanSpace ℝ (Fin d)) (l : Fin P), l ∉ Set.range G.2 →
      L t l = ρ * (G.1 l : ℝ) := by
    intro t l hl
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hl ⟨j, h.symm⟩
  -- `L` is an isometry because `(e_{γ(j)})_j` is orthonormal.
  have hv : Orthonormal ℝ (fun j => EuclideanSpace.single (G.2 j) (1 : ℝ)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).comp _ G.2.injective
  have hiso : Isometry L := by
    refine Isometry.of_dist_eq fun t t' => ?_
    have hdiff : L t - L t' = ∑ j, (t j - t' j) • EuclideanSpace.single (G.2 j) (1 : ℝ) := by
      rw [hL, hL]
      simp [sub_smul, Finset.sum_sub_distrib]
    have h2 : ‖L t - L t'‖ ^ 2 = ‖t - t'‖ ^ 2 := by
      rw [hdiff, ← real_inner_self_eq_norm_sq, hv.inner_sum, EuclideanSpace.norm_sq_eq]
      simp [sq]
    rw [dist_eq_norm, dist_eq_norm]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  -- The face lies in the range of `L`.
  have hrange : latticeFace ρ G ⊆ Set.range L := by
    intro x hx
    refine ⟨WithLp.toLp 2 (fun j => x (G.2 j) - ρ * (G.1 (G.2 j) : ℝ)), PiLp.ext fun l => ?_⟩
    by_cases hl : l ∈ Set.range G.2
    · obtain ⟨j, rfl⟩ := hl
      rw [hcoord₁]
      simp
    · rw [hcoord₂ _ _ hl]
      exact ((hx l).2 hl).symm
  -- The face pulls back to the cube `[0,ρ]^d` of parameters.
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      (L ⁻¹' latticeFace ρ G) = Set.Icc 0 (fun _ => ρ) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).1
        rw [hcoord₁] at this
        simp only [Pi.zero_apply]
        linarith
      · have := ((h (G.2 j)).1 ⟨j, rfl⟩).2
        rw [hcoord₁] at this
        linarith
    · rintro ⟨h0, h1⟩ i
      refine ⟨?_, hcoord₂ _ i⟩
      rintro ⟨j, rfl⟩
      rw [hcoord₁]
      have h0j := h0 j
      have h1j := h1 j
      simp only [Pi.zero_apply] at h0j
      constructor <;> nlinarith
  -- `L_* Hᵈ = Hᵈ ⌞ range L`; change variables along `L`, then along `toLp`.
  calc ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P))
      = ∫ x in latticeFace ρ G, g x
          ∂((μHE[d] : Measure (EuclideanSpace ℝ (Fin d))).map L) := by
        rw [hiso.map_euclideanHausdorffMeasure, Measure.restrict_restrict_of_subset hrange]
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t)
          ∂(μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) :=
        hiso.isClosedEmbedding.setIntegral_map _
    _ = ∫ t in L ⁻¹' latticeFace ρ G, g (L t) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    _ = ∫ s in (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
          (L ⁻¹' latticeFace ρ G), g (L (WithLp.toLp 2 s)) :=
        ((PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
          (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
          (fun t => g (L t)) (L ⁻¹' latticeFace ρ G)).symm
    _ = _ := by
        rw [hpre]
        simp only [hL]
/-- Fubini and the fundamental theorem of calculus on the cube `[0,ρ]^{n+1}`: for `φ` of class
`C¹` and `e_i = Pi.single i 1`,
`∫_{[0,ρ]^{n+1}} Dφ(s)(e_i) ds = ∫_{[0,ρ]^n} (φ(insertNth_i(ρ, s')) - φ(insertNth_i(0, s'))) ds'`.
The measure-preserving map `(t, s') ↦ insertNth_i(t, s')` pulls the cube back to
`[0,ρ] × [0,ρ]^n`, Fubini puts the `t`-integral inside, and
`d/dt φ(insertNth_i(t, s')) = Dφ(insertNth_i(t, s'))(e_i)`. -/
theorem Submission.br_cube_integral_fderiv_eq_faces :
    ∀ (n : ℕ) (ρ : ℝ), 0 ≤ ρ → ∀ (φ : (Fin (n + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      ∀ (i : Fin (n + 1)),
        ∫ s in Set.Icc (0 : Fin (n + 1) → ℝ) (fun _ => ρ), fderiv ℝ φ s (Pi.single i 1) =
          ∫ s in Set.Icc (0 : Fin n → ℝ) (fun _ => ρ),
            (φ (Fin.insertNth i ρ s) - φ (Fin.insertNth i 0 s)) := by
  intro n ρ hρ φ hφ i
  -- `g(s) = Dφ(s)(e_i)` is continuous.
  have hg : Continuous fun s => fderiv ℝ φ s (Pi.single i 1) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- `(t, s') ↦ insertNth_i(t, s')` is measure preserving and pulls `[0,ρ]^{n+1}` back to
  -- `[0,ρ] × [0,ρ]^n` (as in Mathlib's `torusIntegral_succAbove`).
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have heI : (e ⁻¹' Set.Icc 0 fun _ => ρ) =
      Set.Icc 0 ρ ×ˢ Set.Icc (0 : Fin n → ℝ) fun _ => ρ :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) i).preimage_Icc _ _).trans (Set.Icc_prod_eq _ _)
  have hint : Integrable (fun z => fderiv ℝ φ (e z) (Pi.single i 1))
      ((volume.restrict (Set.Icc (0 : ℝ) ρ)).prod
        (volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => ρ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hg.comp (continuous_fst.finInsertNth i continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← hem.map_eq, setIntegral_map_equiv, heI, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ hint]
  -- Fundamental theorem of calculus in the `i`-th coordinate, for each `s'`.
  congr 1
  funext y
  have hcurve : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (Fin.insertNth i t y : Fin (n + 1) → ℝ)) (Pi.single i 1) t := by
    intro t
    refine hasDerivAt_pi.2 fun j => ?_
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
      exact hasDerivAt_id' t
    · simp only [Fin.insertNth_apply_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne _ k)]
      exact hasDerivAt_const t (y k)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (Fin.insertNth i t y))
      (fderiv ℝ φ (Fin.insertNth i t y) (Pi.single i 1)) t := fun t =>
    ((hφ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hcurve t)
  have hcont : Continuous fun t : ℝ => fderiv ℝ φ (Fin.insertNth i t y) (Pi.single i 1) :=
    hg.comp (continuous_iff_continuousAt.2 fun t => (hcurve t).continuousAt)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hρ]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 ρ)

/-- Stokes' theorem on the parameter cube of the lattice face `ρ (z + F_α)`, `F = (z, α)`.  Put
`p = ρ z`, `v_j = e_{α j}`, `A(s) = p + ∑_j s_j v_j` and `α_i = α ∘ succAbove_i`; then
`∫_{[0,ρ]^{m+1}} dω(A(s))(v) ds` is the alternating sum over `i` of the integrals of `ω(·)(e_{α_i})`
over the faces `s_i = ρ` and `s_i = 0`, i.e. of
`∫_{[0,ρ]^m} ω(ρ (z + e_{α i}) + ∑_k s_k e_{α_i k})(e_{α_i})` minus
`∫_{[0,ρ]^m} ω(p + ∑_k s_k e_{α_i k})(e_{α_i})`.
By `exteriorDerivative_apply` and the chain rule, `dω(A(s))(v) = ∑_i (-1)^i Dφ_i(s)(e_i)` for
`φ_i(s) = ω(A(s))(removeNth_i v)`; `br_cube_integral_fderiv_eq_faces` integrates each term, and
`A(insertNth_i(t, s')) = p + t v_i + ∑_k s'_k e_{α_i k}` identifies the two faces. -/
theorem Submission.br_cube_stokes_lattice :
    ∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (F : LatticeFaceIndex (m + 1) P)
      (ω : DifferentialForm (Eucl P) m), IsSmoothForm ω →
      ∫ s in Set.Icc (0 : Fin (m + 1) → ℝ) (fun _ => ρ),
        exteriorDerivative ω (∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
          ∑ j, s j • EuclideanSpace.single (F.2 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) =
      ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
        ((∫ s in Set.Icc (0 : Fin m → ℝ) (fun _ => ρ),
          ω (∑ l, (ρ * (((F.1 + Pi.single (F.2 i) 1 : Fin P → ℤ) l : ℤ) : ℝ)) •
              EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j) (1 : ℝ))
            (fun j => EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j) (1 : ℝ))) -
        ∫ s in Set.Icc (0 : Fin m → ℝ) (fun _ => ρ),
          ω (∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
            ∑ j, s j • EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j) (1 : ℝ))
            (fun j => EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) j)
              (1 : ℝ))) := by
  intro P m ρ hρ F ω hω
  -- The base point `p = ρ z`, the frame `v j = e_{α j}` and `A s = p + ∑ j, s j • v j`.
  set p : Eucl P := ∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) with hp
  set v : Fin (m + 1) → Eucl P := fun j => EuclideanSpace.single (F.2 j) (1 : ℝ) with hv
  have hωd : Differentiable ℝ ω := hω.differentiable (by simp)
  -- `A` is affine with linear part `DA s = ∑ j, s j • v j`.
  let DA : (Fin (m + 1) → ℝ) →L[ℝ] Eucl P := ∑ j, (ContinuousLinearMap.proj j).smulRight (v j)
  have hDA : ∀ s, DA s = ∑ j, s j • v j := fun s => by simp [DA]
  have hAeq : (fun s : Fin (m + 1) → ℝ => p + ∑ j, s j • v j) = fun s => p + DA s := by
    funext s; rw [hDA]
  have hA : ∀ s, HasFDerivAt (fun s : Fin (m + 1) → ℝ => p + ∑ j, s j • v j) DA s := fun s => by
    rw [hAeq]
    exact DA.hasFDerivAt.const_add p
  -- `φ i s = ω (A s) (removeNth i v)` is `C¹`: evaluation at a fixed frame is continuous linear.
  set φ : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ :=
    fun i s => ω (p + ∑ j, s j • v j) (Fin.removeNth i v)
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := by
    intro i
    have h1 : ContDiff ℝ 1 (fun y => ω y (Fin.removeNth i v)) :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (Fin.removeNth i v)).contDiff.comp
        (hω.of_le (by simp))
    have h2 : ContDiff ℝ 1 (fun s : Fin (m + 1) → ℝ => p + ∑ j, s j • v j) := by
      rw [hAeq]
      exact contDiff_const.add DA.contDiff
    exact h1.comp h2
  -- Pointwise `dω(A s)(v) = ∑ i, (-1)^i Dφ_i(s)(e_i)`, by the chain rule and `DA e_i = v i`.
  have hpt : ∀ s : Fin (m + 1) → ℝ, exteriorDerivative ω (p + ∑ j, s j • v j) v =
      ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (φ i) s (Pi.single i 1) := by
    intro s
    rw [exteriorDerivative_apply (hωd _) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : HasFDerivAt (fun y => ω y (Fin.removeNth i v))
        (fderiv ℝ (fun y => ω y (Fin.removeNth i v)) (p + ∑ j, s j • v j))
        (p + ∑ j, s j • v j) :=
      ((hωd _).continuousAlternatingMap_apply_const _).hasFDerivAt
    have hφi : φ i = (fun y => ω y (Fin.removeNth i v)) ∘ (fun s => p + ∑ j, s j • v j) := rfl
    rw [hφi, (hc.comp s (hA s)).fderiv, ContinuousLinearMap.comp_apply, hDA]
    have hsum : ∑ j, (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ) j • v j = v i := by
      simp [Pi.single_apply]
    rw [hsum, zsmul_eq_mul]
    push_cast
    ring
  -- Integrate the finite sum of continuous functions over the cube term by term.
  have hcont : ∀ i, Continuous fun s => fderiv ℝ (φ i) s (Pi.single i 1) :=
    fun i => ((hφ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ i : Fin (m + 1), IntegrableOn
      (fun s => (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (φ i) s (Pi.single i 1))
      (Set.Icc (0 : Fin (m + 1) → ℝ) (fun _ => ρ)) :=
    fun i => (continuous_const.mul (hcont i)).continuousOn.integrableOn_compact isCompact_Icc
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ => hpt s),
    integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Fubini and the fundamental theorem of calculus in the `i`-th coordinate.
  rw [integral_const_mul, Submission.br_cube_integral_fderiv_eq_faces m ρ hρ.le (φ i) (hφ i) i]
  congr 1
  have hcI : ∀ c : ℝ, IntegrableOn (fun s' : Fin m → ℝ => φ i (Fin.insertNth i c s'))
      (Set.Icc 0 fun _ => ρ) := fun c =>
    ((hφ i).continuous.comp (continuous_const.finInsertNth i continuous_id)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  rw [integral_sub (hcI ρ) (hcI 0)]
  -- Identify the faces `s_i = ρ` and `s_i = 0`.
  have hA_ins : ∀ (c : ℝ) (s' : Fin m → ℝ),
      p + ∑ j, Fin.insertNth (α := fun _ => ℝ) i c s' j • v j =
        (p + c • v i) + ∑ k, s' k •
          EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) k) (1 : ℝ) := by
    intro c s'
    rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same, add_assoc]
    simp only [Fin.insertNth_apply_succAbove]
    rfl
  have hrem : Fin.removeNth i v =
      fun k => EuclideanSpace.single (((Fin.succAboveOrderEmb i).trans F.2) k) (1 : ℝ) := rfl
  have htop : ∑ l, (ρ * (((F.1 + Pi.single (F.2 i) 1 : Fin P → ℤ) l : ℤ) : ℝ)) •
      EuclideanSpace.single l (1 : ℝ) = p + ρ • v i := by
    simp only [Pi.add_apply, Int.cast_add, mul_add, add_smul, Finset.sum_add_distrib, hp, hv]
    congr 1
    rw [Finset.sum_eq_single (F.2 i)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  congr 1
  · refine setIntegral_congr_fun measurableSet_Icc fun s' _ => ?_
    simp only [φ, hA_ins, htop, hrem]
  · refine setIntegral_congr_fun measurableSet_Icc fun s' _ => ?_
    simp only [φ, hA_ins, hrem, zero_smul, add_zero]

/-- Stokes' theorem on a lattice face (Simon Ch. 6, §5 and the proof of 6.3): for
`F = (z, α) ∈ 𝓛ₘ₊₁(ρ)` and a smooth `m`-form `ω`,
`[[F]](dω) = ∑ᵢ (-1)ⁱ ([[(z + e_{α(i)}, α ∘ succAboveᵢ)]](ω) - [[(z, α ∘ succAboveᵢ)]](ω))`.
Every face integral is the integral over its parameter cube `[0, ρ]ᵈ`, and on the cube this is
Stokes' theorem (Fubini and the fundamental theorem of calculus). -/
theorem Submission.br_lattice_face_stokes :
    ∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (F : LatticeFaceIndex (m + 1) P)
      (ω : DifferentialForm (Eucl P) m), IsSmoothForm ω →
      latticeFaceAction ρ F (exteriorDerivative ω) =
        ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
          (latticeFaceAction ρ (F.1 + Pi.single (F.2 i) 1, (Fin.succAboveOrderEmb i).trans F.2) ω -
            latticeFaceAction ρ (F.1, (Fin.succAboveOrderEmb i).trans F.2) ω) := by
  intro P m ρ hρ F ω hω
  -- Both sides become integrals over parameter cubes: `[0, ρ]ᵐ⁺¹` for `F` and `[0, ρ]ᵐ` for
  -- the two faces opposite in direction `α(i)`.
  simp only [latticeFaceAction, Submission.br_latticeFace_setIntegral_eq_cube]
  exact Submission.br_cube_stokes_lattice P m ρ hρ F ω hω

theorem Submission.br_top_dim_lattice_approximation : ∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1) → ℤ) (Pk : ℕ → GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), (∀ k, 0 < ρ k) ∧ (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧ WeaklyConvergesOn Pk X ∧ (⨆ k, (Pk k).boundary.mass) < ∞ := by
  classical
  intro m X hX hXm hXb
  let _ : MeasureSpace (Eucl (m + 1)) := measureSpaceOfInnerProductSpace
  let _ : NormedAddCommGroup (Eucl (m + 1)) := inferInstance
  let _ : NormedSpace ℝ (Eucl (m + 1)) := inferInstance
  have hSMm : ∀ I : Fin m → Fin (m + 1), StrictMono I → ∃ k, I = Fin.succAbove k := by
    intro I hI
    obtain ⟨k, hk⟩ : ∃ k, k ∉ Set.range I := by
      by_contra hcon
      push Not at hcon
      have := Fintype.card_le_of_surjective I hcon
      simp at this
    choose J hJ using fun b => Fin.exists_succAbove_eq (fun hb : I b = k => hk ⟨b, hb⟩)
    have hJm : StrictMono J := fun a b hab => by
      have h := hI hab
      rw [← hJ a, ← hJ b] at h
      exact Fin.succAbove_lt_succAbove_iff.1 h
    refine ⟨k, funext fun b => ?_⟩
    rw [← hJ b, hJm.eq_id]; rfl
  have hCNm : ∀ κ : Covector (Eucl (m + 1)) m, covectorEuclideanNorm κ ≤
      Real.sqrt (∑ k : Fin (m + 1),
        (κ (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))) ^ 2) := by
    intro κ
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.image
      (fun k : Fin (m + 1) => (Fin.succAbove k : Fin m → Fin (m + 1)))) (fun I hI => ?_)
      (fun _ _ _ => sq_nonneg _)).trans ((Finset.sum_image_le_of_nonneg
        (fun _ _ => sq_nonneg _)).trans (le_of_eq ?_))
    · obtain ⟨k, rfl⟩ := hSMm I (Finset.mem_filter.1 hI).2
      exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
    · simp only [EuclideanSpace.basisFun_apply]
  have hCN1 : ∀ (κ : Covector (Eucl (m + 1)) m) (k : Fin (m + 1)),
      |κ (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))| ≤ covectorEuclideanNorm κ := by
    intro κ k
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun I : Fin m → Fin (m + 1) => if StrictMono I then
      (κ fun i => EuclideanSpace.basisFun (Fin (m + 1)) ℝ (I i)) ^ 2 else 0)
      (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ (Fin.succAbove k))
    simpa only [Fin.strictMono_succAbove, ite_true, EuclideanSpace.basisFun_apply] using this
  have hCNn : ∀ α : Covector (Eucl (m + 1)) (m + 1),
      covectorEuclideanNorm α = |α (fun i => EuclideanSpace.single i (1 : ℝ))| := by
    intro α
    unfold covectorEuclideanNorm
    rw [Finset.sum_eq_single (id : Fin (m + 1) → Fin (m + 1))]
    · simp only [strictMono_id, ite_true, EuclideanSpace.basisFun_apply, id, Real.sqrt_sq_eq_abs]
    · intro I _ hI; exact ite_eq_right_iff.2 fun h => absurd h.eq_id hI
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨Δ, hΔ, hΔe, hΔτ⟩ : ∃ Δ : Covector (Eucl (m + 1)) (m + 1),
      (∀ (α : Covector (Eucl (m + 1)) (m + 1)) v,
        α v = α (fun i => EuclideanSpace.single i (1 : ℝ)) * Δ v) ∧
      Δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 ∧
      ∀ τ : Fin (m + 1) → Eucl (m + 1), Orthonormal ℝ τ → Δ τ = 1 ∨ Δ τ = -1 := by
    have hdet : ∀ v, wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j) v =
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.det v := by
      intro v
      rw [wedgeCovectors_apply_det, Module.Basis.det_apply]
      congr 1
    have hb : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis =
        fun i => EuclideanSpace.single i (1 : ℝ) := by
      funext i; simp
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), fun α v => ?_, ?_,
      fun τ hτ => ?_⟩
    · have := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis α.toAlternatingMap)
      simp only [AlternatingMap.smul_apply, ContinuousAlternatingMap.coe_toAlternatingMap,
        smul_eq_mul, hb] at this
      rw [hdet]; exact this
    · rw [hdet, ← hb, Module.Basis.det_self]
    · rw [hdet]
      have hsp := hτ.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
      have := OrthonormalBasis.det_to_matrix_orthonormalBasis_real
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (OrthonormalBasis.mk hτ hsp.ge)
      rwa [OrthonormalBasis.coe_mk] at this
  have hDL : ∀ i k : Fin (m + 1), wedgeCovectors m (fun j => EuclideanSpace.proj (Fin.succAbove i j))
      (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ)) = if i = k then 1 else 0 := by
    intro i k
    rw [wedgeCovectors_apply_det]
    split_ifs with hik
    · subst hik
      convert Matrix.det_one (n := Fin m) (R := ℝ)
      ext a c
      simp [Matrix.one_apply]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
      refine Matrix.det_eq_zero_of_row_eq_zero z fun c => ?_
      simp [hz, Ne.symm (Fin.succAbove_ne k c)]
  have hκ : ∀ v : Eucl (m + 1), ∃ κ : Covector (Eucl (m + 1)) m, ∀ k : Fin (m + 1),
      κ (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ)) = (-1 : ℝ) ^ (k : ℕ) * v k := by
    intro v
    refine ⟨∑ i : Fin (m + 1), ((-1 : ℝ) ^ (i : ℕ) * v i) •
      wedgeCovectors m (fun j => EuclideanSpace.proj (Fin.succAbove i j)), fun k => ?_⟩
    simp [hDL]
  have he : ∏ i : Fin (m + 1), ‖(EuclideanSpace.single i (1 : ℝ) : Eucl (m + 1))‖ = 1 := by
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one]
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, X.boundary.mass.toReal = Mb := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := hMb ▸ ENNReal.toReal_nonneg
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  obtain ⟨u, hu_meas, hu_Z, hu_loc, hE1⟩ : ∃ u : Eucl (m + 1) → ℝ, Measurable u ∧
      (∀ x, ∃ k : ℤ, u x = k) ∧ (∀ K, IsCompact K → IntegrableOn u K volume) ∧
      ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1),
        X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    obtain ⟨M, θ, ξ, hT, hθ, hXT⟩ := hX
    obtain ⟨M', hM'M, hM'm, hM'ae⟩ :=
      (hvol ▸ hT.nullMeasurableSet : NullMeasurableSet M volume).exists_measurable_subset_ae_eq
    have hrM : volume.restrict M' = volume.restrict M := Measure.restrict_congr_set hM'ae
    have hor : ∀ᵐ x ∂(volume.restrict M'), ξ x Δ = 1 ∨ ξ x Δ = -1 := by
      have h := hT.orients
      rw [hvol, ← hrM] at h
      filter_upwards [h] with x hx
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      rcases hξ with h | h <;> rw [h]
      · exact hΔτ τ hτ
      · rcases hΔτ τ hτ with h' | h' <;> simp [h']
    have hθm : AEStronglyMeasurable θ (volume.restrict M') := by
      have hU : M' = ⋃ k : ℕ, M' ∩ closedBall 0 k := by
        rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
      rw [hU, aestronglyMeasurable_iUnion_iff]
      intro k
      have h := hT.integrableOn _ (isCompact_closedBall 0 k) (subset_univ _)
      rw [hvol] at h
      exact (h.mono_set (inter_subset_inter_left _ hM'M)).1
    have hsm : AEStronglyMeasurable (fun x => ξ x Δ) (volume.restrict M') := by
      have h := hT.aestronglyMeasurable
      rw [hvol, ← hrM] at h
      exact (ContinuousLinearMap.apply ℝ ℝ Δ).continuous.comp_aestronglyMeasurable h
    have hu₀m : AEStronglyMeasurable (M'.indicator (fun x => θ x * ξ x Δ)) volume :=
      (aestronglyMeasurable_indicator_iff hM'm).2 (hθm.mul hsm)
    have hu₀Z : ∀ᵐ x ∂volume, M'.indicator (fun x => θ x * ξ x Δ) x ∈
        Set.range (Int.cast : ℤ → ℝ) := by
      filter_upwards [(ae_restrict_iff' hM'm).1 hor] with x hx
      by_cases hxM : x ∈ M'
      · rw [indicator_of_mem hxM]
        obtain ⟨k, hk⟩ := hθ x (hM'M hxM)
        rcases hx hxM with h1 | h1 <;> rw [h1, hk]
        · exact ⟨k, by simp⟩
        · exact ⟨-k, by simp⟩
      · rw [indicator_of_notMem hxM]; exact ⟨0, by simp⟩
    have hũm : Measurable (hu₀m.mk _) := hu₀m.stronglyMeasurable_mk.measurable
    have hu_ae : (fun x => if hu₀m.mk _ x ∈ Set.range (Int.cast : ℤ → ℝ) then hu₀m.mk _ x
        else 0) =ᵐ[volume] M'.indicator (fun x => θ x * ξ x Δ) := by
      filter_upwards [hu₀m.ae_eq_mk, hu₀Z] with x h1 h2
      rw [← h1]; simp only [h2, ite_true]
    refine ⟨fun x => if hu₀m.mk _ x ∈ Set.range (Int.cast : ℤ → ℝ) then hu₀m.mk _ x else 0,
      Measurable.ite (hũm (Set.countable_range _).measurableSet) hũm measurable_const,
      fun x => ?_, fun K hK => ?_, fun ω => ?_⟩
    · dsimp only; split_ifs with h
      · obtain ⟨k, hk⟩ := h; exact ⟨k, hk.symm⟩
      · exact ⟨0, by simp⟩
    · refine IntegrableOn.congr_fun_ae ?_ (ae_restrict_of_ae hu_ae.symm)
      rw [IntegrableOn, integrable_indicator_iff hM'm, IntegrableOn,
        Measure.restrict_restrict hM'm]
      have h := hT.integrableOn K hK (subset_univ _)
      rw [hvol] at h
      refine (h.mono_set (inter_subset_inter_left _ hM'M)).mul_bdd
        (hsm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) ?_ (c := 1)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hor] with x hx
      rcases hx with hx | hx <;> simp [hx]
    · rw [hXT ω]
      unfold tauAction
      rw [hvol, ← hrM, ← integral_indicator hM'm]
      refine integral_congr_ae ?_
      filter_upwards [hu_ae] with x hx
      rw [hx]
      by_cases hxM : x ∈ M'
      · rw [indicator_of_mem hxM, indicator_of_mem hxM]
        have h : ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) =
            (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
              (fun i => EuclideanSpace.single i (1 : ℝ)) * ξ x Δ := by
          rw [← smul_eq_mul, ← map_smul]; congr 1; ext v
          rw [hΔ ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) v]; rfl
        rw [h]; ring
      · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, zero_mul]
  have dual : ∀ (w : Eucl (m + 1) → ℝ) (c : ℝ), Measurable w →
      (∀ K, IsCompact K → IntegrableOn w K volume) →
      (∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
          HasCompactSupport φ → (∀ x, |φ x| ≤ 1) → ∫ x, w x * φ x ≤ c) →
      ∫⁻ x, ‖w x‖ₑ ≤ ENNReal.ofReal c := by
    intro w c hw hloc H
    have stepA : ∀ K, IsCompact K → ∫⁻ x in K, ‖w x‖ₑ ≤ ENNReal.ofReal c := by
      intro K hK
      obtain ⟨W, hWo, hKW, -, hWc⟩ :=
        exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
      have hWL : W ⊆ closure W := subset_closure
      have hwL : IntegrableOn w (closure W) volume := hloc _ hWc
      let ν := (volume.restrict (closure W)).withDensity (fun x => ‖w x‖ₑ)
      have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hwL.2.ne
      -- smooth Urysohn approximation of `1_A` up to a set of small `ν`-measure
      have approx : ∀ A, MeasurableSet A → A ⊆ K → ∀ ε : ℝ, 0 < ε →
          ∃ ψ : Eucl (m + 1) → ℝ, ∃ S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
            (∀ x, ψ x ∈ Icc (0 : ℝ) 1) ∧ Function.support ψ ⊆ W ∧ MeasurableSet S ∧
            S ⊆ closure W ∧ (∀ x, |ψ x - A.indicator 1 x| ≤ S.indicator 1 x) ∧
            ∫ x in S, |w x| ≤ 2 * ε := by
        intro A hA hAK ε hε
        have hε' : ENNReal.ofReal ε ≠ 0 := by simpa using hε
        obtain ⟨F, hFA, hFc, hνF⟩ := hA.exists_isClosed_sdiff_lt (μ := ν) (measure_ne_top ν A) hε'
        obtain ⟨U, hAU, hUo, -, hνU⟩ := hA.exists_isOpen_sdiff_lt (μ := ν) (measure_ne_top ν A) hε'
        obtain ⟨ψ, hψd, hψr, hψs, hψ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
          (hUo.inter hWo) hFc (subset_inter (hFA.trans hAU) ((hFA.trans hAK).trans hKW))
        have hψI : ∀ x, ψ x ∈ Icc (0 : ℝ) 1 := fun x => hψr (mem_range_self x)
        have hSm : MeasurableSet ((U ∩ W) \ F) :=
          (hUo.inter hWo).measurableSet.diff hFc.measurableSet
        refine ⟨ψ, (U ∩ W) \ F, hψd, hψI, hψs.subset.trans inter_subset_right, hSm,
          fun x hx => hWL hx.1.2, fun x => ?_, ?_⟩
        · by_cases hxS : x ∈ (U ∩ W) \ F
          · rw [indicator_of_mem hxS, Pi.one_apply, abs_le]
            have := hψI x
            by_cases hxA : x ∈ A
            · rw [indicator_of_mem hxA, Pi.one_apply]; constructor <;> linarith [this.1, this.2]
            · rw [indicator_of_notMem hxA]; constructor <;> linarith [this.1, this.2]
          · rw [indicator_of_notMem hxS]
            by_cases hxF : x ∈ F
            · rw [(hψ1 x).1 hxF, indicator_of_mem (hFA hxF)]; simp
            · have hxUW : x ∉ U ∩ W := fun h => hxS ⟨h, hxF⟩
              have hψ0 : ψ x = 0 := by rw [← Function.notMem_support, hψs]; exact hxUW
              rw [hψ0, indicator_of_notMem (fun h => hxUW ⟨hAU h, hKW (hAK h)⟩)]; simp
        · have hνS : ν ((U ∩ W) \ F) = ∫⁻ x in (U ∩ W) \ F, ‖w x‖ₑ := by
            rw [withDensity_apply _ hSm, Measure.restrict_restrict hSm,
              inter_eq_left.2 (fun x hx => hWL hx.1.2)]
          have hle : ν ((U ∩ W) \ F) < ENNReal.ofReal (2 * ε) := by
            calc ν ((U ∩ W) \ F) ≤ ν ((U \ A) ∪ (A \ F)) := by
                  apply measure_mono
                  rintro x ⟨⟨hxU, -⟩, hxF⟩
                  by_cases hxA : x ∈ A
                  · exact Or.inr ⟨hxA, hxF⟩
                  · exact Or.inl ⟨hxU, hxA⟩
              _ ≤ ν (U \ A) + ν (A \ F) := measure_union_le _ _
              _ < ENNReal.ofReal ε + ENNReal.ofReal ε := ENNReal.add_lt_add hνU hνF
              _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε.le hε.le]; ring_nf
          have h1 := integral_norm_eq_lintegral_enorm (μ := volume.restrict ((U ∩ W) \ F))
            hw.aestronglyMeasurable
          simp only [Real.norm_eq_abs] at h1
          rw [h1, ← hνS]
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle.le
      have hAm : MeasurableSet (K ∩ {x | 0 < w x}) :=
        hK.measurableSet.inter (measurableSet_lt measurable_const hw)
      have hBm : MeasurableSet (K ∩ {x | w x < 0}) :=
        hK.measurableSet.inter (measurableSet_lt hw measurable_const)
      have hwK : IntegrableOn w K volume := hloc K hK
      have hId : ∀ x, w x * ((K ∩ {x | 0 < w x}).indicator 1 x - (K ∩ {x | w x < 0}).indicator 1 x)
          = K.indicator (fun x => |w x|) x := by
        intro x
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK]
          rcases lt_trichotomy (w x) 0 with h | h | h
          · rw [indicator_of_notMem (fun hx => absurd hx.2 (not_lt.2 h.le)),
              indicator_of_mem (show x ∈ K ∩ {x | w x < 0} from ⟨hxK, h⟩), abs_of_neg h]; simp
          · rw [h]; simp
          · rw [indicator_of_mem (show x ∈ K ∩ {x | 0 < w x} from ⟨hxK, h⟩),
              indicator_of_notMem (fun hx => absurd hx.2 (not_lt.2 h.le)), abs_of_pos h]; simp
        · rw [indicator_of_notMem hxK, indicator_of_notMem (fun hx => hxK hx.1),
            indicator_of_notMem (fun hx => hxK hx.1)]; simp
      have hIK : ∫ x in K, |w x| ≤ c := by
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨ψA, SA, hψAd, hψAI, hψAs, hSAm, hSAL, hψAS, hSAe⟩ :=
          approx _ hAm inter_subset_left (ε / 4) (by positivity)
        obtain ⟨ψB, SB, hψBd, hψBI, hψBs, hSBm, hSBL, hψBS, hSBe⟩ :=
          approx _ hBm inter_subset_left (ε / 4) (by positivity)
        have hφs : ∀ x, x ∉ W → ψA x - ψB x = 0 := by
          intro x hxW
          rw [Function.notMem_support.1 (fun h => hxW (hψAs h)),
            Function.notMem_support.1 (fun h => hxW (hψBs h)), sub_zero]
        have hφsupp : Function.support (fun x => ψA x - ψB x) ⊆ W :=
          fun x hx => by_contra fun hxW => hx (hφs x hxW)
        have hφ1 : ∀ x, |ψA x - ψB x| ≤ 1 := fun x => by
          have a := hψAI x; have b := hψBI x
          rw [abs_le]; constructor <;> linarith [a.1, a.2, b.1, b.2]
        have hH := H _ (hψAd.sub hψBd)
          (HasCompactSupport.of_support_subset_isCompact hWc (hφsupp.trans hWL)) hφ1
        have hint1 : Integrable (fun x => w x * (ψA x - ψB x)) volume := by
          refine ((show IntegrableOn (fun x => |w x|) (closure W) volume from hwL.abs).integrable_indicator
            isClosed_closure.measurableSet).mono'
            (hw.mul (hψAd.continuous.sub hψBd.continuous).measurable).aestronglyMeasurable
            (Eventually.of_forall fun x => ?_)
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem (hWL hxW), Real.norm_eq_abs, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hφ1 x)
          · rw [hφs x hxW, mul_zero, norm_zero]
            exact indicator_nonneg (fun _ _ => abs_nonneg _) _
        have hint2 : Integrable (fun x => w x * ((K ∩ {x | 0 < w x}).indicator 1 x -
            (K ∩ {x | w x < 0}).indicator 1 x)) volume := by
          simp_rw [hId]
          exact (show IntegrableOn (fun x => |w x|) K volume from hwK.abs).integrable_indicator
            hK.measurableSet
        have hintS : Integrable (fun x => SA.indicator (fun x => |w x|) x +
            SB.indicator (fun x => |w x|) x) volume :=
          ((show IntegrableOn (fun x => |w x|) SA volume from (hwL.mono_set hSAL).abs).integrable_indicator
            hSAm).add ((show IntegrableOn (fun x => |w x|) SB volume from
              (hwL.mono_set hSBL).abs).integrable_indicator hSBm)
        have m := integral_mono (hint2.sub hint1) hintS (fun x => by
          show w x * (_ - _) - w x * (ψA x - ψB x) ≤ _
          have e : w x * ((K ∩ {x | 0 < w x}).indicator 1 x - (K ∩ {x | w x < 0}).indicator 1 x) -
              w x * (ψA x - ψB x) = w x * (-(ψA x - (K ∩ {x | 0 < w x}).indicator 1 x) +
              (ψB x - (K ∩ {x | w x < 0}).indicator 1 x)) := by ring
          rw [e]
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          calc |w x| * |-(ψA x - (K ∩ {x | 0 < w x}).indicator 1 x) +
                (ψB x - (K ∩ {x | w x < 0}).indicator 1 x)|
              ≤ |w x| * (SA.indicator 1 x + SB.indicator 1 x) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add (hψAS x) (hψBS x))
            _ = SA.indicator (fun x => |w x|) x + SB.indicator (fun x => |w x|) x := by
                simp only [mul_add, Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero])
        have e1 := integral_sub hint2 hint1
        have e2 := integral_add ((show IntegrableOn (fun x => |w x|) SA volume from
          (hwL.mono_set hSAL).abs).integrable_indicator hSAm) ((show IntegrableOn (fun x => |w x|) SB
          volume from (hwL.mono_set hSBL).abs).integrable_indicator hSBm)
        simp only [Pi.sub_apply] at m
        rw [integral_indicator hSAm, integral_indicator hSBm] at e2
        have hK_eq : ∫ x in K, |w x| = ∫ x, w x * ((K ∩ {x | 0 < w x}).indicator 1 x -
            (K ∩ {x | w x < 0}).indicator 1 x) := by
          simp_rw [hId]; rw [integral_indicator hK.measurableSet]
        linarith only [hK_eq, e1, m, e2, hH, hSAe, hSBe]
      rw [← ofReal_integral_norm_eq_lintegral_enorm hwK]
      exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hIK)
    rw [← setLIntegral_univ, ← iUnion_closedBall_nat (0 : Eucl (m + 1)),
      ← withDensity_apply _ (MeasurableSet.iUnion fun _ => measurableSet_closedBall),
      Monotone.measure_iUnion fun i j hij => closedBall_subset_closedBall (by exact_mod_cast hij)]
    refine iSup_le fun j => ?_
    rw [withDensity_apply _ measurableSet_closedBall]
    exact stepA _ (isCompact_closedBall 0 j)
  have hu_int : Integrable u volume := by
    have H : ∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, |φ x| ≤ 1) → ∫ x, u x * φ x ≤ X.mass.toReal := by
      intro φ hφ hφc hφ1
      let ω' : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1) :=
        ⟨fun x => φ x • Δ, ⟨hφ.smul contDiff_const, hφc.smul_right⟩, subset_univ _⟩
      have hval : ∀ x, (φ x • Δ) (fun i => EuclideanSpace.single i (1 : ℝ)) = φ x := fun x => by
        rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hΔe, mul_one]
      have hadm : ω' ∈ massAdmissibleOn univ (m + 1) univ :=
        ⟨subset_univ _, fun x => by rw [hCNn]; exact (congrArg abs (hval x)).trans_le (hφ1 x)⟩
      have hXω : X ω' = ∫ x, u x * φ x := by
        rw [hE1]
        exact integral_congr_ae (Eventually.of_forall fun x => congrArg (u x * ·) (hval x))
      rw [← hXω]
      exact (ENNReal.ofReal_le_iff_le_toReal hXm.ne).1 (GeometricCurrentOn.le_massOn _ hadm)
    exact ⟨hu_meas.aestronglyMeasurable, (dual u _ hu_meas hu_loc H).trans_lt ENNReal.ofReal_lt_top⟩
  have hωh : ∀ {d : ℕ} (ω : TestFormOn (univ : Set (Eucl (m + 1))) d) (w : Fin d → Eucl (m + 1)),
      Continuous (fun x => (ω : DifferentialForm (Eucl (m + 1)) d) x w) ∧
      HasCompactSupport (fun x => (ω : DifferentialForm (Eucl (m + 1)) d) x w) := fun ω w =>
    ⟨ω.property.1.1.continuous.eval_const w,
      ω.property.1.2.comp_left (g := fun α : Covector (Eucl (m + 1)) _ => α w) rfl⟩
  have hV : ∀ ψ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      (∀ x, |ψ x| ≤ 1) → ∀ v : Eucl (m + 1), ‖v‖ ≤ 1 →
      ∫ x, u x * fderiv ℝ ψ x v ≤ Mb := by
    intro ψ hψ hψc hψ1 v hv
    obtain ⟨κ, hκv⟩ := hκ v
    have hωs : IsSmoothForm (fun x => ψ x • κ) := hψ.smul contDiff_const
    have hdω : ∀ x, exteriorDerivative (fun x => ψ x • κ) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ ψ x v := by
      intro x
      rw [exteriorDerivative_apply ((hωs.differentiable (by simp)).differentiableAt)]
      have hd : ∀ k : Fin (m + 1), fderiv ℝ (fun y => (ψ y • κ)
          (Fin.removeNth k fun i => EuclideanSpace.single i (1 : ℝ))) x =
          ((-1 : ℝ) ^ (k : ℕ) * v k) • fderiv ℝ ψ x := by
        intro k
        have h1 : (fun y => (ψ y • κ) (Fin.removeNth k fun i => EuclideanSpace.single i (1 : ℝ))) =
            fun y => ψ y * ((-1 : ℝ) ^ (k : ℕ) * v k) := by
          funext y
          rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← hκv k]; rfl
        rw [h1, fderiv_mul_const ((hψ.differentiable (by simp)) x)]
      have hsum : ∑ k : Fin (m + 1), v k • (EuclideanSpace.single k (1 : ℝ) : Eucl (m + 1)) = v := by
        conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr v]
        simp
      conv_rhs => rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd, smul_apply, smul_eq_mul, zsmul_eq_mul, map_smul, smul_eq_mul]
      have h2 : ((((-1 : ℤ) ^ (k : ℕ) : ℤ) : ℝ)) * (-1 : ℝ) ^ (k : ℕ) = 1 := by
        push_cast; rw [← mul_pow]; norm_num
      beta_reduce
      linear_combination (v k * fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ))) * h2
    let ω' : TestFormOn (univ : Set (Eucl (m + 1))) m :=
      ⟨fun x => ψ x • κ, ⟨hωs, hψc.smul_right⟩, subset_univ _⟩
    have hXω : X.boundary ω' = ∫ x, u x * fderiv ℝ ψ x v := by
      rw [GeometricCurrentOn.boundary_apply, hE1]
      congr 1; funext x; rw [← hdω x]; rfl
    have hadm : ω' ∈ massAdmissibleOn univ m univ := by
      refine ⟨subset_univ _, fun x => (hCNm _).trans ?_⟩
      refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
      have h1 : ∀ k : Fin (m + 1), (((ψ x • κ : Covector (Eucl (m + 1)) m))
          (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))) ^ 2 = ψ x ^ 2 * v k ^ 2 := by
        intro k
        have hs : ((-1 : ℝ) ^ (k : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hκv k, mul_pow, mul_pow, hs, one_mul]
      have h2 : ∑ k : Fin (m + 1), v k ^ 2 = ‖v‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        simp [Real.norm_eq_abs, sq_abs]
      have hψ2 : ψ x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hψ1 x)
      have hv2 : ‖v‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
      change ∑ k : Fin (m + 1), (((ψ x • κ : Covector (Eucl (m + 1)) m))
          (fun j => EuclideanSpace.single (Fin.succAbove k j) (1 : ℝ))) ^ 2 ≤ 1
      simp only [h1, ← Finset.mul_sum, h2]
      exact (mul_le_mul hψ2 hv2 (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [← hXω, ← hMb]
    exact (ENNReal.ofReal_le_iff_le_toReal hXb.ne).1 (GeometricCurrentOn.le_massOn _ hadm)
  have hTr : ∀ h : Eucl (m + 1), ∫⁻ x, ‖u (x + h) - u x‖ₑ ≤
      ENNReal.ofReal (‖h‖ * Mb) := by
    intro h
    have hw : Measurable (fun x => u (x + h) - u x) :=
      (hu_meas.comp (measurable_add_const h)).sub hu_meas
    have hwI : Integrable (fun x => u (x + h) - u x) volume :=
      (hu_int.comp_add_right h).sub hu_int
    suffices H : ∀ φ : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
        HasCompactSupport φ → (∀ x, |φ x| ≤ 1) →
        ∫ x, (u (x + h) - u x) * φ x ≤ ‖h‖ * Mb by
      exact dual _ _ hw (fun K _ => hwI.integrableOn) H
    intro φ hφ hφc hφ1
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    obtain ⟨B, hB⟩ := hφ'c.bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
    have hφb : ∀ x, ‖φ x‖ ≤ 1 := fun x => by rw [Real.norm_eq_abs]; exact hφ1 x
    have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun y => u y * φ (y - t • h)) volume :=
      fun t => (hu_meas.mul (hφ.continuous.measurable.comp (measurable_id.sub_const _))).aestronglyMeasurable
    have hFd : ∀ t : ℝ, HasDerivAt (fun t => ∫ y, u y * φ (y - t • h))
        (∫ y, u y * fderiv ℝ φ (y - t • h) (-h)) t := by
      intro t
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
        (F := fun t y => u y * φ (y - t • h)) (x₀ := t)
        (F' := fun t y => u y * fderiv ℝ φ (y - t • h) (-h))
        (bound := fun y => ‖u y‖ * (B * ‖h‖)) (s := univ) univ_mem
        (Eventually.of_forall hmeasF) (hu_int.mul_bdd
          (hφ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
          (Eventually.of_forall fun y => hφb _))
        ((hu_meas.mul ((hφ'c.comp (continuous_id.sub continuous_const)).clm_apply
          continuous_const).measurable).aestronglyMeasurable)
        (Eventually.of_forall fun y t' _ => ?_) (hu_int.norm.mul_const _)
        (Eventually.of_forall fun y t' _ => ?_)).2
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left (((fderiv ℝ φ _).le_opNorm _).trans ?_) (norm_nonneg _)
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
      · have h1 : HasDerivAt (fun t : ℝ => y - t • h) (-h) t' := by
          simpa using ((hasDerivAt_id t').smul_const h).const_sub y
        exact ((hφd (y - t' • h)).hasFDerivAt.comp_hasDerivAt t' h1).const_mul (u y)
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun t => ∫ y, u y * φ (y - t • h))
      (fun t => ∫ y, u y * fderiv ℝ φ (y - t • h) (-h)) zero_lt_one
      (fun t _ => (hFd t).continuousAt.continuousWithinAt) (fun t _ => hFd t)
    have hF1 : ∫ y, u y * φ (y - (1 : ℝ) • h) = ∫ x, u (x + h) * φ x := by
      rw [← integral_add_right_eq_self (fun y => u y * φ (y - (1 : ℝ) • h)) h]
      simp
    have hF0 : ∫ y, u y * φ (y - (0 : ℝ) • h) = ∫ x, u x * φ x := by simp
    have hsplit : ∫ x, (u (x + h) - u x) * φ x = (∫ x, u (x + h) * φ x) - ∫ x, u x * φ x := by
      simp only [sub_mul]
      exact integral_sub ((hu_int.comp_add_right h).mul_bdd hφ.continuous.aestronglyMeasurable
        (Eventually.of_forall hφb)) (hu_int.mul_bdd hφ.continuous.aestronglyMeasurable
        (Eventually.of_forall hφb))
    rw [hsplit, ← hF1, ← hF0]
    simp only [sub_zero, div_one] at hc
    rw [← hc]
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
    have hψ := hV (fun y => φ (y + -(c • h))) (hφ.comp (contDiff_id.add contDiff_const))
      (hφc.comp_homeomorph (Homeomorph.addRight (-(c • h)))) (fun y => hφ1 _)
      (‖h‖⁻¹ • (-h)) (by rw [norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ hnh.ne'])
    simp only [fderiv_comp_add_right] at hψ
    simp only [map_smul, smul_eq_mul, ← sub_eq_add_neg] at hψ
    have he : ∀ y, u y * fderiv ℝ φ (y - c • h) (-h) =
        ‖h‖ * (u y * (‖h‖⁻¹ * fderiv ℝ φ (y - c • h) (-h))) := fun y => by
      rw [mul_left_comm, mul_inv_cancel_left₀ hnh.ne']
    simp only [he, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hψ hnh.le
  have main : ∀ ρ : ℝ, 0 < ρ → ∃ (β : LatticeFaceIndex (m + 1) (m + 1) → ℤ)
      (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)),
      IsLatticeChain ρ (fun F => (β F : ℝ)) Pc ∧
      (∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) (c : ℝ),
        (∀ x, |(ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))| ≤ c) →
        |X ω - Pc ω| ≤ c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb)) ∧
      Pc.boundary.mass ≤
        ENNReal.ofReal ((m + 1) * (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb) := by
    intro ρ hρ
    obtain ⟨H, hHdef⟩ : ∃ H : (Fin (m + 1) → ℤ) → Set (Eucl (m + 1)),
        H = fun z => WithLp.ofLp ⁻¹' (Set.univ.pi fun i => Ico (ρ * z i) (ρ * z i + ρ)) := ⟨_, rfl⟩
    have hofLp := PiLp.volume_preserving_ofLp (Fin (m + 1))
    have hHm : ∀ z, MeasurableSet (H z) := fun z => by
      rw [hHdef]; exact hofLp.measurable (MeasurableSet.univ_pi fun i => measurableSet_Ico)
    have hHv : ∀ z, volume (H z) = ENNReal.ofReal (ρ ^ (m + 1)) := fun z => by
      rw [hHdef]; dsimp only
      rw [hofLp.measure_preimage (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet,
        Real.volume_pi_Ico]
      simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow hρ.le]
    have hint : ∀ (a b : ℤ) (t : ℝ), ρ * a ≤ t → t < ρ * b + ρ → a ≤ b := by
      intro a b t h1 h2
      have h3 : (a : ℝ) < b + 1 := lt_of_mul_lt_mul_left (by linarith) hρ.le
      exact Int.lt_add_one_iff.1 (by exact_mod_cast h3)
    have hHd : Pairwise (Function.onFun Disjoint H) := by
      intro z z' hzz'
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rw [hHdef] at hx hx'
      simp only [mem_preimage, mem_univ_pi, mem_Ico] at hx hx'
      exact hzz' (funext fun i => le_antisymm (hint _ _ _ (hx i).1 (hx' i).2)
        (hint _ _ _ (hx' i).1 (hx i).2))
    have hHc : ⋃ z, H z = univ := by
      refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨fun i => ⌊x i / ρ⌋, ?_⟩
      rw [hHdef]
      simp only [mem_preimage, mem_univ_pi, mem_Ico]
      intro i
      have e : ρ * (x i / ρ) = x i := mul_div_cancel₀ _ hρ.ne'
      constructor
      · nlinarith [Int.floor_le (x i / ρ)]
      · nlinarith [Int.lt_floor_add_one (x i / ρ)]
    have hpart : ∀ f : Eucl (m + 1) → ℝ≥0∞, ∑' z, ∫⁻ x in H z, f x = ∫⁻ x, f x := by
      intro f
      rw [← lintegral_iUnion hHm hHd, hHc, Measure.restrict_univ]
    have hHF : ∀ F : LatticeFaceIndex (m + 1) (m + 1), H F.1 =ᵐ[volume] latticeFace ρ F := by
      intro F
      have hr : ∀ i, i ∈ Set.range F.2 := fun i => ⟨i, congrFun F.2.strictMono.eq_id i⟩
      have hL : latticeFace ρ F =
          WithLp.ofLp ⁻¹' Icc (fun i => ρ * F.1 i) (fun i => ρ * F.1 i + ρ) := by
        ext x
        simp only [latticeFace, mem_ofPred_eq, hr, true_implies, not_true_eq_false, false_implies,
          and_true, mem_preimage, mem_Icc, Pi.le_def, mul_add, mul_one]
        exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
      rw [hL, hHdef]
      exact hofLp.quasiMeasurePreserving.preimage_ae_eq Measure.univ_pi_Ico_ae_eq_Icc
    obtain ⟨Q, hQdef⟩ : ∃ Q : Set (Eucl (m + 1)),
        Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ => Ioo (-ρ) ρ) := ⟨_, rfl⟩
    have hQm : MeasurableSet Q := by
      rw [hQdef]; exact hofLp.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    have hQv : volume Q = ENNReal.ofReal ((2 * ρ) ^ (m + 1)) := by
      rw [hQdef, hofLp.measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
      simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.ofReal_pow (by linarith), two_mul]
    have hQn : ∀ h ∈ Q, ‖h‖ ≤ Real.sqrt ((m : ℝ) + 1) * ρ := by
      intro h hh
      rw [hQdef] at hh
      simp only [mem_preimage, mem_univ_pi, mem_Ioo] at hh
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hρ.le, ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖h i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), ρ ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]; exact (sq_lt_sq' (hh i).1 (hh i).2).le
        _ = ((m : ℝ) + 1) * ρ ^ 2 := by simp
    have hHQ : ∀ z, ∀ x ∈ H z, ∀ y ∈ H z, y - x ∈ Q := by
      intro z x hx y hy
      rw [hHdef] at hx hy; rw [hQdef]
      simp only [mem_preimage, mem_univ_pi, mem_Ico, mem_Ioo, WithLp.ofLp_sub, Pi.sub_apply] at hx hy ⊢
      intro i
      constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    have h2ρ : ENNReal.ofReal (ρ ^ (m + 1)) = 2 * ENNReal.ofReal (ρ ^ (m + 1) / 2) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    have hmed : ∀ z, ∃ bz : ℤ, ∀ a : ℝ, ENNReal.ofReal |(bz : ℝ) - a| * ENNReal.ofReal (ρ ^ (m + 1)) ≤
        2 * ∫⁻ x in H z, ‖u x - a‖ₑ := by
      intro z
      have hfm : ∀ j : ℤ, MeasurableSet ({x | (j : ℝ) ≤ u x} ∩ H z) := fun j =>
        (measurableSet_le measurable_const hu_meas).inter (hHm z)
      have hfa : ∀ j k : ℤ, j ≤ k →
          volume ({x | (k : ℝ) ≤ u x} ∩ H z) ≤ volume ({x | (j : ℝ) ≤ u x} ∩ H z) :=
        fun j k hjk => measure_mono (inter_subset_inter_left _ fun x (hx : (k : ℝ) ≤ u x) =>
          (le_trans (by exact_mod_cast hjk) hx : (j : ℝ) ≤ u x))
      have hhpos : 0 < ENNReal.ofReal (ρ ^ (m + 1) / 2) := ENNReal.ofReal_pos.2 (by positivity)
      have hhlt : ENNReal.ofReal (ρ ^ (m + 1) / 2) < volume (H z) := by
        rw [hHv]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
          (by linarith [show 0 < ρ ^ (m + 1) from by positivity])
      obtain ⟨j₁, hj₁⟩ : ∃ j : ℤ,
          volume ({x | (j : ℝ) ≤ u x} ∩ H z) < ENNReal.ofReal (ρ ^ (m + 1) / 2) := by
        by_contra hcon
        push Not at hcon
        have ht := tendsto_measure_iInter_atTop (μ := volume)
          (s := fun k : ℕ => {x | ((k : ℤ) : ℝ) ≤ u x} ∩ H z)
          (fun k => (hfm k).nullMeasurableSet) (fun k l hkl => inter_subset_inter_left _
            fun x (hx : ((l : ℤ) : ℝ) ≤ u x) => (le_trans (by exact_mod_cast hkl) hx : ((k : ℤ) : ℝ) ≤ u x))
          ⟨0, ((measure_mono inter_subset_right).trans_lt
            ((hHv z).symm ▸ ENNReal.ofReal_lt_top)).ne⟩
        have hempty : (⋂ k : ℕ, {x | ((k : ℤ) : ℝ) ≤ u x} ∩ H z) = ∅ := by
          refine eq_empty_of_forall_notMem fun x hx => ?_
          obtain ⟨k, hk⟩ := exists_nat_gt (u x)
          have := (mem_iInter.1 hx k).1
          simp only [mem_ofPred_eq, Int.cast_natCast] at this
          linarith
        rw [hempty, measure_empty] at ht
        exact absurd (ge_of_tendsto' ht fun k => hcon k) (not_le.2 hhpos)
      obtain ⟨j₀, hj₀⟩ : ∃ j : ℤ,
          ENNReal.ofReal (ρ ^ (m + 1) / 2) ≤ volume ({x | (j : ℝ) ≤ u x} ∩ H z) := by
        have ht := tendsto_measure_iUnion_atTop (μ := volume)
          (s := fun k : ℕ => {x | ((-(k : ℤ) : ℤ) : ℝ) ≤ u x} ∩ H z)
          (fun k l hkl => inter_subset_inter_left _ fun x (hx : (((-(k : ℤ)) : ℤ) : ℝ) ≤ u x) =>
            (le_trans (by push_cast; exact neg_le_neg (by exact_mod_cast hkl)) hx :
              (((-(l : ℤ)) : ℤ) : ℝ) ≤ u x))
        have hU : (⋃ k : ℕ, {x | ((-(k : ℤ) : ℤ) : ℝ) ≤ u x} ∩ H z) = H z := by
          refine Subset.antisymm (iUnion_subset fun k => inter_subset_right) fun x hx =>
            mem_iUnion.2 ?_
          obtain ⟨k, hk⟩ := exists_nat_gt (-u x)
          exact ⟨k, ⟨show (((-(k : ℤ) : ℤ)) : ℝ) ≤ u x by push_cast; linarith, hx⟩⟩
        rw [hU] at ht
        obtain ⟨k, hk⟩ := ((tendsto_order.1 ht).1 _ hhlt).exists
        exact ⟨-(k : ℤ), hk.le⟩
      obtain ⟨bz, hbz, hbmax⟩ := Int.exists_greatest_of_bdd (P := fun j : ℤ =>
          ENNReal.ofReal (ρ ^ (m + 1) / 2) ≤ volume ({x | (j : ℝ) ≤ u x} ∩ H z))
        ⟨j₁, fun j hj => by
          by_contra hjj
          exact absurd (hj.trans (hfa _ _ (le_of_lt (not_le.1 hjj)))) (not_le.2 hj₁)⟩ ⟨j₀, hj₀⟩
      have hb1 : volume ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z) < ENNReal.ofReal (ρ ^ (m + 1) / 2) :=
        lt_of_not_ge fun h => absurd (hbmax _ h) (by omega)
      refine ⟨bz, fun a => ?_⟩
      rw [h2ρ, mul_left_comm]
      gcongr
      rcases le_or_gt a bz with hab | hab
      · calc ENNReal.ofReal |(bz : ℝ) - a| * ENNReal.ofReal (ρ ^ (m + 1) / 2)
            ≤ ENNReal.ofReal |(bz : ℝ) - a| * volume ({x | (bz : ℝ) ≤ u x} ∩ H z) := by gcongr
          _ = ∫⁻ x in {x | (bz : ℝ) ≤ u x} ∩ H z, ENNReal.ofReal |(bz : ℝ) - a| :=
            (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in {x | (bz : ℝ) ≤ u x} ∩ H z, ‖u x - a‖ₑ :=
            setLIntegral_mono' (hfm bz) fun x hx => by
              have hx1 : (bz : ℝ) ≤ u x := hx.1
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (abs_le_abs (by linarith) (by linarith))
          _ ≤ ∫⁻ x in H z, ‖u x - a‖ₑ := lintegral_mono_set inter_subset_right
      · have hD : ENNReal.ofReal (ρ ^ (m + 1) / 2) ≤
            volume (H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z)) := by
          rw [measure_sdiff inter_subset_right (hfm _).nullMeasurableSet
            ((measure_mono inter_subset_right).trans_lt ((hHv z).symm ▸ ENNReal.ofReal_lt_top)).ne,
            hHv, h2ρ, two_mul]
          exact ENNReal.le_sub_of_add_le_right ((measure_mono inter_subset_right).trans_lt
            ((hHv z).symm ▸ ENNReal.ofReal_lt_top)).ne (add_le_add le_rfl hb1.le)
        calc ENNReal.ofReal |(bz : ℝ) - a| * ENNReal.ofReal (ρ ^ (m + 1) / 2)
            ≤ ENNReal.ofReal |(bz : ℝ) - a| *
              volume (H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z)) := by gcongr
          _ = ∫⁻ x in H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z), ENNReal.ofReal |(bz : ℝ) - a| :=
            (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in H z \ ({x | ((bz + 1 : ℤ) : ℝ) ≤ u x} ∩ H z), ‖u x - a‖ₑ :=
            setLIntegral_mono' ((hHm z).diff (hfm _)) fun x hx => by
              obtain ⟨k, hk⟩ := hu_Z x
              have hlt : u x < (bz : ℝ) + 1 := by
                by_contra h
                exact hx.2 ⟨show (((bz + 1 : ℤ)) : ℝ) ≤ u x by push_cast; linarith, hx.1⟩
              have hle : u x ≤ bz := by
                rw [hk] at hlt ⊢
                exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast hlt)
              rw [Real.enorm_eq_ofReal_abs, abs_sub_comm, abs_sub_comm (u x)]
              exact ENNReal.ofReal_le_ofReal (abs_le_abs (by linarith) (by linarith))
          _ ≤ ∫⁻ x in H z, ‖u x - a‖ₑ := lintegral_mono_set sdiff_subset
    choose b hb using hmed
    have hbfin : {z | b z ≠ 0}.Finite := by
      have htsum : ∑' z, ∫⁻ x in H z, ‖u x‖ₑ ≠ ⊤ := by rw [hpart]; exact hu_int.2.ne
      refine (ENNReal.finite_const_le_of_tsum_ne_top htsum
        (ε := ENNReal.ofReal (ρ ^ (m + 1) / 2)) (ENNReal.ofReal_pos.2 (by positivity)).ne').subset
        fun z hz => ?_
      have h1 := hb z 0
      simp only [sub_zero] at h1
      have h3 : (1 : ℝ) ≤ |(b z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
      have h4 : ENNReal.ofReal (ρ ^ (m + 1)) ≤ 2 * ∫⁻ x in H z, ‖u x‖ₑ := by
        refine le_trans ?_ h1
        calc ENNReal.ofReal (ρ ^ (m + 1)) = 1 * ENNReal.ofReal (ρ ^ (m + 1)) := (one_mul _).symm
          _ ≤ ENNReal.ofReal |(b z : ℝ)| * ENNReal.ofReal (ρ ^ (m + 1)) := by
            gcongr; exact ENNReal.one_le_ofReal.2 h3
      rw [h2ρ] at h4
      exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h4
    have hKEY : ∑' z, ∫⁻ x in H z, ‖u x - b z‖ₑ ≤
        ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
      have hPM : ∀ z, ENNReal.ofReal (ρ ^ (m + 1)) * ∫⁻ x in H z, ‖u x - b z‖ₑ ≤
          3 * ∫⁻ y in H z, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by
        intro z
        have hI : ∀ y ∈ H z, ∫⁻ x in H z, ‖u x - b z‖ₑ ≤ 3 * ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by
          intro y hy
          have hDB : ∫⁻ x in H z, ‖u x - u y‖ₑ ≤ ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by
            rw [← lintegral_indicator (hHm z), ← lintegral_add_left_eq_self _ y,
              ← lintegral_indicator hQm]
            refine lintegral_mono fun h => ?_
            by_cases hh : y + h ∈ H z
            · rw [indicator_of_mem hh, indicator_of_mem (by simpa using hHQ z y hy _ hh)]
            · rw [indicator_of_notMem hh]; exact zero_le
          have h1 : ∫⁻ x in H z, ‖u x - b z‖ₑ ≤
              (∫⁻ x in H z, ‖u x - u y‖ₑ) + ENNReal.ofReal (ρ ^ (m + 1)) * ‖u y - b z‖ₑ := by
            calc ∫⁻ x in H z, ‖u x - b z‖ₑ ≤ ∫⁻ x in H z, (‖u x - u y‖ₑ + ‖u y - b z‖ₑ) :=
                  lintegral_mono fun x => by
                    simpa only [sub_add_sub_cancel] using enorm_add_le (u x - u y) (u y - b z)
              _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const, hHv, mul_comm]
          have h2 : ENNReal.ofReal (ρ ^ (m + 1)) * ‖u y - b z‖ₑ ≤ 2 * ∫⁻ x in H z, ‖u x - u y‖ₑ := by
            rw [mul_comm, Real.enorm_eq_ofReal_abs, abs_sub_comm]; exact hb z (u y)
          calc ∫⁻ x in H z, ‖u x - b z‖ₑ
              ≤ (∫⁻ x in H z, ‖u x - u y‖ₑ) + 2 * ∫⁻ x in H z, ‖u x - u y‖ₑ :=
                h1.trans (add_le_add le_rfl h2)
            _ = 3 * ∫⁻ x in H z, ‖u x - u y‖ₑ := by ring
            _ ≤ 3 * ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by gcongr
        calc ENNReal.ofReal (ρ ^ (m + 1)) * ∫⁻ x in H z, ‖u x - b z‖ₑ
            = ∫⁻ y in H z, ∫⁻ x in H z, ‖u x - b z‖ₑ := by rw [setLIntegral_const, hHv, mul_comm]
          _ ≤ ∫⁻ y in H z, 3 * ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := setLIntegral_mono' (hHm z) hI
          _ = 3 * ∫⁻ y in H z, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := lintegral_const_mul' _ _ (by norm_num)
      have hswap : ∫⁻ y, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ = ∫⁻ h in Q, ∫⁻ y, ‖u (y + h) - u y‖ₑ :=
        lintegral_lintegral_swap (((hu_meas.comp measurable_add).sub
          (hu_meas.comp measurable_fst)).enorm.aemeasurable)
      have hQb : ∫⁻ h in Q, ∫⁻ y, ‖u (y + h) - u y‖ₑ ≤
          ENNReal.ofReal (Real.sqrt ((m : ℝ) + 1) * ρ * Mb) * ENNReal.ofReal ((2 * ρ) ^ (m + 1)) := by
        rw [← hQv, ← setLIntegral_const]
        exact setLIntegral_mono' hQm fun h hh => (hTr h).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hQn h hh) hMb0))
      have hne : ENNReal.ofReal (ρ ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [← ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top, ← ENNReal.tsum_mul_left]
      calc ∑' z, ENNReal.ofReal (ρ ^ (m + 1)) * ∫⁻ x in H z, ‖u x - b z‖ₑ
          ≤ ∑' z, 3 * ∫⁻ y in H z, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := ENNReal.tsum_le_tsum hPM
        _ = 3 * ∫⁻ y, ∫⁻ h in Q, ‖u (y + h) - u y‖ₑ := by rw [ENNReal.tsum_mul_left, hpart]
        _ ≤ 3 * (ENNReal.ofReal (Real.sqrt ((m : ℝ) + 1) * ρ * Mb) *
            ENNReal.ofReal ((2 * ρ) ^ (m + 1))) := by rw [hswap]; gcongr
        _ = ENNReal.ofReal (ρ ^ (m + 1)) *
            ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
    have hZbm : ∀ z, z ∉ hbfin.toFinset → b z = 0 := fun z hz => by
      by_contra h; exact hz (hbfin.mem_toFinset.2 h)
    obtain ⟨v, hvdef⟩ : ∃ v : Eucl (m + 1) → ℝ,
        v = fun x => ∑ z ∈ hbfin.toFinset, (H z).indicator (fun _ => (b z : ℝ)) x := ⟨_, rfl⟩
    have hv_meas : Measurable v := by
      rw [hvdef]; exact Finset.measurable_sum _ fun z _ => measurable_const.indicator (hHm z)
    have hv_eq : ∀ z, ∀ x ∈ H z, v x = b z := by
      intro z x hx
      rw [hvdef]; dsimp only
      rw [Finset.sum_eq_single z (fun z' _ hz' => indicator_of_notMem
        (fun hx' => Set.disjoint_left.1 (hHd hz') hx' hx) _)
        (fun hz => by rw [indicator_of_mem hx, hZbm z hz, Int.cast_zero]), indicator_of_mem hx]
    have hv_bdd : ∀ x, ‖v x‖ ≤ ∑ z ∈ hbfin.toFinset, |(b z : ℝ)| := by
      intro x; rw [hvdef]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
      by_cases hx : x ∈ H z
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
      · rw [indicator_of_notMem hx, norm_zero]; exact abs_nonneg _
    have hv_intg : Integrable v volume := by
      rw [hvdef]
      exact integrable_finsetSum _ fun z _ => (integrableOn_const (by rw [hHv]; exact
        ENNReal.ofReal_ne_top)).integrable_indicator (hHm z)
    have hv_int : ∀ g : Eucl (m + 1) → ℝ, Integrable g volume →
        ∫ x, v x * g x = ∑ z ∈ hbfin.toFinset, (b z : ℝ) * ∫ x in H z, g x := by
      intro g hg
      rw [hvdef]
      simp only [Finset.sum_mul]
      rw [integral_finsetSum _ fun z _ => ?_]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [← integral_indicator (hHm z), ← integral_const_mul]
        congr 1; funext x
        by_cases hx : x ∈ H z
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, mul_zero]
      · refine ((hg.indicator (hHm z)).const_mul (b z : ℝ)).congr (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ H z
        · simp only [indicator_of_mem hx]
        · simp only [indicator_of_notMem hx, zero_mul, mul_zero]
    have hI : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Integrable (fun x =>
        v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)))
        volume := fun ω =>
      ((hωh ω _).1.integrable_of_hasCompactSupport (hωh ω _).2).bdd_mul hv_meas.aestronglyMeasurable
        (Eventually.of_forall hv_bdd)
    obtain ⟨F, hF⟩ : ∃ F : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1) → ℝ, ∀ ω, F ω =
        ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := ⟨_, fun _ => rfl⟩
    have hadd : ∀ ω η, F (ω + η) = F ω + F η := fun ω η => by
      rw [hF, hF, hF, ← integral_add (hI ω) (hI η)]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_add _ _ _)
    have hsmul : ∀ (c : ℝ) ω, F (c • ω) = (RingHom.id ℝ) c • F ω := fun c ω => by
      rw [hF, hF, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_left_comm (v x) c _)
    have hcont : ∀ ωs : ℕ → TestFormOn (univ : Set (Eucl (m + 1))) (m + 1),
        TestFormOnConverges ωs 0 → Tendsto (fun j => F (ωs j)) atTop (𝓝 0) := by
      rintro ωs ⟨K, -, -, hsupp, -, hder⟩
      refine Metric.tendsto_nhds.2 fun ε hε => (hder 0 _ (Metric.dist_mem_uniformity
        (show 0 < ε / ((∫ x, ‖v x‖) + 1) by positivity))).mono fun j hj => ?_
      have hbd : ∀ x, ‖(ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ ε / ((∫ x, ‖v x‖) + 1) := by
        intro x
        refine (((ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x).le_opNorm _).trans ?_
        rw [he, mul_one]
        by_cases hx : x ∈ K
        · have h : dist (iteratedFDeriv ℝ 0 ((0 : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) :
              DifferentialForm (Eucl (m + 1)) (m + 1)) x)
              (iteratedFDeriv ℝ 0 (ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x) <
              ε / ((∫ x, ‖v x‖) + 1) := hj x hx
          rw [show ((0 : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) :
            DifferentialForm (Eucl (m + 1)) (m + 1)) = 0 from rfl, iteratedFDeriv_zero, Pi.zero_apply,
            dist_zero_left, norm_iteratedFDeriv_zero] at h
          exact h.le
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]; positivity
      rw [dist_zero_right, hF]
      calc ‖∫ x, v x * (ωs j : DifferentialForm (Eucl (m + 1)) (m + 1)) x
            (fun i => EuclideanSpace.single i (1 : ℝ))‖
          ≤ ∫ x, ε / ((∫ x, ‖v x‖) + 1) * ‖v x‖ :=
            norm_integral_le_of_norm_le (hv_intg.norm.const_mul _) (Eventually.of_forall fun x => by
              rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _))
        _ = ε / ((∫ x, ‖v x‖) + 1) * ∫ x, ‖v x‖ := integral_const_mul _ _
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          exact mul_lt_mul_of_pos_left (lt_add_one _) hε
    obtain ⟨Pc, hPc⟩ : ∃ Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1),
        ∀ ω, Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := ⟨⟨⟨⟨F, hadd⟩, hsmul⟩, hcont⟩, hF⟩
    have hLFA : ∀ (z : Fin (m + 1) → ℤ) (σ : SimonMultiIndex (m + 1) (m + 1))
        (ω : DifferentialForm (Eucl (m + 1)) (m + 1)),
        latticeFaceAction ρ (z, σ) ω = ∫ x in H z, ω x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
      intro z σ ω
      unfold latticeFaceAction
      rw [hvol, ← setIntegral_congr_set (hHF (z, σ))]
      have hσ : ⇑σ = id := σ.strictMono.eq_id
      simp only [hσ, id]
    have hPcZ : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω =
        ∑ z ∈ hbfin.toFinset, (b z : ℝ) * latticeFaceAction ρ (z, RelEmbedding.refl _) ω := by
      intro ω
      rw [hPc, hv_int _ ((hωh ω _).1.integrable_of_hasCompactSupport (hωh ω _).2)]
      simp only [hLFA]
    have hLC : IsLatticeChain ρ (fun F : LatticeFaceIndex (m + 1) (m + 1) => ((b F.1 : ℤ) : ℝ)) Pc := by
      intro ω
      rw [hPcZ, ← (Equiv.mk (fun z => (z, RelEmbedding.refl _)) Prod.fst (fun _ => rfl)
        (fun F => Prod.ext rfl (DFunLike.coe_injective (F.2.strictMono.eq_id).symm)) :
          (Fin (m + 1) → ℤ) ≃ LatticeFaceIndex (m + 1) (m + 1)).tsum_eq]
      exact (tsum_eq_sum fun z hz => by simp only [hZbm z hz, Int.cast_zero, zero_mul]).symm
    have hres : ∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) (c : ℝ),
        (∀ x, |(ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))| ≤ c) →
        |X ω - Pc ω| ≤ c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
      intro ω c hc
      have hωhi := (hωh ω (fun i => EuclideanSpace.single i (1 : ℝ))).1.integrable_of_hasCompactSupport
        (μ := volume) (hωh ω _).2
      have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
      have huv : Integrable (fun x => u x - v x) volume := hu_int.sub hv_intg
      rw [hE1, hPc, ← integral_sub (hu_int.mul_bdd hωhi.aestronglyMeasurable
        (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hc x))) (hI ω)]
      refine (le_trans (b := ∫ x, c * |u x - v x|) ?_ ?_)
      · rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (huv.abs.const_mul c) (Eventually.of_forall fun x => ?_)
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      have h2 : ∫ x, |u x - v x| = (∫⁻ x, ‖u x - v x‖ₑ).toReal := by
        rw [← integral_norm_eq_lintegral_enorm huv.aestronglyMeasurable]
        simp only [Real.norm_eq_abs]
      rw [h2]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      rw [← hpart]
      exact le_trans (le_of_eq (tsum_congr fun z => setLIntegral_congr_fun (hHm z)
        fun x hx => by simp only [hv_eq z x hx])) hKEY
    have hadj : ∀ i : Fin (m + 1), ∑' z, ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| *
        ρ ^ (m + 1)) ≤ ENNReal.ofReal (2 * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) +
          ρ * Mb) := by
      intro i
      have hcn : ‖ρ • (EuclideanSpace.single i (1 : ℝ) : Eucl (m + 1))‖ = ρ := by
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg hρ.le]
      have hshift : ∀ z, ∫⁻ x in H z, ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) -
          b (z + Pi.single i 1)‖ₑ = ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ := by
        intro z
        rw [← lintegral_indicator (hHm z), ← lintegral_indicator (hHm _)]
        conv_rhs => rw [← lintegral_add_right_eq_self _ (ρ • EuclideanSpace.single i (1 : ℝ))]
        refine lintegral_congr fun x => ?_
        have hiff : x + ρ • EuclideanSpace.single i (1 : ℝ) ∈ H (z + Pi.single i 1) ↔ x ∈ H z := by
          rw [hHdef]
          simp only [mem_preimage, mem_univ_pi, mem_Ico, WithLp.ofLp_add, WithLp.ofLp_smul,
            PiLp.ofLp_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          refine forall_congr' fun j => ?_
          rcases eq_or_ne j i with rfl | hj
          · simp only [Pi.single_eq_same, Int.cast_add, Int.cast_one, mul_add, mul_one,
              add_le_add_iff_right, add_lt_add_iff_right]
          · simp only [Pi.single_eq_of_ne hj, add_zero, mul_zero]
        by_cases hx : x ∈ H z
        · rw [indicator_of_mem hx, indicator_of_mem (hiff.2 hx)]
        · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hiff.1 h))]
      have hz : ∀ z, ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| * ρ ^ (m + 1)) ≤
          (∫⁻ x in H z, ‖u x - b z‖ₑ) + (∫⁻ x in H z,
            ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ) +
          ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ := by
        intro z
        rw [← hshift z]
        calc ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| * ρ ^ (m + 1))
            = ∫⁻ x in H z, ENNReal.ofReal |(b z : ℝ) - b (z + Pi.single i 1)| := by
              rw [setLIntegral_const, hHv, ENNReal.ofReal_mul (abs_nonneg _)]
          _ ≤ ∫⁻ x in H z, (‖u x - b z‖ₑ + ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ +
              ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - b (z + Pi.single i 1)‖ₑ) :=
              lintegral_mono fun x => by
                rw [← Real.enorm_eq_ofReal_abs, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub,
                  ← edist_eq_enorm_sub, ← edist_eq_enorm_sub, edist_comm (u x),
                  edist_comm (u (x + ρ • EuclideanSpace.single i (1 : ℝ)))]
                exact edist_triangle4 _ _ _ _
          _ = _ := by
              have hm1 : Measurable fun x : Eucl (m + 1) =>
                  ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - (b (z + Pi.single i 1) : ℝ)‖ₑ :=
                ((hu_meas.comp (measurable_add_const _)).sub_const _).enorm
              have hm2 : Measurable fun x : Eucl (m + 1) =>
                  ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ :=
                ((hu_meas.comp (measurable_add_const _)).sub hu_meas).enorm
              rw [lintegral_add_right _ hm1, lintegral_add_right _ hm2]
      calc ∑' z, ENNReal.ofReal (|(b z : ℝ) - b (z + Pi.single i 1)| * ρ ^ (m + 1))
          ≤ ∑' z, ((∫⁻ x in H z, ‖u x - b z‖ₑ) + (∫⁻ x in H z,
            ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ) +
            ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ) :=
            ENNReal.tsum_le_tsum hz
        _ = (∑' z, ∫⁻ x in H z, ‖u x - b z‖ₑ) + (∑' z, ∫⁻ x in H z,
            ‖u (x + ρ • EuclideanSpace.single i (1 : ℝ)) - u x‖ₑ) +
            ∑' z, ∫⁻ y in H (z + Pi.single i 1), ‖u y - b (z + Pi.single i 1)‖ₑ := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add]
        _ ≤ ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) +
            ENNReal.ofReal (ρ * Mb) +
            ENNReal.ofReal (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) * ρ * Mb) := by
            refine add_le_add (add_le_add hKEY ?_) ?_
            · rw [hpart]; exact (hTr _).trans (by rw [hcn])
            · exact (Equiv.tsum_eq (Equiv.addRight (Pi.single i 1))
                (fun z => ∫⁻ y in H z, ‖u y - b z‖ₑ)).le.trans hKEY
        _ = _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    have hface : ∀ (i : Fin (m + 1)) (w : Fin (m + 1) → ℤ),
        (μHE[m] : Measure (Eucl (m + 1))) (latticeFace ρ
          (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))) ≤ ENNReal.ofReal (ρ ^ m) := by
      intro i w
      have hι : Isometry (fun s : EuclideanSpace ℝ (Fin m) => (WithLp.toLp 2 fun l =>
          ρ * (w l : ℝ) + Fin.insertNth (α := fun _ => ℝ) i 0 (WithLp.ofLp s) l : Eucl (m + 1))) :=
        Isometry.of_dist_eq fun s t => by
          rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succAbove _ i]
          simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
            dist_add_left, dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            zero_add]
      have hsub : latticeFace ρ (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _)) ⊆
          (fun s : EuclideanSpace ℝ (Fin m) => (WithLp.toLp 2 fun l =>
            ρ * (w l : ℝ) + Fin.insertNth (α := fun _ => ℝ) i 0 (WithLp.ofLp s) l : Eucl (m + 1))) ''
          (WithLp.ofLp ⁻¹' Icc 0 (fun _ => ρ)) := by
        intro x hx
        have hr : ∀ j, (Fin.succAbove i j) ∈ Set.range
            ((Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _) : Fin m → Fin (m + 1)) :=
          fun j => ⟨j, rfl⟩
        have hi : i ∉ Set.range
            ((Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _) : Fin m → Fin (m + 1)) := by
          rintro ⟨j, hj⟩; exact Fin.succAbove_ne i j hj
        refine ⟨WithLp.toLp 2 fun j => x (Fin.succAbove i j) - ρ * (w (Fin.succAbove i j) : ℝ),
          ⟨fun j => ?_, fun j => ?_⟩, ?_⟩
        · have := ((hx (Fin.succAbove i j)).1 (hr j)).1
          simp only [Pi.zero_apply]; linarith
        · have := ((hx (Fin.succAbove i j)).1 (hr j)).2
          dsimp only; linarith
        · ext l
          dsimp only
          rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
          · rw [Fin.insertNth_apply_same, add_zero, (hx l).2 hi]
          · rw [Fin.insertNth_apply_succAbove]; ring
      calc (μHE[m] : Measure (Eucl (m + 1))) (latticeFace ρ
            (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _)))
          ≤ (μHE[m] : Measure (Eucl (m + 1))) _ := measure_mono hsub
        _ = (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) (WithLp.ofLp ⁻¹' Icc 0 (fun _ => ρ)) :=
          hι.euclideanHausdorffMeasure_image _
        _ = ENNReal.ofReal (ρ ^ m) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
            (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage measurableSet_Icc.nullMeasurableSet,
            Real.volume_Icc_pi]
          simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [ENNReal.ofReal_pow hρ.le]
    have hAbd : ∀ (i : Fin (m + 1)) (w : Fin (m + 1) → ℤ)
        (ω : TestFormOn (univ : Set (Eucl (m + 1))) m),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ 1) →
        |latticeFaceAction ρ (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
          (ω : DifferentialForm (Eucl (m + 1)) m)| ≤ ρ ^ m := by
      intro i w ω hω
      refine (norm_setIntegral_le_of_norm_le_const (C := 1)
        ((hface i w).trans_lt ENNReal.ofReal_lt_top)
        fun x _ => by rw [Real.norm_eq_abs]; exact (hCN1 _ i).trans (hω x)).trans ?_
      rw [one_mul]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hface i w)
    have hbdry : ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) m,
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ 1) →
        Pc.boundary ω ≤ (m + 1) * (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb := by
      intro ω hω
      have hst : ∀ z, latticeFaceAction ρ (z, RelEmbedding.refl _)
          (exteriorDerivative (ω : DifferentialForm (Eucl (m + 1)) m)) = ∑ i : Fin (m + 1),
          (-1 : ℝ) ^ (i : ℕ) * (latticeFaceAction ρ (z + Pi.single i 1,
            (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _)) (ω : DifferentialForm (Eucl (m + 1)) m) -
            latticeFaceAction ρ (z, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
              (ω : DifferentialForm (Eucl (m + 1)) m)) := fun z =>
        Submission.br_lattice_face_stokes (m + 1) m ρ hρ (z, RelEmbedding.refl _) ω ω.property.1.1
      rw [GeometricCurrentOn.boundary_apply, hPcZ]
      change ∑ z ∈ hbfin.toFinset, (b z : ℝ) * latticeFaceAction ρ (z, RelEmbedding.refl _)
        (exteriorDerivative (ω : DifferentialForm (Eucl (m + 1)) m)) ≤ _
      simp only [hst, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine (le_abs_self _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      have hfin : ∀ i : Fin (m + 1), |∑ z ∈ hbfin.toFinset, (b z : ℝ) * ((-1 : ℝ) ^ (i : ℕ) *
          (latticeFaceAction ρ (z + Pi.single i 1, (Fin.succAboveOrderEmb i).trans
            (RelEmbedding.refl _)) (ω : DifferentialForm (Eucl (m + 1)) m) -
          latticeFaceAction ρ (z, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
            (ω : DifferentialForm (Eucl (m + 1)) m)))| ≤
          (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb := by
        intro i
        obtain ⟨A, hA⟩ : ∃ A : (Fin (m + 1) → ℤ) → ℝ, ∀ w, latticeFaceAction ρ
            (w, (Fin.succAboveOrderEmb i).trans (RelEmbedding.refl _))
            (ω : DifferentialForm (Eucl (m + 1)) m) = A w := ⟨_, fun _ => rfl⟩
        have hAb : ∀ w, |A w| ≤ ρ ^ m := fun w => (hA w) ▸ hAbd i w ω hω
        simp only [hA]
        have hadj' := hadj i
        generalize (Pi.single i 1 : Fin (m + 1) → ℤ) = e at hadj' ⊢
        have e1 : ∑ z ∈ hbfin.toFinset, (b z : ℝ) * A (z + e) =
            ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e), (b (w - e) : ℝ) * A w := by
          rw [← Finset.sum_subset (s₁ := hbfin.toFinset.image (· + e))
            (f := fun w => (b (w - e) : ℝ) * A w) Finset.subset_union_right ?_,
            Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
          · simp only [add_sub_cancel_right]
          · intro w _ hw
            rw [hZbm _ (fun h => hw (Finset.mem_image.2 ⟨_, h, sub_add_cancel w e⟩)),
              Int.cast_zero, zero_mul]
        have e2 : ∑ z ∈ hbfin.toFinset, (b z : ℝ) * A z =
            ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e), (b w : ℝ) * A w :=
          Finset.sum_subset Finset.subset_union_left fun w _ hw => by
            rw [hZbm w hw, Int.cast_zero, zero_mul]
        have e3 : ∑ z ∈ hbfin.toFinset, (b z : ℝ) * ((-1 : ℝ) ^ (i : ℕ) * (A (z + e) - A z)) =
            (-1 : ℝ) ^ (i : ℕ) * ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e),
              ((b (w - e) : ℝ) - b w) * A w := by
          calc ∑ z ∈ hbfin.toFinset, (b z : ℝ) * ((-1 : ℝ) ^ (i : ℕ) * (A (z + e) - A z))
              = (-1 : ℝ) ^ (i : ℕ) * (∑ z ∈ hbfin.toFinset, (b z : ℝ) * A (z + e) -
                ∑ z ∈ hbfin.toFinset, (b z : ℝ) * A z) := by
                rw [← Finset.sum_sub_distrib, Finset.mul_sum]
                exact Finset.sum_congr rfl fun z _ => by ring
            _ = _ := by rw [e1, e2, ← Finset.sum_sub_distrib]; simp only [sub_mul]
        have hsumW : ρ * ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e),
            |(b (w - e) : ℝ) - b w| * ρ ^ m ≤
            ρ * ((6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb) := by
          rw [Finset.mul_sum, ← ENNReal.ofReal_le_ofReal_iff (by positivity),
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          calc ∑ w ∈ hbfin.toFinset ∪ hbfin.toFinset.image (· + e),
                ENNReal.ofReal (ρ * (|(b (w - e) : ℝ) - b w| * ρ ^ m))
              ≤ ∑' w, ENNReal.ofReal (|(b (w - e) : ℝ) - b w| * ρ ^ (m + 1)) := by
                refine le_trans (le_of_eq (Finset.sum_congr rfl fun w _ => by ring_nf))
                  (ENNReal.sum_le_tsum _)
            _ = ∑' z, ENNReal.ofReal (|(b z : ℝ) - b (z + e)| * ρ ^ (m + 1)) := by
                rw [← (Equiv.addRight e).tsum_eq]
                simp only [Equiv.coe_addRight, add_sub_cancel_right]
            _ ≤ _ := hadj'
            _ = _ := by congr 1; ring
        rw [e3, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine le_trans (Finset.sum_le_sum fun w _ => ?_) (le_of_mul_le_mul_left hsumW hρ)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hAb w) (abs_nonneg _)
      refine (Finset.sum_le_sum fun i _ => hfin i).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hmass : Pc.boundary.mass ≤
        ENNReal.ofReal ((m + 1) * (6 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) + 1) * Mb) := by
      rw [GeometricCurrentOn.mass, GeometricCurrentOn.massOn]
      refine sSup_le ?_
      rintro _ ⟨ω, hω, rfl⟩
      exact ENNReal.ofReal_le_ofReal (hbdry ω hω.2)
    exact ⟨fun F => b F.1, Pc, hLC, hres, hmass⟩
  choose β Pc hLC hres hbd using fun k : ℕ => main (1 / ((k : ℝ) + 1)) (by positivity)
  refine ⟨fun k => 1 / ((k : ℝ) + 1), β, Pc, fun k => by positivity, hLC, fun ω => ?_,
    (iSup_le hbd).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨c, hc⟩ := (hωh ω (fun i => EuclideanSpace.single i (1 : ℝ))).1.bounded_above_of_compact_support
    (hωh ω _).2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun k : ℕ => c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1) *
    (1 / ((k : ℝ) + 1)) * Mb)) (fun k => norm_nonneg _) (fun k => ?_) ?_
  · rw [Real.norm_eq_abs, abs_sub_comm]
    exact hres k ω c fun x => (Real.norm_eq_abs _).symm.trans_le (hc x)
  · have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (c * (3 * 2 ^ (m + 1) * Real.sqrt ((m : ℝ) + 1)))).mul_const Mb
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
