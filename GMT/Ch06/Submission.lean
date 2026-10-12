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

/-- **Bounded density of a dominated finitely additive set function** (the Radon–Nikodym step of
`(L¹)* = L^∞`, used without proof in Simon Ch. 6, Theorem 2.34, p. 142; cf. Folland, *Real
Analysis*, Thm 6.15).  Let `μ` be finite, `C ≥ 0`, and `ν` additive on disjoint measurable sets
with `|ν(A)| ≤ C μ(A)`.  Then `ρ = ν + C μ` is a finite measure: `ν(∅) = 0`, `ρ` is finitely
additive, and `ρ(⋃ sᵢ) - ρ(⋃_{i<N} sᵢ) = ρ(⋃ sᵢ \ ⋃_{i<N} sᵢ) ≤ 2C μ(⋃ sᵢ \ ⋃_{i<N} sᵢ) → 0`.
Also `ρ ≪ μ`, so `ρ = f μ` for `f = dρ/dμ` (zero singular part), and `0 ≤ f ≤ 2C` `μ`-a.e.  The
truncation `θ = min(f, 2C) - C` is measurable, `|θ| ≤ C` everywhere, and `θ = f - C` `μ`-a.e.,
so `ν(A) = ρ(A) - C μ(A) = ∫_A θ dμ`. -/
theorem Submission.constancy_riesz_bounded_density_of_dominated_additive : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α), IsFiniteMeasure μ → ∀ (ν : Set α → ℝ) (C : ℝ), 0 ≤ C → (∀ A B : Set α, MeasurableSet A → MeasurableSet B → Disjoint A B → ν (A ∪ B) = ν A + ν B) → (∀ A : Set α, MeasurableSet A → |ν A| ≤ C * μ.real A) → ∃ θ : α → ℝ, Measurable θ ∧ (∀ x, |θ x| ≤ C) ∧ ∀ A : Set α, MeasurableSet A → ν A = ∫ x in A, θ x ∂μ := by
  intro α _ μ hμ ν C hC hadd hdom
  -- Step 1: `ν(∅) = 0`, since `|ν(∅)| ≤ C μ(∅) = 0`.
  have hν0 : ν ∅ = 0 := by
    have h := hdom ∅ MeasurableSet.empty
    rw [measureReal_empty, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- `g = ν + C μ` is nonnegative, bounded by `2C μ` and additive on measurable sets.
  set g : Set α → ℝ := fun A => ν A + C * μ.real A with hg_def
  have hg_nonneg : ∀ A, MeasurableSet A → 0 ≤ g A := fun A hA => by
    have h := hdom A hA
    have := neg_abs_le (ν A)
    simp only [hg_def]; linarith
  have hg_le : ∀ A, MeasurableSet A → g A ≤ 2 * C * μ.real A := fun A hA => by
    have h := hdom A hA
    have := le_abs_self (ν A)
    simp only [hg_def]; linarith
  have hg_add : ∀ A B, MeasurableSet A → MeasurableSet B → Disjoint A B →
      g (A ∪ B) = g A + g B := by
    intro A B hA hB hAB
    simp only [hg_def]
    rw [hadd A B hA hB hAB, measureReal_union hAB hB]; ring
  -- Step 2: finite additivity, `g(⋃_{i<N} sᵢ) = ∑_{i<N} g(sᵢ)`, by induction on `N`.
  have hfin : ∀ s : ℕ → Set α, (∀ i, MeasurableSet (s i)) → Pairwise (Function.onFun Disjoint s) →
      ∀ N, g (⋃ i ∈ Finset.range N, s i) = ∑ i ∈ Finset.range N, g (s i) := by
    intro s hs hd N
    induction N with
    | zero => simp [hg_def, hν0]
    | succ N ih =>
      rw [Finset.range_add_one, Finset.set_biUnion_insert,
        Finset.sum_insert Finset.notMem_range_self,
        hg_add _ _ (hs N) (Finset.measurableSet_biUnion _ fun i _ => hs i), ih]
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (Finset.mem_range.mp hi).ne'
  -- Step 3: countable additivity.  With `A = ⋃ sᵢ` and `S_N = ⋃_{i<N} sᵢ ↑ A`,
  -- `g(A) - 2C (μ(A) - μ(S_N)) ≤ g(S_N) ≤ g(A)` and `μ(S_N) → μ(A)`.
  have hcount : ∀ s : ℕ → Set α, (∀ i, MeasurableSet (s i)) →
      Pairwise (Function.onFun Disjoint s) → HasSum (fun i => g (s i)) (g (⋃ i, s i)) := by
    intro s hs hd
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => hg_nonneg _ (hs i))]
    set S : ℕ → Set α := fun N => ⋃ i ∈ Finset.range N, s i with hS_def
    have hSm : ∀ N, MeasurableSet (S N) := fun N =>
      Finset.measurableSet_biUnion _ fun i _ => hs i
    have hA : MeasurableSet (⋃ i, s i) := MeasurableSet.iUnion hs
    have hSA : ∀ N, S N ⊆ ⋃ i, s i := fun N => Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
    have hmono : Monotone S := by
      intro a b hab x hx
      simp only [hS_def, Set.mem_iUnion, Finset.mem_range] at hx ⊢
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨i, by omega, hx⟩
    have hU : ⋃ N, S N = ⋃ i, s i := by
      ext x
      simp only [hS_def, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨N, i, _, hx⟩; exact ⟨i, hx⟩
      · rintro ⟨i, hx⟩; exact ⟨i + 1, i, by omega, hx⟩
    have hlim : Tendsto (fun N => μ.real (S N)) atTop (𝓝 (μ.real (⋃ i, s i))) := by
      have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
      rw [hU] at h
      exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h
    have hdiff : ∀ N, g (⋃ i, s i) = g (S N) + g ((⋃ i, s i) \ S N) := fun N => by
      rw [← hg_add _ _ (hSm N) (hA.diff (hSm N)) disjoint_sdiff_right,
        Set.union_sdiff_cancel (hSA N)]
    have hS : Tendsto (fun N => g (S N)) atTop (𝓝 (g (⋃ i, s i))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun N => g (⋃ i, s i) - 2 * C * (μ.real (⋃ i, s i) - μ.real (S N)))
        (h := fun _ => g (⋃ i, s i)) ?_ tendsto_const_nhds ?_ ?_
      · have h := tendsto_const_nhds (x := g (⋃ i, s i)) |>.sub
          (tendsto_const_nhds (x := 2 * C) |>.mul
            (tendsto_const_nhds (x := μ.real (⋃ i, s i)) |>.sub hlim))
        simpa using h
      · intro N
        have h1 := hdiff N
        have h2 := hg_le _ (hA.diff (hSm N))
        rw [measureReal_sdiff (hSA N) (hSm N)] at h2
        dsimp only
        linarith
      · intro N
        have h1 := hdiff N
        have h2 := hg_nonneg _ (hA.diff (hSm N))
        dsimp only
        linarith
    exact hS.congr fun N => hfin s hs hd N
  -- Step 4: the finite measure `ρ = ν + C μ`.
  let ρ : Measure α := Measure.ofMeasurable (fun A _ => ENNReal.ofReal (g A))
    (by simp [hg_def, hν0]) (fun s hs hd => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hg_nonneg _ (hs i)) (hcount s hs hd).summable,
        (hcount s hs hd).tsum_eq])
  have hρ : ∀ A, MeasurableSet A → ρ A = ENNReal.ofReal (g A) := fun A hA =>
    Measure.ofMeasurable_apply A hA
  have : IsFiniteMeasure ρ := ⟨by rw [hρ _ MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩
  -- Step 5: `ρ ≪ μ`, since `μ(A) = 0` forces `0 ≤ g(A) ≤ 2C μ(A) = 0`.
  have hρμ : ρ ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    have hr : μ.real A = 0 := by rw [measureReal_def, h0, ENNReal.toReal_zero]
    rw [hρ A hA, ENNReal.ofReal_eq_zero]
    have := hg_le A hA
    rwa [hr, mul_zero] at this
  -- Step 6: Radon–Nikodym.  The singular part of `ρ ≪ μ` vanishes, so `ρ = f μ`, `f = dρ/dμ`.
  have hρ_eq : μ.withDensity (ρ.rnDeriv μ) = ρ := by
    have h := Measure.haveLebesgueDecomposition_add ρ μ
    rw [Measure.singularPart_eq_zero_of_ac hρμ, zero_add] at h
    exact h.symm
  set f := ρ.rnDeriv μ with hf_def
  have hf_meas : Measurable f := Measure.measurable_rnDeriv ρ μ
  have hf_lint : ∀ A, MeasurableSet A → ∫⁻ x in A, f x ∂μ = ENNReal.ofReal (g A) := fun A hA => by
    rw [← withDensity_apply _ hA, hρ_eq, hρ A hA]
  -- Step 7: `f ≤ 2C` `μ`-a.e., since `∫_A f dμ = g(A) ≤ 2C μ(A)` for every measurable `A`.
  have hf_le : f ≤ᵐ[μ] fun _ => ENNReal.ofReal (2 * C) := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf_meas fun A hA _ => ?_
    rw [hf_lint A hA, setLIntegral_const, ← ENNReal.ofReal_toReal (measure_ne_top μ A),
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (hg_le A hA)
  -- Step 8: truncation `θ = min(f, 2C) - C`, equal to `f - C` `μ`-a.e.
  refine ⟨fun x => min (f x).toReal (2 * C) - C,
    (hf_meas.ennreal_toReal.min measurable_const).sub_const C, ?_, ?_⟩
  · intro x
    rw [abs_le]
    have h1 : 0 ≤ min (f x).toReal (2 * C) := le_min ENNReal.toReal_nonneg (by linarith)
    have h2 : min (f x).toReal (2 * C) ≤ 2 * C := min_le_right _ _
    constructor <;> linarith
  · intro A hA
    have hfin_int : ∫⁻ x in A, f x ∂μ ≠ ∞ := by rw [hf_lint A hA]; exact ENNReal.ofReal_ne_top
    have hint : Integrable (fun x => (f x).toReal) (μ.restrict A) :=
      integrable_toReal_of_lintegral_ne_top hf_meas.aemeasurable hfin_int
    have h1 : ∫ x in A, (min (f x).toReal (2 * C) - C) ∂μ = ∫ x in A, ((f x).toReal - C) ∂μ := by
      refine setIntegral_congr_ae hA ?_
      filter_upwards [hf_le] with x hx _
      rw [min_eq_left (ENNReal.toReal_le_of_le_ofReal (by linarith) hx)]
    rw [h1, integral_sub hint (integrable_const C), setIntegral_const,
      integral_toReal hf_meas.aemeasurable ?_, hf_lint A hA, ENNReal.toReal_ofReal (hg_nonneg A hA)]
    · simp only [hg_def, smul_eq_mul]; ring
    · exact ae_restrict_of_ae (hf_le.mono fun x hx => lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
/-- Extension from indicators for the duality `(L¹(μ))* = L^∞(μ)` (Riesz), used in Simon Ch. 6,
proof of Theorem 2.34 (p. 142).  Let `μ` be finite and let `F` be additive and homogeneous with
`|F f| ≤ C ∫ |f| dμ` on `μ`-integrable functions.  Let `θ` be measurable with `|θ| ≤ M`, and
suppose `F (1_A) = ∫_A θ dμ` for every measurable `A`.  Then `F f = ∫ f θ dμ` for every integrable
`f`.  Both sides are additive and `L¹`-Lipschitz, hence continuous on `α →₁[μ] ℝ`, so
`Integrable.induction` extends the identity from multiples of indicators to all of `L¹(μ)`. -/
theorem Submission.constancy_riesz_eq_integral_mul_of_indicator_eq : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α), IsFiniteMeasure μ → ∀ (F : (α → ℝ) → ℝ) (C : ℝ), (∀ f g : α → ℝ, Integrable f μ → Integrable g μ → F (f + g) = F f + F g) → (∀ (c : ℝ) (f : α → ℝ), Integrable f μ → F (c • f) = c * F f) → (∀ f : α → ℝ, Integrable f μ → |F f| ≤ C * ∫ x, |f x| ∂μ) → ∀ (θ : α → ℝ) (M : ℝ), Measurable θ → (∀ x, |θ x| ≤ M) → (∀ A : Set α, MeasurableSet A → F (A.indicator 1) = ∫ x in A, θ x ∂μ) → ∀ f : α → ℝ, Integrable f μ → F f = ∫ x, f x * θ x ∂μ := by
  intro α _ μ _ F C hadd hsmul hbound θ M hθ hθM hind f hf
  -- Step 2: `F (g - h) = F g - F h`, since `g - h = g + (-1) • h`.
  have hsub : ∀ g h : α → ℝ, Integrable g μ → Integrable h μ → F (g - h) = F g - F h := by
    intro g h hg hh
    have e : g - h = g + (-1 : ℝ) • h := by rw [neg_one_smul, sub_eq_add_neg]
    rw [e, hadd _ _ hg (hh.smul _), hsmul _ _ hh]
    ring
  -- Step 3: `|F g - F h| = |F (g - h)| ≤ C * ∫ |g - h| dμ`.
  have hFlip : ∀ g h : α → ℝ, Integrable g μ → Integrable h μ →
      |F g - F h| ≤ C * ∫ x, |g x - h x| ∂μ := by
    intro g h hg hh
    rw [← hsub g h hg hh]
    exact hbound _ (hg.sub hh)
  -- Step 4: `F` respects `μ`-a.e. equality.
  have hFae : ∀ g h : α → ℝ, Integrable g μ → Integrable h μ → g =ᵐ[μ] h → F g = F h := by
    intro g h hg hh hgh
    have h0 : ∫ x, |g x - h x| ∂μ = 0 := integral_eq_zero_of_ae (by
      filter_upwards [hgh] with x hx
      simp [hx])
    have hle := hFlip g h hg hh
    rw [h0, mul_zero] at hle
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)
  -- Step 5: `g θ` is integrable for integrable `g`, since `θ` is measurable and `|θ| ≤ M`.
  have hθbd : ∀ᵐ x ∂μ, ‖θ x‖ ≤ M := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact hθM x
  have hint : ∀ g : α → ℝ, Integrable g μ → Integrable (fun x => g x * θ x) μ :=
    fun g hg => hg.mul_bdd hθ.aestronglyMeasurable hθbd
  -- Step 6: `|∫ g θ dμ - ∫ h θ dμ| ≤ ∫ |g - h| |θ| dμ ≤ M * ∫ |g - h| dμ`.
  have hIlip : ∀ g h : α → ℝ, Integrable g μ → Integrable h μ →
      |∫ x, g x * θ x ∂μ - ∫ x, h x * θ x ∂μ| ≤ M * ∫ x, |g x - h x| ∂μ := by
    intro g h hg hh
    rw [← integral_sub (hint g hg) (hint h hh), ← integral_const_mul]
    refine abs_integral_le_integral_abs.trans (integral_mono ((hint g hg).sub (hint h hh)).abs
      ((hg.sub hh).abs.const_mul _) fun x => ?_)
    show |g x * θ x - h x * θ x| ≤ M * |g x - h x|
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hθM x) (abs_nonneg _)
  -- Step 7: if `|Φ g - Φ h| ≤ K * ∫ |g - h| dμ`, then `u ↦ Φ u` is `K⁺`-Lipschitz, hence
  -- continuous, on `α →₁[μ] ℝ`, because `‖u - v‖ = ∫ |u - v| dμ`.
  have hcont : ∀ (Φ : (α → ℝ) → ℝ) (K : ℝ),
      (∀ g h : α → ℝ, Integrable g μ → Integrable h μ →
        |Φ g - Φ h| ≤ K * ∫ x, |g x - h x| ∂μ) →
      Continuous fun u : α →₁[μ] ℝ => Φ u := by
    intro Φ K hΦ
    refine LipschitzWith.continuous (LipschitzWith.of_dist_le' (K := K) fun u v => ?_)
    rw [Real.dist_eq, dist_eq_norm, L1.norm_eq_integral_norm]
    refine (hΦ _ _ (L1.integrable_coeFn u) (L1.integrable_coeFn v)).trans_eq ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u v] with x hx
    rw [hx, Pi.sub_apply, Real.norm_eq_abs]
  -- Step 8: `Integrable.induction` for `F g = ∫ g θ dμ`.
  refine Integrable.induction (fun g => F g = ∫ x, g x * θ x ∂μ) ?_ ?_ ?_ ?_ hf
  · -- (a) multiples of indicators of measurable sets
    intro c s hs _
    have hs1 : Integrable (s.indicator (1 : α → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hs
    have e : (s.indicator fun _ => c) = c • s.indicator (1 : α → ℝ) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [e, hsmul c _ hs1, hind s hs, ← integral_const_mul, ← integral_indicator hs]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ s <;> simp [hx]
  · -- (b) sums
    intro g h _ hg hh hPg hPh
    rw [hadd g h hg hh, hPg, hPh, ← integral_add (hint g hg) (hint h hh)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, add_mul]
  · -- (c) the set where the two continuous maps on `α →₁[μ] ℝ` agree is closed
    exact isClosed_eq (hcont F C hFlip) (hcont (fun g => ∫ x, g x * θ x ∂μ) M hIlip)
  · -- (d) `μ`-a.e. congruence
    intro g h hgh hg hPg
    have hh : Integrable h μ := hg.congr hgh
    rw [← hFae g h hg hh hgh, hPg]
    refine integral_congr_ae ?_
    filter_upwards [hgh] with x hx
    rw [hx]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
