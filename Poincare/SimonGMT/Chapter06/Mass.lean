module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.LiminfLimsup
public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Simon GMT, Chapter 6, §§1.15, 2.4--2.5, 2.14: mass and weak convergence

Simon's mass uses the Euclidean inner-product norm of the covector
coefficients, as emphasized in Remark 2.6. We use the coefficients on the
increasing coordinate tuples explicitly, rather than the operator/comass
norm used by Mathlib's continuous alternating maps. Currents carry the
source continuity condition on the test forms supported in their domain.
-/

open Filter Function Set
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

/-- The Euclidean coefficient norm of an `n`-covector on `ℝᴾ`, used in
Simon (6.1.15) and (6.2.4). The coordinate wedges with strictly increasing
indices are orthonormal; their coefficients are the values on those tuples
of the standard orthonormal basis. -/
def covectorEuclideanNorm {P n : ℕ}
    (alpha : Covector (EuclideanSpace ℝ (Fin P)) n) : ℝ :=
  Real.sqrt (∑ I : Fin n → Fin P,
    if StrictMono I then
      (alpha (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2
    else 0)

@[simp] theorem covectorEuclideanNorm_zero (P n : ℕ) :
    covectorEuclideanNorm (0 : Covector (EuclideanSpace ℝ (Fin P)) n) = 0 := by
  classical
  simp [covectorEuclideanNorm]

theorem covectorEuclideanNorm_nonneg {P n : ℕ}
    (alpha : Covector (EuclideanSpace ℝ (Fin P)) n) :
    0 ≤ covectorEuclideanNorm alpha :=
  Real.sqrt_nonneg _

@[simp] theorem covectorEuclideanNorm_neg {P n : ℕ}
    (alpha : Covector (EuclideanSpace ℝ (Fin P)) n) :
    covectorEuclideanNorm (-alpha) = covectorEuclideanNorm alpha := by
  classical
  simp [covectorEuclideanNorm]

/-- The source admissible forms for `M_W(T)`: smooth compactly supported
forms in `U`, supported in `W`, whose Euclidean coefficient norm is at most
one at every point. Values outside `U` vanish by the test-form support
condition. -/
def massAdmissibleOn {P : ℕ} (U : Set (EuclideanSpace ℝ (Fin P)))
    (n : ℕ) (W : Set (EuclideanSpace ℝ (Fin P))) :
    Set (TestFormOn U n) :=
  {omega | tsupport (omega : DifferentialForm (EuclideanSpace ℝ (Fin P)) n) ⊆ W ∧
    ∀ x, covectorEuclideanNorm
      ((omega : DifferentialForm (EuclideanSpace ℝ (Fin P)) n) x) ≤ 1}

/-- Simon (6.2.5): local mass of a continuous current in `U`, with precisely
the Euclidean covector norm used by the source. The supremum is represented
in `ℝ≥0∞`; since the zero form is admissible, replacing negative evaluations
by zero does not change this nonnegative supremum. -/
def GeometricCurrentOn.massOn {P n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin P))}
    (T : GeometricCurrentOn U n) (W : Set (EuclideanSpace ℝ (Fin P))) : ℝ≥0∞ :=
  sSup ((fun omega ↦ ENNReal.ofReal (T omega)) '' massAdmissibleOn U n W)

/-- Simon (6.2.4): total mass is local mass on the full current domain. -/
def GeometricCurrentOn.mass {P n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin P))}
    (T : GeometricCurrentOn U n) : ℝ≥0∞ :=
  T.massOn U

/-- Local mass is monotone under enlargement of the test-form support
region. -/
theorem GeometricCurrentOn.massOn_mono {P n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin P))}
    (T : GeometricCurrentOn U n) {W₁ W₂ : Set (EuclideanSpace ℝ (Fin P))}
    (hW : W₁ ⊆ W₂) : T.massOn W₁ ≤ T.massOn W₂ := by
  apply sSup_le_sSup
  rintro r ⟨omega, homega, rfl⟩
  exact ⟨omega, ⟨homega.1.trans hW, homega.2⟩, rfl⟩

/-- Every admissible test evaluation is bounded by local mass. -/
theorem GeometricCurrentOn.le_massOn {P n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin P))}
    (T : GeometricCurrentOn U n) {W : Set (EuclideanSpace ℝ (Fin P))}
    {omega : TestFormOn U n} (homega : omega ∈ massAdmissibleOn U n W) :
    ENNReal.ofReal (T omega) ≤ T.massOn W :=
  le_sSup ⟨omega, homega, rfl⟩

/-- Simon (6.2.14): local mass is lower semicontinuous under weak
convergence of continuous currents on the domain. The proof works for every
support region, in particular each open `W ⊆ U` as in the source. -/
theorem WeaklyConvergesOn.massOn_le_liminf {P n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin P))}
    {Tseq : ℕ → GeometricCurrentOn U n} {T : GeometricCurrentOn U n}
    (h : WeaklyConvergesOn Tseq T) (W : Set (EuclideanSpace ℝ (Fin P))) :
    T.massOn W ≤ liminf (fun j ↦ (Tseq j).massOn W) atTop := by
  apply sSup_le
  rintro r ⟨omega, homega, rfl⟩
  calc
    ENNReal.ofReal (T omega) =
        liminf (fun j ↦ ENNReal.ofReal (Tseq j omega)) atTop :=
      (ENNReal.tendsto_ofReal (h omega)).liminf_eq.symm
    _ ≤ liminf (fun j ↦ (Tseq j).massOn W) atTop :=
      liminf_le_liminf (Eventually.of_forall fun j ↦ (Tseq j).le_massOn homega)

end

end Poincare.SimonGMT.Chapter06
