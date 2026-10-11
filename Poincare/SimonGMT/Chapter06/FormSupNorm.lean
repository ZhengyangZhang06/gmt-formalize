module

public import Poincare.SimonGMT.Chapter06.Mass

@[expose] public section

/-!
# Simon GMT, Chapter 6, formula (1.15)

This module packages the literal Euclidean coefficient supremum norm of a
compactly supported smooth test form.  The pointwise coefficient norm is the
one defined in `Mass.lean`, not the alternating-map operator norm.
-/

open Set

namespace Poincare.SimonGMT.Chapter06

noncomputable section

/-- Simon (6.1.15): the supremum over the domain of the Euclidean coefficient
norm of a compactly supported smooth test form. -/
def testFormEuclideanSupNorm {P n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin P))} (omega : TestFormOn U n) : ℝ :=
  sSup (range fun x : U ↦
    covectorEuclideanNorm
      ((omega : DifferentialForm (EuclideanSpace ℝ (Fin P)) n) x))

end

end Poincare.SimonGMT.Chapter06
