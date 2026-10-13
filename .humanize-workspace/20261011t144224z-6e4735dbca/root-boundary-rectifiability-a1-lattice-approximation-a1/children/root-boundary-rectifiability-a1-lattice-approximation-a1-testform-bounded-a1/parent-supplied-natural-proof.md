# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.lattice_approximation-a1`
- Child DAG node: `root.boundary_rectifiability-a1.lattice_approximation-a1.testform_bounded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Notation paragraph of the parent proof (‖ω‖ := sup_x|ω(x)| is finite for test forms because they are continuous with compact support). Here that finiteness is proved in the form of an explicit positive bound.

1. (|·| is continuous on Λⁿ(ℝ^P).)
  - For each fixed v ∈ (ℝ^P)ⁿ, the evaluation α ↦ α(v) is continuous on the space of continuous alternating maps (continuous_eval_const; the instance is ContinuousAlternatingMap.instContinuousEvalConst).
  - Hence, for each I : Fin n → Fin P, the map α ↦ (if I is strictly increasing then α(e_{I(0)}, …, e_{I(n−1)})² else 0) is continuous: it is either the square of a continuous function or the constant 0.
  - The finite sum over I is continuous (continuous_finsetSum), and composing with the continuous square root (Real.continuous_sqrt) shows that α ↦ |α| is continuous.
2. (Continuity of f.) ω is smooth (ContDiff ℝ ∞; this is the first component of the test-form property of ω), hence continuous. So f(x) := |ω(x)| is continuous on ℝ^P, as a composition of continuous maps.
3. (Compact support of f.) If ω(x) = 0 then f(x) = |0| = 0 (covectorEuclideanNorm_zero). Hence support f ⊆ support ω ⊆ tsupport ω. Since ω has compact support, f has compact support (HasCompactSupport.mono'). (Lean remark: in this environment use mono' here; HasCompactSupport.comp_left produced a whnf heartbeat timeout in a scratch check, while mono' compiled.)
4. (Boundedness.) A continuous, compactly supported real function is bounded (Continuous.bounded_above_of_compact_support): there is C₀ ∈ ℝ with |f(x)| ≤ C₀ for all x ∈ ℝ^P. In particular C₀ ≥ |f(0)| ≥ 0.
5. Put C := C₀ + 1. Then C ≥ 1 > 0, and for every x, f(x) ≤ |f(x)| ≤ C₀ < C. ∎

## Key steps

1. α ↦ |α| is continuous: evaluations of continuous alternating maps are continuous, then a finite sum of squares and a square root.
2. x ↦ |ω(x)| is continuous and has compact support, because ω is smooth with compact support and |0| = 0.
3. A continuous compactly supported real function is bounded by some C₀ ≥ 0; take C := C₀ + 1 > 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git show d8d46c9:GMT/Ch06/{Contract,Submission}.lean; cmp Contract.lean Submission.lean; cmp with snapshot project/GMT/Ch06/Contract.lean (all byte-identical)`
- `cat -n GMT/Ch06/Contract.lean (DeformationTheorem, IsLatticeChain, LatticeFaceIndex, IsIntegerMultiplicity, Eucl)`
- `cat simongmt Chapter06/Mass.lean, Currents.lean, Forms.lean, FormSupNorm.lean (covectorEuclideanNorm{_zero,_nonneg,_neg}, massAdmissibleOn, massOn, mass, le_massOn, GeometricCurrentOn.boundary_apply, exteriorDerivativeTestOn, WeaklyConvergesOn, TestFormOn, testFormEuclideanSupNorm)`
- `grep -rn 'covectorEuclideanNorm_smul|covectorEuclideanNorm_continuous|continuous_covectorEuclideanNorm|abs_apply_le|le_mass_mul|mass_mul_sup' simongmt/Poincare/SimonGMT (only Chapter01 abs_apply_le_integral_vectorFunctionalEnvelopeMeasure; no mass inequality, homogeneity or continuity lemma for covectorEuclideanNorm)`
- `rg -n 'theorem map_linearDependent' mathlib/Mathlib`
- `rg -n 'theorem fintype_card_le_finrank' mathlib/Mathlib`
- `rg -n 'theorem finrank_euclideanSpace_fin' mathlib/Mathlib`
- `rg -n 'bounded_above_of_compact_support' mathlib/Mathlib`
- `rg -n 'ContinuousEvalConst' mathlib/Mathlib/Topology/Algebra/Module/Alternating`
- `rg -n "theorem mono'" mathlib/Mathlib/Topology/Algebra/Support.lean`
- `rg -n 'theorem eventually_ne_nhds' mathlib/Mathlib/Topology/Separation`
- `rg -n 'theorem tendsto_toReal|theorem tendsto_ofReal|protected theorem Tendsto.const_mul' mathlib/Mathlib/Topology/Instances/ENNReal`
- `rg -n 'theorem tendsto_one_div_add_atTop_nhds_zero_nat' mathlib/Mathlib/Analysis/SpecificLimits`
- `lake env lean Scratch/Probe.lean (#check ENNReal.ofReal_le_iff_le_toReal, squeeze_zero_norm', ENNReal.Tendsto.mul_const, ContinuousAlternatingMap.ext, AlternatingMap.map_linearDependent, continuous_eval_const on Covector (Eucl P) n)`
- `python3 gmt-compare.py contract_scope replay (open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `lake build GMT.Ch06.Submission (scratch /tmp/la-decomp-0Vm2C2/proj at frozen commit d8d46c9, pinned shared packages, no package rebuild)`
- `lake env lean Scratch/Split.lean -o Split.olean (4 children fully proved; parent br_lattice_approximation and literal variant br_lattice_approximation_v0 from the children plus a stand-in for br_top_dim_lattice_approximation; #print axioms)`
- `gmt-compare.py child_modules -> Checks/Challenge_{0..3}.lean (sorry) and Checks/Solution_{0..3}.lean (exact Submission.X); lake env lean on each (0 errors; solutions use only propext, Classical.choice, Quot.sound)`
- `python3 scan of dag.json lean_name values (155 nodes; no br_la_* collision)`
- `grep -n 'Evidently (1), (2)|^2.4|^2.5' book/sources/chapter-06-source.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/tmp/la-decomp-0Vm2C2/proj/Scratch/Probe.lean`
- `/tmp/la-decomp-0Vm2C2/proj/Scratch/Split.lean`
- `/tmp/la-decomp-0Vm2C2/proj/Scratch/C2c.lean`
- `/tmp/la-decomp-0Vm2C2/proj/Checks/Challenge_0.lean`
- `/tmp/la-decomp-0Vm2C2/proj/Checks/Solution_0.lean`

Snapshot (project d8d46c95, Mathlib 25730c7c): the frozen Ch06 contract is byte-identical to Submission.lean at the frozen commit.

What the libraries do and do not provide:
- SimonGMT has covectorEuclideanNorm with only _zero, _nonneg and _neg lemmas. It has massAdmissibleOn, massOn and mass with le_massOn, massOn_mono and lower semicontinuity. It has boundary_apply and exteriorDerivativeTestOn.
- SimonGMT has no mass inequality, no homogeneity or continuity lemma for covectorEuclideanNorm, and no vanishing lemma for degree > P.
- FormSupNorm.lean defines testFormEuclideanSupNorm (a sup over U only, with no boundedness lemma), so it is not used.
- Mathlib supplies AlternatingMap.map_linearDependent, LinearIndependent.fintype_card_le_finrank, finrank_euclideanSpace_fin, ContinuousAlternatingMap.instContinuousEvalConst, HasCompactSupport.mono', Continuous.bounded_above_of_compact_support, ENNReal.ofReal_le_iff_le_toReal, ENNReal.tendsto_toReal, eventually_ne_nhds, squeeze_zero_norm', ENNReal.Tendsto.const_mul/mul_const, ENNReal.tendsto_ofReal and tendsto_one_div_add_atTop_nhds_zero_nat.
- Using these, all four children were proved in scratch with axioms [propext, Classical.choice, Quot.sound]. HasCompactSupport.comp_left caused a whnf heartbeat timeout; mono' works, and the testform_bounded proof says so.

Comparator checks: with the exact comparator child scope, the four NodeChallenge modules elaborate and the four NodeSolution modules close. The parent typechecks from the children plus the sibling br_top_dim_lattice_approximation, with sorryAx only from that sibling's stand-in.

Names: no br_la_* name occurs in dag.json or SimonGMT.

These checks do not certify the sibling br_top_dim_lattice_approximation or DeformationTheorem; both are separate DAG nodes.
