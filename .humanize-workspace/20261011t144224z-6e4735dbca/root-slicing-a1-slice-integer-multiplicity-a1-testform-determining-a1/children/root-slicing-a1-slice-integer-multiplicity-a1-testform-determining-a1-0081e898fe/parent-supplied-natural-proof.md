# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.current_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝ^P = Eucl P. D^k(U) = TestFormOn U k, a submodule of the k-forms on ℝ^P: C^∞ forms with compact support and tsupport ⊆ U. Addition and subtraction in D^k(U) act pointwise on the underlying forms. S ∈ D_k(U) = GeometricCurrentOn U k is an ℝ-linear functional S : D^k(U) → ℝ (S.toCurrent) with the continuity field S.continuous': TestFormOnConverges ϖ 0 implies S(ϖ_l) → 0.
1. (Unpacking.) By the hypothesis TestFormOnConverges e ω there is a compact K ⊆ ℝ^P with K ⊆ U such that tsupport e_l ⊆ K for every l, tsupport ω ⊆ K, and for every i ∈ ℕ, iteratedFDeriv ℝ i e_l → iteratedFDeriv ℝ i ω uniformly on K as l → ∞.
2. (Differences converge to 0.) For l ∈ ℕ put ϖ_l := e_l − ω ∈ D^k(U); its underlying form is the pointwise difference e_l − ω. We check TestFormOnConverges ϖ 0 with the same K.
(a) tsupport ϖ_l ⊆ tsupport e_l ∪ tsupport ω ⊆ K (tsupport_sub and Step 1).
(b) The underlying form of 0 ∈ D^k(U) is the zero form, whose tsupport is ∅ ⊆ K.
(c) Fix i ∈ ℕ. e_l and ω are C^∞, hence C^i, so iteratedFDeriv ℝ i ϖ_l = iteratedFDeriv ℝ i e_l − iteratedFDeriv ℝ i ω (iteratedFDeriv_sub). Also iteratedFDeriv ℝ i 0 = 0. Hence for every x ∈ K, dist(iteratedFDeriv ℝ i 0 x, iteratedFDeriv ℝ i ϖ_l x) = ‖iteratedFDeriv ℝ i e_l x − iteratedFDeriv ℝ i ω x‖ = dist(iteratedFDeriv ℝ i ω x, iteratedFDeriv ℝ i e_l x). Let ε > 0. The uniform convergence in Step 1 gives an l₀ such that the right-hand side is < ε for all l ≥ l₀ and all x ∈ K. So iteratedFDeriv ℝ i ϖ_l → iteratedFDeriv ℝ i 0 uniformly on K (Metric.tendstoUniformlyOn_iff).
By (a), (b) and (c), and since K is compact with K ⊆ U, TestFormOnConverges ϖ 0 holds.
3. (Continuity at 0.) Applying the continuity field of S (GeometricCurrentOn.continuous') to Step 2 gives S(ϖ_l) → 0 as l → ∞.
4. (Linearity.) S is linear, so S(ϖ_l) = S(e_l − ω) = S(e_l) − S(ω) (LinearMap.map_sub). Hence S(e_l) − S(ω) → 0. Adding the constant S(ω) (Tendsto.add_const) gives S(e_l) = (S(e_l) − S(ω)) + S(ω) → 0 + S(ω) = S(ω). ∎

## Key steps

1. Unpack TestFormOnConverges e ω: a compact K ⊆ U contains every tsupport e_l and tsupport ω, and every derivative converges uniformly on K.
2. The differences ϖ_l := e_l − ω satisfy TestFormOnConverges ϖ 0 on the same K (tsupport_sub, iteratedFDeriv_sub, tsupport 0 = ∅).
3. The continuity field of S gives S(ϖ_l) → 0.
4. Linearity S(ϖ_l) = S(e_l) − S(ω), then adding the constant S(ω), gives S(e_l) → S(ω).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c95 into scratch /tmp/tdet-decomp-PlZhE0 (.lake/packages -> lake-packages-25730c7c); sha256sum GMT/Ch06/{Contract,Submission}.lean and snapshot project/GMT/Ch06/Contract.lean (all ea3ee0dd…)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (namespace GMT.Ch06; open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; open Poincare.SimonGMT.Chapter06/Chapter03/Chapter01)`
- `sed simongmt Chapter06/Currents.lean (TestFormOn, TestFormOnConverges, GeometricCurrentOn.continuous' only at 0, GeometricCurrentOn.ext) and Chapter06/FixedSupportCurrentTopology.lean, Chapter06/Forms.lean (Covector = Eucl P [⋀^Fin k]→L[ℝ] ℝ)`
- `grep -rn -i 'countable|separable|SecondCountable|dense' simongmt Poincare/SimonGMT/Chapter06 (only a local FirstCountableTopology in FixedSupportCurrentTopology.lean; no separability or countable-determining lemma)`
- `python3 scan of dag.json (394 nodes): lean_name collisions for slicing_im_td_countable_seq_dense / slicing_im_td_current_tendsto (none); lean_statements mentioning TestFormOnConverges or Countable+TestFormOn; cmb_exists_compactly_contained_exhaustion -> root.compactness_mass_bounds-a1.exhaustion-a1 (accepted, candidate cb89cc7f, identical lean_statement)`
- `git diff 9f6ec514 cb89cc7f -- GMT (accepted exhaustion proof, 45 lines, no imports); git diff 9f6ec514 bfaf075e -- GMT (cmb_exists_countable_dense_testForms: sup-norm density only)`
- `read controller _recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint) and tests/test_worktrees.py::test_cross_branch_accepted_same_type_is_reused`
- `rg 'theorem IsSeparable.of_separableSpace|IsSeparable.exists_countable_dense_subset|theorem tendsto_iff_tendstoUniformly|tendstoUniformlyOn_iff_tendstoUniformly_comp_coe|theorem iteratedFDeriv_sub|ContDiff.continuous_iteratedFDeriv|def toMultilinearMapLinear|def toContinuousMultilinearMapLinear|toMultilinearMap_injective|toContinuousMultilinearMap_injective|FiniteDimensional.proper_real|pseudoMetrizableSpace_pi|Module.Finite.multilinearMap' mathlib/Mathlib`
- `lake env lean Scratch/Inst.lean, Inst2.lean, Inst3.lean (#synth FiniteDimensional/SecondCountableTopology for Covector (Eucl P) k and Eucl P [×i]→L[ℝ] Covector (Eucl P) k fail by search; explicit Module.Finite.of_injective and @secondCountable_of_proper _ _ (FiniteDimensional.proper_real _) succeed; C(K,F_i), product and PseudoMetrizableSpace instances then found)`
- `lake env lean Scratch/Seq.lean and Scratch/Dense.lean (child proofs; axioms [propext, Classical.choice, Quot.sound]); Scratch/DenseNoImp1.lean, DenseNoImp2.lean (both extra imports required)`
- `lake env lean Scratch/Stmts.lean (parent assembly from the three sorry'd child types in comparator scope)`
- `lake build GMT.Ch06.Submission with exhaustion, seq_dense, current_tendsto and parent inserted before main_theorem (0 errors; only the frozen main_theorem sorry)`
- `gmt-compare.py child_modules(mode='contract') for exhaustion, seq_dense, current_tendsto and parent; lake env lean Cmp/*_NodeChallenge.lean and Cmp/*_NodeSolution.lean (0 errors; solution axioms [propext, Classical.choice, Quot.sound])`
- `python3 lean_contract.validate_lean_statement on all three child types and the parent type (pass)`
- `sed -n 1290,1330p book/chapter-06.txt (Simon 4.5 proof: 'by considering a countable dense set of ω ∈ Dⁿ(U)'; no printed proof)`
- `independent reviewer subagent: /tmp/tdet-review-YuJKAK/Review1.lean (assembly from the three child types; verdict ACCEPT)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/CompactConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-exhaustion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-testform-separable-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-cmb-exists-compactly-contained-exhaustion.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/tests/test_worktrees.py`
- `/tmp/tdet-decomp-PlZhE0/Scratch/Stmts.lean`
- `/tmp/tdet-decomp-PlZhE0/Scratch/Seq.lean`
- `/tmp/tdet-decomp-PlZhE0/Scratch/Dense.lean`
- `/tmp/tdet-decomp-PlZhE0/Scratch/Inst3.lean`
- `/tmp/tdet-decomp-PlZhE0/GMT/Ch06/Submission.lean`
- `/tmp/tdet-decomp-PlZhE0/Cmp/parent_NodeSolution.lean`
- `/tmp/tdet-decomp-PlZhE0/decomposition-draft-subproblems.json`
- `/tmp/tdet-review-YuJKAK/Review1.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Submission.lean is byte-identical to Contract.lean, so child types can use only Contract, SimonGMT and Mathlib names. In the comparator scope (namespace GMT.Ch06 with the Contract's opens) all three child types and the parent type elaborate and pass validate_lean_statement.

SimonGMT provides TestFormOn, TestFormOnConverges, GeometricCurrentOn (its continuity is stated only at 0) and GeometricCurrentOn.ext. It has no separability, countable-dense or countable-determining lemma for test forms. The only related accepted DAG declaration, cmb_exists_countable_dense_testForms, gives sup-norm density only, which is too weak. The accepted cmb_exists_compactly_contained_exhaustion (node root.compactness_mass_bounds-a1.exhaustion-a1, accepted, candidate cb89cc7f, 45 lines, no imports) has a byte-identical lean_statement to the exhaustion child. The controller reuses such a node without starting a new worker.

Mathlib supplies every step:
- ContinuousMap.instSecondCountableTopology; needs import Mathlib.Topology.ContinuousMap.SecondCountableSpace.
- Module.Finite.multilinearMap; needs import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional.
- Module.Finite.of_injective, with ContinuousMultilinearMap.toMultilinearMapLinear/toMultilinearMap_injective and ContinuousAlternatingMap.toContinuousMultilinearMapLinear/toContinuousMultilinearMap_injective.
- FiniteDimensional.proper_real and secondCountable_of_proper. They must be applied explicitly, because instance search fails for Covector (Eucl P) k and Eucl P [×i]→L[ℝ] Covector (Eucl P) k.
- TopologicalSpace.IsSeparable.of_separableSpace, IsSeparable.exists_countable_dense_subset, mem_closure_iff_seq_limit.
- ContinuousMap.tendsto_iff_tendstoUniformly, which needs explicit arguments.
- tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, iteratedFDeriv_sub, ContDiff.continuous_iteratedFDeriv, Metric.tendstoUniformlyOn_iff.

In the scratch build, both new children are proved without sorry (about 55 and 25 lines). Together with the accepted exhaustion proof they give the parent type in about 15 lines. All comparator solution modules compile with axioms [propext, Classical.choice, Quot.sound]. The two new names are unused in the DAG, the snapshot project and SimonGMT. Book p. 157 (Simon 4.5) only invokes 'a countable dense set of ω ∈ Dⁿ(U)' without a proof.
