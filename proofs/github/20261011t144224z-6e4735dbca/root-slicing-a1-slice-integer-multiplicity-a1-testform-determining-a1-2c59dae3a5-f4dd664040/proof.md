# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.seq_dense-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝ^P = Eucl P. D^k(U) = TestFormOn U k: forms ω : ℝ^P → Covector (Eucl P) k that are C^∞ (ContDiff ℝ ∞), have compact support, and satisfy tsupport ω ⊆ U; D^k(U) is a real vector space (a submodule of all k-forms). For i ∈ ℕ let F_i := ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝ^P) (Covector (Eucl P) k) (Lean: Eucl P [×i]→L[ℝ] Covector (Eucl P) k), the space in which iteratedFDeriv ℝ i ω x takes its values. K carries the subspace topology of ℝ^P and C(K, F_i) the compact-open topology. Fix P, k, U and a compact K ⊆ ℝ^P with K ⊆ U.
1. (Finite-dimensionality.) Let G be a finite-dimensional real normed space and i ∈ ℕ. The forgetful map ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝ^P) G → MultilinearMap ℝ (fun _ : Fin i => ℝ^P) G is ℝ-linear and injective (ContinuousMultilinearMap.toMultilinearMapLinear, ContinuousMultilinearMap.toMultilinearMap_injective). Its target is finite-dimensional because ℝ^P and G are (Module.Finite.multilinearMap, from Mathlib.LinearAlgebra.Multilinear.FiniteDimensional), and a module with an injective linear map into a finite-dimensional space is finite-dimensional (Module.Finite.of_injective). So ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝ^P) G is finite-dimensional. With G = ℝ and i = k this applies to ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ^P) ℝ. The map α ↦ α.toContinuousMultilinearMap from Covector (Eucl P) k = ℝ^P [⋀^Fin k]→L[ℝ] ℝ into that space is linear and injective (ContinuousAlternatingMap.toContinuousMultilinearMapLinear, ContinuousAlternatingMap.toContinuousMultilinearMap_injective), so Covector (Eucl P) k is finite-dimensional. Applying the first claim again with G = Covector (Eucl P) k shows that every F_i is finite-dimensional.
2. (Second countability.) A finite-dimensional real normed space is proper (FiniteDimensional.proper_real), and a proper metric space is second countable (secondCountable_of_proper). Hence every F_i is second countable. [Lean: type-class search does not find these instances for F_i. Supply them explicitly as `@secondCountable_of_proper _ _ (FiniteDimensional.proper_real F_i)`, with F_i written out, after constructing the FiniteDimensional instances of Step 1 by Module.Finite.of_injective.] K is a compact space (isCompact_iff_compactSpace) and Hausdorff, hence locally compact; as a subspace of ℝ^P it is second countable. By ContinuousMap.instSecondCountableTopology (import Mathlib.Topology.ContinuousMap.SecondCountableSpace), every C(K, F_i) is second countable. Therefore the countable product X := Π_{i∈ℕ} C(K, F_i) is second countable, hence separable and first countable. Each C(K, F_i) is metrizable because K is compact, so the countable product X is pseudo-metrizable (these instances are found automatically).
3. (Jet map.) Let ω ∈ D^k(U). Since ω is C^∞ and i ≤ ∞, the map x ↦ iteratedFDeriv ℝ i ω x is continuous on ℝ^P (ContDiff.continuous_iteratedFDeriv), so its restriction to K is an element ι(ω)_i ∈ C(K, F_i). Define ι : D^k(U) → X by ι(ω) := (ι(ω)_i)_{i∈ℕ}. Thus ι(ω)_i(x) = iteratedFDeriv ℝ i ω x for x ∈ K.
4. (Countable dense subfamily.) Let D_K := {ω ∈ D^k(U) : tsupport ω ⊆ K} and A := ι(D_K) ⊆ X. X is separable, so A lies in the closure of a countable subset of X (TopologicalSpace.IsSeparable.of_separableSpace). X is pseudo-metrizable, so there is a countable T ⊆ A with A ⊆ closure T (TopologicalSpace.IsSeparable.exists_countable_dense_subset, which needs [PseudoMetrizableSpace X]). Every t ∈ T lies in ι(D_K), so we may choose g(t) ∈ D_K with ι(g(t)) = t. Let E := g(T) ⊆ D^k(U). E is countable, being the image of the countable set T.
5. (Approximating sequence.) Let ω ∈ D^k(U) with tsupport ω ⊆ K. Then ω ∈ D_K, so ι(ω) ∈ A ⊆ closure T. X is first countable, so there is a sequence (t_l)_{l∈ℕ} in T with t_l → ι(ω) in X (mem_closure_iff_seq_limit). Put e_l := g(t_l). Then e_l ∈ E for every l. Moreover tsupport e_l ⊆ K, because g(t_l) ∈ D_K, and ι(e_l) = t_l.
6. (Uniform convergence of every derivative on K.) Fix i ∈ ℕ. The projection of X onto the factor C(K, F_i) is continuous, so ι(e_l)_i = t_l(i) → ι(ω)_i in C(K, F_i). K is compact, so convergence in the compact-open topology of C(K, F_i) is the same as uniform convergence on K (ContinuousMap.tendsto_iff_tendstoUniformly). [Lean: pass its arguments α := K, β := F_i, F := (l ↦ t_l(i)), f := ι(ω)_i and p := atTop explicitly, because unification through the topology instance of F_i fails otherwise.] For x ∈ K we have ι(e_l)_i(x) = iteratedFDeriv ℝ i e_l x and ι(ω)_i(x) = iteratedFDeriv ℝ i ω x. Hence iteratedFDeriv ℝ i e_l → iteratedFDeriv ℝ i ω uniformly on K, that is, TendstoUniformlyOn (fun l x => iteratedFDeriv ℝ i e_l x) (fun x => iteratedFDeriv ℝ i ω x) atTop K (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).
7. (Conclusion.) Take K' := K in the definition of TestFormOnConverges. K' is compact and K' ⊆ U by hypothesis. tsupport e_l ⊆ K' for every l by Step 5, and tsupport ω ⊆ K' by assumption. Step 6 gives the uniform convergence on K' of the i-th derivatives for every i ∈ ℕ. Hence TestFormOnConverges e ω holds, and e_l ∈ E for all l. Since ω was an arbitrary element of D^k(U) with tsupport ω ⊆ K, the countable set E has the required property. ∎

## Key steps

1. Covector (Eucl P) k and the jet spaces F_i = Eucl P [×i]→L[ℝ] Covector (Eucl P) k are finite-dimensional (injective linear maps into finite-dimensional multilinear-map spaces), hence proper and second countable.
2. X := Π_{i∈ℕ} C(K, F_i) is second countable (ContinuousMap.instSecondCountableTopology; K is compact, Hausdorff and second countable) and pseudo-metrizable.
3. The jet map ι(ω) := (iteratedFDeriv ℝ i ω restricted to K)_i sends D_K = {ω : tsupport ω ⊆ K} into X. Choose a countable T ⊆ ι(D_K) dense in ι(D_K), and let E be a set of chosen preimages of T.
4. For ω supported in K, first countability gives t_l ∈ T with t_l → ι(ω). The preimages e_l lie in E and are supported in K.
5. Coordinatewise convergence in C(K, F_i), with K compact, is uniform convergence of iteratedFDeriv ℝ i e_l to iteratedFDeriv ℝ i ω on K. Hence TestFormOnConverges e ω with K' := K.

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
