# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.retraction-a1.cube_core-a1`
- Child DAG node: `root.deformation-a1.retraction-a1.cube_core-a1.skeleton_facts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Lemma 5.4, printed proof p. 161, displays (1) and (2) (the segment from a to a_F lies in L_{k−1}(a), and L_{k−1}(a) is a union of translates of p_ℓ^{-1}(p_ℓ(a))), as facts 1(a), 1(b), 1(d), (d1), (d2) of the parent proof. Only 1/4 < a_i < 3/4 is used about a.

Notation: m, ℓ ∈ ℕ, d := m + 1 + ℓ, indices i range over Fin d, ℝ^d = Eucl d with the Euclidean norm |·|, C := [0,1]^d (y ∈ C iff 0 ≤ y_i ≤ 1 for all i), a ∈ ℝ^d with 1/4 < a_i < 3/4 for all i, and La := {y ∈ ℝ^d : there is a set J of indices with |J| = m + 2 and integers k_i with y_i − a_i = k_i for all i ∈ J}. 

1. (Integers in (−1, 1).) If k ∈ ℤ and −1 < k < 1 as real numbers, then k = 0.
2. (La is closed; fact 1(b).) For an index i let E_i := {y : y_i − a_i ∈ ℤ}, the preimage of the set ℤ ⊂ ℝ (the range of the cast ℤ → ℝ, which is closed in ℝ because the cast is an isometric closed embedding) under the continuous map y ↦ y_i − a_i; so E_i is closed. Directly from the definition, La = ⋃_{J : |J| = m+2} ⋂_{i ∈ J} E_i. Each ⋂_{i∈J} E_i is an intersection of closed sets, hence closed, and the union runs over the finitely many subsets J of the finite index set. A finite union of closed sets is closed, so La is closed.
3. (Face centres lie in La; printed (1), fact (d1).) Let |J| ≥ m + 2 and c_i = a_i for i ∈ J. Choose J′ ⊆ J with |J′| = m + 2. For i ∈ J′, c_i − a_i = 0, which is the integer 0. Hence J′ witnesses c ∈ La.
4. (Cone property; printed (2), fact (d2).) Let J, c, x, y, s be as in (3) and suppose y ∈ La, witnessed by J′ with |J′| = m + 2 and integers k_i with y_i − a_i = k_i for i ∈ J′. We show x_i − a_i = 0 for every i ∈ J′; then J′ (with all integers equal to 0) witnesses x ∈ La.
 (a) No i ∈ J′ lies outside J. Indeed, if i ∉ J then x_i = c_i, so y_i − c_i = s·(x_i − c_i) = 0 and y_i = c_i ∈ {0,1}. If c_i = 0 then k_i = −a_i ∈ (−3/4, −1/4), so −1 < k_i < 0, impossible for an integer; if c_i = 1 then k_i = 1 − a_i ∈ (1/4, 3/4), so 0 < k_i < 1, impossible.
 (b) Let i ∈ J′; by (a), i ∈ J and c_i = a_i. Since 0 ≤ y_i ≤ 1 and 1/4 < a_i < 3/4, k_i = y_i − a_i lies in (−3/4, 3/4) ⊂ (−1, 1), so k_i = 0 by step 1, i.e. y_i = a_i. Then s·(x_i − a_i) = s·(x_i − c_i) = y_i − c_i = a_i − a_i = 0, and s > 0 gives x_i − a_i = 0.
5. Steps 2, 3 and 4 prove (1), (2) and (3). ∎

Formalization notes (non-binding): rewrite La as `⋃ J ∈ {J | J.card = m + 2}, ⋂ i ∈ J, (fun y => y i - a i) ⁻¹' Set.range ((↑) : ℤ → ℝ)` and use `Set.Finite.isClosed_biUnion (Set.toFinite _)`, `isClosed_biInter`, `Real.isClosed_range_intCast.preimage (by fun_prop)`; `Finset.exists_subset_card_eq` for step 3; step 1 by `exact_mod_cast` and `omega`.

## Key steps

1. An integer strictly between −1 and 1 is 0.
2. La is a finite union over |J| = m+2 of finite intersections of preimages of the closed set ℤ, hence closed.
3. A point agreeing with a on m+2 coordinates lies in La (face centres, printed (1)).
4. Cone property: a witness index of y ∈ La outside J would give an integer in (−3/4,−1/4) ∪ (1/4,3/4); inside J it forces y_i = a_i, hence x_i = a_i (s > 0).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp workspace GMT/Ch06/Contract.lean = Submission.lean = snapshot project/GMT/Ch06/Contract.lean (identical)`
- `python3 -I: handoff lean_statement == dag.json node root.deformation-a1.retraction-a1.cube_core-a1 lean_statement (True); verifier gmt-compare.py contract_scope replay = [open MeasureTheory Filter Set Metric, open scoped ENNReal NNReal Topology, namespace GMT.Ch06, open Poincare.SimonGMT.Chapter06, open …Chapter03 (…), open …Chapter01 (…), noncomputable section, end]`
- `rg -n -i 'radial|retract|skeleton|gauge' project/GMT (only Ch04 normalRadialSq; no cubical/radial retraction, gauge or dual-skeleton lemma)`
- `rg -l -i 'radialRetraction|cubeRetraction|dualSkeleton|lip_at|LipschitzAt' .lake/packages/simongmt/Poincare (no match); grep -rn dr_cc_ GMT .lake/packages/simongmt/Poincare (no match)`
- `rg -n 'lemma isClosed_range_intCast' mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean (486, namespace Real)`
- `rg -n 'notMem_iff_infDist_pos|theorem infDist_le_dist_of_mem|lemma le_infDist|theorem infDist_empty' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean (584, 500, 508, 476)`
- `rg -n 'theorem dist_apply_le|theorem norm_apply_le|theorem sub_apply|theorem smul_apply|CoeFun' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean (652, 713, 122, 126, 92); rg -n 'structure WithLp' mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean (49: toLp/ofLp)`
- `rg -n 'theorem EuclideanSpace.dist_eq' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (158)`
- `rg -n 'theorem sup.._le_iff|theorem le_sup..|theorem exists_mem_eq_sup..' mathlib/Mathlib/Data/Finset/Lattice/Fold.lean (557, 563, 763); rg -n 'theorem abs_max_sub_max_le_max' mathlib/Mathlib/Algebra/Order/Group/MinMax.lean (83)`
- `rg -n 'exists_subset_card_eq|card_insert_of_notMem|card_erase_of_mem|card_sdiff_of_subset' mathlib/Mathlib/Data/Finset/Card.lean (677, 103, 151, 597); rg -n card_univ_sdiff mathlib/Mathlib/Data/Fintype/Card.lean (130)`
- `rg -n 'theorem Finite.exists_min' mathlib/Mathlib/Data/Fintype/Lattice.lean (56); rg -n 'theorem isOpen_iff' mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean (833); rg -n 'theorem isClosed_const|theorem isClosed_biInter|theorem Set.Finite.isClosed_biUnion' mathlib/Mathlib/Topology/Basic.lean (134, 162, 185)`
- `rg -n 'theorem iterate_succ_apply|theorem iterate_fixed' mathlib/Mathlib/Logic/Function/Iterate.lean (65, 91, 174); rg -n 'theorem update_of_ne' mathlib/Mathlib/Logic/Function/Basic.lean (652); rg -n 'lemma le_induction' mathlib/Mathlib/Data/Nat/Init.lean (233); rg -n 'lemma le_div_iff₀|lemma div_le_div_iff₀' mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean (1128, 1423)`
- `sed -n '1440,1690p' book/chapter-06.txt (printed Lemma 5.4 and proof, pp. 160–163: ψ_F, (1)–(8), translation property, claim (3))`
- `python3 -I over dag.json (457 nodes): the seven dr_cc_* names vs all lean_name reservations (no collision); no reusable identical statement`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the seven statements (all valid); lake env lean /tmp/cubecore-a1-scratch/stmts/NC_<key>.lean for each (exit 0, only the sorry warning)`
- `lake env lean /tmp/cubecore-a1-scratch/AllProofs.lean (full proofs of the seven children and of Submission.deformation_retraction_cube_core from them; #print axioms = [propext, Classical.choice, Quot.sound] for all)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fintype/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fintype/Lattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Logic/Function/Iterate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Logic/Function/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Nat/Init.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1-cube-core-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cubecore-a1-scratch/stmts/statements.json`
- `/tmp/cubecore-a1-scratch/AllProofs.lean`

Pinned revisions confirmed; the frozen Contract (= Submission) is byte-identical to the snapshot, and the selected frozen type equals the DAG entry. Neither the project nor SimonGMT has a cubical/radial retraction, a gauge, a dual-skeleton lemma, or a pointwise-Lipschitz calculus, so the children are built from pinned Mathlib primitives: Real.isClosed_range_intCast, Set.Finite.isClosed_biUnion and isClosed_biInter (closedness of La); IsClosed.notMem_iff_infDist_pos, Metric.le_infDist and Metric.infDist_le_dist_of_mem (distances); PiLp.dist_apply_le, PiLp.norm_apply_le, EuclideanSpace.dist_eq and WithLp.toLp/ofLp (coordinates); Finset.sup', le_sup', exists_mem_eq_sup', sup'_le and abs_max_sub_max_le_max (the gauge); Finset.exists_subset_card_eq, card_univ_sdiff, card_erase_of_mem and card_insert_of_notMem (counting); Function.iterate_succ_apply/iterate_succ_apply'/iterate_fixed (ψ₀ = R^ℓ); Finite.exists_min and Metric.isOpen_iff (union rule); Nat.le_induction (face-dimension induction). All seven child types validate and elaborate in the exact comparator challenge scope. All seven were fully proved in scratch, and the parent type was kernel-checked from construction + pointwise_lip, with axioms [propext, Classical.choice, Quot.sound]. No name collision exists, and no existing DAG node has a reusable identical statement.
