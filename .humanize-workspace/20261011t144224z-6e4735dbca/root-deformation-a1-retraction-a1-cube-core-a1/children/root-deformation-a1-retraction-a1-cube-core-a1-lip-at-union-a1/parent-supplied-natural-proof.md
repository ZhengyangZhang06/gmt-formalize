# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.retraction-a1.cube_core-a1`
- Child DAG node: `root.deformation-a1.retraction-a1.cube_core-a1.lip_at_union-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: rule “6.1 Two rules (Union)” of the parent proof. It replaces the printed a.e. reasoning at the point y = ψ^{(n+ℓ)}(x), which may lie on several closed (n + ℓ − 1)-faces of C, n := m + 1 (Simon, Ch. 6, Lemma 5.4, printed p. 162: “let F be any closed (n+ℓ−1)-face of C which contains y”).

1. Fix ε > 0. For every k ∈ ι we choose r_k > 0 with the property (∗)_k: d(g(y′), g(y)) ≤ (K + ε)·d(y′, y) for all y′ ∈ G k ∩ B with d(y′, y) < r_k.
 (a) If y ∈ G k, the hypothesis applied to k and ε gives such an r_k.
 (b) If y ∉ G k, then y belongs to the open set X ∖ G k (G k is closed), so there is r_k > 0 with ball(y, r_k) ⊆ X ∖ G k. Then no y′ ∈ G k satisfies d(y′, y) < r_k, and (∗)_k holds vacuously.
2. Choose δ > 0 with δ ≤ r_k for every k: if ι is nonempty, the finite family k ↦ r_k attains a minimum at some k₀ (ι is finite), and δ := r_{k₀} > 0 works; if ι is empty, δ := 1 works vacuously.
3. Let y′ ∈ B with d(y′, y) < δ. Since B ⊆ ⋃_k G k, there is k with y′ ∈ G k; thus y′ ∈ G k ∩ B and d(y′, y) < δ ≤ r_k, and (∗)_k gives d(g(y′), g(y)) ≤ (K + ε)·d(y′, y). ∎

Formalization notes (non-binding): `Metric.isOpen_iff` applied to `(hG k).isOpen_compl` gives the ball in 1(b); `choose r hr hbound` over k; `Finite.exists_min r` (needs `Nonempty ι`) gives δ; `Set.mem_iUnion` for step 3.

## Key steps

1. For each piece G k pick a radius r_k: from the hypothesis if y ∈ G k, and a ball missing the closed set G k if y ∉ G k.
2. Take δ = min_k r_k > 0 (finite index type; δ = 1 if ι is empty).
3. Any y′ ∈ B within δ of y lies in some G k ∩ B with d(y′,y) < r_k, so the bound holds.

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
