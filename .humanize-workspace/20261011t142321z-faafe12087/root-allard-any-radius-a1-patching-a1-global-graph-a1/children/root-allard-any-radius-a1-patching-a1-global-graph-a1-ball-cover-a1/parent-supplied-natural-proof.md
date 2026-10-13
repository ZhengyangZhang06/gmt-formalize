# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.patching-a1.global_graph-a1`
- Child DAG node: `root.allard_any_radius-a1.patching-a1.global_graph-a1.ball_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is step 6 of the parent proof, with the conclusion of its step 5 as hypothesis (c), stated for a general closed set D and centre c. Notation: B°_r(x) is the open ball (Metric.ball). Let D, c and R satisfy the hypotheses, and put U := D ∩ B°_R(c).
1. U is open. Let w ∈ U. By (c), choose ε > 0 with B°_ε(w) ∩ B°_R(c) ⊆ D, and put N := B°_ε(w) ∩ B°_R(c).
- B°_ε(w) is a neighbourhood of w, because ε > 0 (ball_mem_nhds).
- B°_R(c) is open (isOpen_ball) and contains w, because w ∈ U. So it is a neighbourhood of w (IsOpen.mem_nhds).
- Hence N is a neighbourhood of w (Filter.inter_mem).
Every x ∈ N lies in D by the choice of ε, and in B°_R(c) because x ∈ N. So N ⊆ U, and U is a neighbourhood of w (Filter.mem_of_superset). As w ∈ U was arbitrary, U is open (isOpen_iff_mem_nhds).
2. B°_R(c) is convex (convex_ball), hence preconnected (Convex.isPreconnected).
3. Since R > 0, c ∈ B°_R(c) (mem_ball_self), and c ∈ D by (b). So c ∈ B°_R(c) ∩ U, and this intersection is nonempty.
4. Since U ⊆ D, closure(U) ⊆ closure(D) (closure_mono). Since D is closed, closure(D) = D (IsClosed.closure_eq). Hence closure(U) ∩ B°_R(c) ⊆ D ∩ B°_R(c) = U.
5. Apply IsPreconnected.subset_of_closure_inter_subset to the set s := B°_R(c), which is preconnected by step 2, and to the set U, which is open by step 1. Its other two hypotheses are that s ∩ U is nonempty (step 3) and that closure(U) ∩ s ⊆ U (step 4). It gives B°_R(c) ⊆ U, and U ⊆ D, so B°_R(c) ⊆ D.

## Key steps

1. U := D ∩ B°_R(c) is open: each w ∈ U has the neighbourhood B°_ε(w) ∩ B°_R(c) ⊆ U (isOpen_iff_mem_nhds)
2. B°_R(c) is convex, hence preconnected
3. c ∈ B°_R(c) ∩ U because R > 0 and c ∈ D
4. closure(U) ∩ B°_R(c) ⊆ D ∩ B°_R(c) = U because D is closed
5. IsPreconnected.subset_of_closure_inter_subset gives B°_R(c) ⊆ U ⊆ D

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; diff -q GMT/Ch05/{Contract,Submission}.lean <snapshot>/project/GMT/Ch05/{Contract,Submission}.lean`
- `grep -n '^open|^namespace|^end|^theorem|^def|^abbrev|^noncomputable def|^variable' GMT/Ch05/Submission.lean; sed -n 1,140p <snapshot>/project/GMT/Ch05/Contract.lean (Amb, Rn, graphPoint, graphOver, horizontalPlane, rotatedPlane)`
- `grep -n 'finAddEquivProd' -r Mathlib; sed -n 360,384p Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -n 'theorem IsPreconnected.subset_of_closure_inter_subset' -A6 Mathlib/Topology/Connected/Basic.lean`
- `grep -rn 'theorem Convex.isPreconnected|theorem convex_ball|theorem ContDiffAt.congr_of_eventuallyEq|theorem Filter.EventuallyEq.fderiv_eq|theorem ContDiffOn.contDiffAt|theorem ContDiffAt.contDiffWithinAt' Mathlib`
- `grep -n 'theorem isOpen_iff_mem_nhds|theorem IsCompact.of_isClosed_subset|theorem isCompact_closedBall|theorem IsCompact.isClosed|theorem IsCompact.image ' -r Mathlib`
- `python3 -I scans of dag.json: this node's status, children and depends_on; cross-branch dependencies; all 353 lean_names for arp_ball_subset_of_closed_rel_open and arp_contDiffOn_of_local_C1_reps; statements mentioning IsPreconnected, subset_of_closure, relOpen or ContDiffOn patching`
- `python3 -I substring scan of every nodes/*/* file for the two proposed names`
- `git grep -l -E 'arp_ball_subset_of_closed_rel_open|arp_contDiffOn_of_local_C1_reps' <obj> -- '*.lean', run once for each of 528 unique ref objects; positive control 'arp_global_graph_of_local_graphs' found in 8d6e98fe`
- `python3 -I comparison of the parent node's decomposition-v4/v5.json (global_graph child unchanged, proof sha256 d7d799483ee6eb3a) and of its v1 rationale and audits`
- `sed -n 455,645p GMT/Ch05/Submission.lean in the parent's speculative worktree .swarm-worktrees/004ef1d823edbbabfbcc (how arp_global_graph_of_local_graphs is used)`
- `cat swarm-project.json; python3 -I read of max_nodes in .humanize/swarm-configs/*.json`
- `grep -n '5\.3|Remark' book/sources/chapter-05-source.txt; sed -n 1030,1060p`
- `lake build GMT.Ch05.Submission (scratch /tmp/gg-split-emWFGJ/proj, .lake/packages symlinked to lake-packages-25730c7c); lake env lean Checks/{Children,Parent,SkeletonAx,Axioms,Inst}.lean`
- `python3 -I /tmp/gg-split-emWFGJ/scripts/gen.py (the verifier's own gmt-compare.py child_modules and lean_contract.validate_lean_statement); lake env lean Checks/Challenge_{parent,sibling,ball_cover,local_c1}.lean and Checks/Solution_{parent,ball_cover,local_c1}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convex/PathConnected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Convex.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/004ef1d823edbbabfbcc/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/gg-split-emWFGJ/proj/Checks/Children.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Parent.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/SkeletonAx.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Axioms.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Inst.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Challenge_parent.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Solution_parent.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Challenge_sibling.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Challenge_ball_cover.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Solution_ball_cover.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Challenge_local_c1.lean`
- `/tmp/gg-split-emWFGJ/proj/Checks/Solution_local_c1.lean`
- `/tmp/gg-split-emWFGJ/scripts/gen.py`
- `/tmp/gg-split-emWFGJ/scripts/children.json`

SNAPSHOT AND TARGET
- The manifest pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.
- The frozen type in dag.json equals the selected type byte for byte.
- The handoff proof has sha256 prefix d7d799483ee6eb3a, the same as the global_graph child in the parent's decomposition-v4/v5.
- The node's status is decomposing, with no children.

CITED LIBRARY RESULTS (all present in the snapshot)
- IsPreconnected.subset_of_closure_inter_subset: Topology/Connected/Basic.lean:434
- Convex.isPreconnected: Analysis/Convex/PathConnected.lean:93
- convex_ball: Analysis/Normed/Module/Convex.lean:62
- isOpen_iff_mem_nhds: Topology/Neighborhoods.lean:263
- ContDiffAt.contDiffWithinAt :946, ContDiffOn.contDiffAt :962 and ContDiffAt.congr_of_eventuallyEq :966, all in Analysis/Calculus/ContDiff/Defs.lean
- Filter.EventuallyEq.fderiv_eq: Analysis/Calculus/FDeriv/Congr.lean:260
- IsCompact.of_isClosed_subset :105 and IsCompact.image :124, both in Topology/Compactness/Compact.lean
- IsCompact.isClosed: Topology/Separation/Hausdorff.lean:600
- EuclideanSpace.finAddEquivProd: PiL2.lean:378. It is a ContinuousLinearEquiv, as the sibling's type assumes.

LEAN CHECKS (scratch project /tmp/gg-split-emWFGJ/proj)
- Both child types pass validate_lean_statement.
- The NodeChallenge modules generated by the verifier's own child_modules elaborate in the contract scope at main_theorem with only the sorry warning. That scope is: open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold.
- Both exact child types have complete proofs without sorry. Their axioms are propext, Classical.choice and Quot.sound.
- The selected theorem's byte-identical frozen type is proved from the two children and the sibling arp_rotatedPlane_graphPoint_coords, whose frozen type was taken from dag.json.
- The NodeSolution modules ('exact Submission.X') compile for the parent and both children.
- With the children and the sibling as axioms, #print axioms for the parent lists exactly propext, Classical.choice, Quot.sound and those three declarations. So every child is used and nothing else is missing.
- Instances: the norm of fderiv is ContinuousLinearMap.hasOpNorm, which rfl reduces to the sInf formula. ball is Metric.ball, and the order 1 is WithTop.one. No Matrix or IsUnit construction occurs.

NAMES AND REUSE
- Neither proposed name occurs among the 353 DAG lean_names, in any nodes/*/* file, in GMT/ or the snapshot project, or in any .lean file of the 528 unique git ref objects. The positive control found arp_global_graph_of_local_graphs in commit 8d6e98fe.
- No DAG declaration has a type identical to either child, so nothing is reused.

RUN STATE
- max_nodes is 1000 (swarm-project.json and the current swarm-configs) and the DAG has 353 nodes, so two new leaves at depth 4 <= 6 can be activated.

SOURCES
- The book's Remark 5.3 (chapter-05-source.txt, p. 122) prints no proof of this patching step. The child proofs are therefore extracted from steps 5-6 and 11 of the supplied proof.
- No network sources were needed.
