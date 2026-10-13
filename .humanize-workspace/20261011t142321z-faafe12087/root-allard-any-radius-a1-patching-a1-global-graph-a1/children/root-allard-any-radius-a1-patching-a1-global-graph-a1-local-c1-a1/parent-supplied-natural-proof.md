# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.patching-a1.global_graph-a1`
- Child DAG node: `root.allard_any_radius-a1.patching-a1.global_graph-a1.local_c1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the last paragraph of step 11 of the parent proof, stated for a general open set Ω and general local representatives. Notation: B°_r(x) is the open ball (Metric.ball); 'C^1 on a set' means ContDiffOn ℝ 1; the norm of a derivative is the operator norm. Let u, Ω and L satisfy the hypotheses.
1. Fix x0 ∈ Ω. By hypothesis, choose ε > 0 and f : R^m → R^k such that f is C^1 on B°_ε(x0), |fderiv f x0| ≤ L, and u(w) = f(w) for all w ∈ B°_ε(x0) ∩ Ω.
2. u = f near x0.
- B°_ε(x0) is a neighbourhood of x0, because ε > 0 (ball_mem_nhds).
- Ω is a neighbourhood of x0, because Ω is open and x0 ∈ Ω (IsOpen.mem_nhds).
- So V := B°_ε(x0) ∩ Ω is a neighbourhood of x0 (Filter.inter_mem).
Since u(w) = f(w) for every w ∈ V, u and f are eventually equal at x0, i.e. u =ᶠ[𝓝 x0] f (Filter.eventually_of_mem).
3. f is C^1 at x0. f is C^1 on B°_ε(x0), which is a neighbourhood of x0 by step 2. Hence ContDiffAt ℝ 1 f x0 (ContDiffOn.contDiffAt).
4. u is C^1 at x0. Step 3 and the eventual equality of step 2 give ContDiffAt ℝ 1 u x0 (ContDiffAt.congr_of_eventuallyEq). In particular ContDiffWithinAt ℝ 1 u Ω x0 (ContDiffAt.contDiffWithinAt).
5. Slope at x0. By step 2, fderiv ℝ u x0 = fderiv ℝ f x0 (Filter.EventuallyEq.fderiv_eq). Hence |fderiv u x0| = |fderiv f x0| ≤ L.
6. Conclusion. Since x0 ∈ Ω was arbitrary, step 4 holds at every point of Ω, which is the definition of ContDiffOn ℝ 1 u Ω. Step 5 gives |fderiv u x| ≤ L for every x ∈ Ω.

## Key steps

1. At x0 ∈ Ω take ε and f; since B°_ε(x0) ∩ Ω is a neighbourhood of x0, u =ᶠ[𝓝 x0] f
2. f is C^1 on a neighbourhood of x0, so ContDiffAt ℝ 1 f x0
3. ContDiffAt.congr_of_eventuallyEq gives ContDiffAt ℝ 1 u x0, hence ContDiffWithinAt ℝ 1 u Ω x0
4. Filter.EventuallyEq.fderiv_eq gives fderiv u x0 = fderiv f x0, so |fderiv u x0| ≤ L
5. x0 was arbitrary, so ContDiffOn ℝ 1 u Ω and the bound holds on Ω

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
