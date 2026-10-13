# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.patching-a1.regraph-a1`
- Child DAG node: `root.allard_any_radius-a1.patching-a1.regraph-a1.inverse_c1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: for x in U write DPhi(x) := fderiv Phi x, a continuous linear endomorphism of R^n; norms of linear maps are operator norms. End := (R^n ->L[R] R^n), the continuous linear endomorphisms of R^n, is a complete normed ring (R^n is finite-dimensional, hence complete). Hypotheses: U and W are open; kappa > 0; (H1) Phi is C^1 on U; (H2) kappa|h| <= |DPhi(x) h| for all x in U and h in R^n; (H3) X is continuous on W; (H4) X(w) is in U and Phi(X(w)) = w for every w in W.
Provenance: this is the abstract form of steps 8, 10 and 11 of the parent regraph proof (invertibility of the chart derivative, the local-left-inverse rule, continuity of the inverse derivative); every step is proved in full here and nothing from the parent is assumed.
1. Each DPhi(x), x in U, is invertible with |DPhi(x)^{-1}| <= 1/kappa. Fix x in U and let L := DPhi(x). If L a = L b, then (H2) gives kappa|a - b| <= |L(a - b)| = 0, and kappa > 0 gives a = b. So L is an injective linear endomorphism of the finite-dimensional space R^n, hence bijective (LinearEquiv.ofInjectiveEndo, Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:412). Linear maps between finite-dimensional normed spaces are continuous, so L is the forward map of a continuous linear equivalence L~ of R^n (LinearEquiv.toContinuousLinearEquiv). For k in R^n, (H2) at h = L~^{-1} k gives kappa|L~^{-1} k| <= |L(L~^{-1} k)| = |k|, so |L~^{-1} k| <= kappa^{-1}|k|; by ContinuousLinearMap.opNorm_le_bound (with 0 <= kappa^{-1}), |L~^{-1}| <= kappa^{-1}.
2. Regularity of Phi on U. Let x be in U. The open set U is a neighbourhood of x, and Phi is C^1 on U with 1 != 0, so Phi is differentiable at x: Phi has derivative DPhi(x) at x. Moreover x -> DPhi(x) is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen, Mathlib/Analysis/Calculus/ContDiff/Defs.lean:916, using 1 <= 1).
3. Derivative of X and the bound. Fix w in W, put x0 := X(w), which lies in U by (H4), and let L~ be the equivalence of step 1 at x0. Three facts hold:
- X is continuous at w, because X is continuous on W (H3) and the open set W is a neighbourhood of w;
- Phi has derivative L~ = DPhi(x0) at X(w) (step 2);
- Phi(X(w')) = w' for all w' in the neighbourhood W of w (H4).
By the local-left-inverse rule (HasFDerivAt.of_local_left_inverse, Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean:165), X has derivative L~^{-1} at w. Consequently X is differentiable at every point of W, fderiv X w = L~^{-1}, and |fderiv X w| <= kappa^{-1} by step 1. This is the second conclusion.
4. The derivative of X through the ring inverse. With w, x0 and L~ as in step 3, DPhi(x0) is the underlying element of the unit u := L~.toUnit of End (ContinuousLinearEquiv.toUnit), and the inverse of u is L~^{-1}. Hence Ring.inverse(DPhi(X(w))) = (u^{-1} : End) = L~^{-1} = fderiv X w (Ring.inverse_unit). So fderiv X w = Ring.inverse(DPhi(X(w))) for every w in W.
5. Continuity of fderiv X on W. Fix w in W and put x0 := X(w), which is in U.
- w' -> DPhi(X(w')) is continuous at w: X is continuous at w (step 3), and DPhi is continuous at x0 since it is continuous on the open set U containing x0 (step 2).
- Ring.inverse is continuous at every unit of the complete normed ring End (NormedRing.inverse_continuousAt, Mathlib/Analysis/Normed/Ring/Units.lean:183), in particular at DPhi(x0), which is the unit L~.toUnit of step 4.
- Hence w' -> Ring.inverse(DPhi(X(w'))) is continuous at w. By step 4 it agrees with fderiv X on the neighbourhood W of w, so fderiv X is continuous at w.
Thus fderiv X is continuous on W. [Alternative estimate: if P := DPhi(X(w')) and Q := DPhi(X(w)) with inverses P~^{-1}, Q~^{-1} from step 1, then P~^{-1} - Q~^{-1} = P~^{-1}(Q - P)Q~^{-1}, so |P~^{-1} - Q~^{-1}| <= kappa^{-2}|P - Q|, which tends to 0 as w' -> w by the first bullet.]
6. X is C^1 on W. W is open, X is differentiable on W (step 3) and fderiv X is continuous on W (step 5). By contDiffOn_succ_iff_fderiv_of_isOpen (Mathlib/Analysis/Calculus/ContDiff/Defs.lean:891) applied with 1 = 0 + 1 (its middle condition, 0 = top in WithTop ENat (i.e. order omega) -> AnalyticOn, is vacuous because 0 != top), together with contDiffOn_zero (C^0 on W is continuity on W), X is C^1 on W. [Equivalently, at each w in W use contDiffAt_succ_iff_hasFDerivAt (Defs.lean:1018) with n = 0 and contDiffAt_zero (Defs.lean:1129), whose neighbourhood is W.] This is the first conclusion.

## Key steps

1. For x in U, DPhi(x) is injective by the lower bound, hence (finite dimension) a continuous linear equivalence with |DPhi(x)^{-1}| <= 1/kappa
2. Phi is differentiable on the open set U and fderiv Phi is continuous on U
3. Local-left-inverse rule (HasFDerivAt.of_local_left_inverse): X has derivative DPhi(X w)^{-1} at each w in W, so |fderiv X w| <= 1/kappa
4. fderiv X w = Ring.inverse(DPhi(X w)); continuity of X, of fderiv Phi and of Ring.inverse at units gives continuity of fderiv X on W
5. Differentiable with continuous derivative on the open set W implies C^1 on W (contDiffOn_succ_iff_fderiv_of_isOpen, contDiffOn_zero)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/{GMT/Ch05/Contract.lean,GMT/Ch05/Submission.lean,lakefile.toml,lean-toolchain,lake-manifest.json} against the workspace copies`
- `rg -n 'theorem surjOn_closedBall_of_nonlinearRightInverse|theorem of_local_left_inverse|theorem inverse_continuousAt|theorem contDiffAt_succ_iff_hasFDerivAt|theorem contDiffAt_zero|continuousOn_fderiv_of_isOpen|theorem contDiffAt_symm|def toOpenPartialHomeomorph|def ofInjectiveEndo|theorem contDiffOn_succ_iff_fderiv_of_isOpen|theorem norm_image_sub_le_of_norm_fderivWithin_le|structure NonlinearRightInverse' <snapshot>/mathlib/Mathlib`
- `rg -n 'contDiffAt_symm|of_local_left_inverse|norm_fderiv_le_of_lipschitz' <snapshot>/mathlib/Mathlib`
- `rg -n 'ring_inverse_equiv|theorem inverse_equiv|def unitsEquiv|def toUnit|theorem inverse_unit|theorem contDiffOn_zero|abbrev EuclideanSpace.finAddEquivProd|theorem append_left|theorem append_right' <snapshot>/mathlib/Mathlib`
- `sed -n 360,400p PiL2.lean; sed -n 30,60p Normed/Operator/Banach.lean; sed -n 130,175p InverseFunctionTheorem/ApproximatesLinearOn.lean; sed -n 155,200p FDeriv/OfCompLeft.lean; sed -n 1,90p ContinuousLinearMap/Invertible.lean`
- `python3 -I scans of dag.json (lean_names, duplicates, statuses, statements mentioning fderiv/ContDiffOn/ApproximatesLinearOn/inverse) and of nodes/*/*.json for arp_rgr_ball_right_inverse, arp_rgr_right_inverse_contDiffOn, arp_rgr_graph_map_fderiv`
- `git for-each-ref (563 refs) | xargs git grep -l -E 'arp_rgr_|rgr_ball_right_inverse|right_inverse_contDiffOn|graph_map_fderiv' -- '*.lean'; grep -rn the same names over GMT/ and <snapshot>/project`
- `grep -n 'depends_on|proof_base_commit|Do not add helper declarations' /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py and prompts.py`
- `lake build GMT.Ch05.Submission in scratch /tmp/regraph-split-Bu1nSC/proj (.lake/packages -> lake-packages-25730c7c)`
- `lake env lean Checks/Avail.lean (#check of all cited lemmas)`
- `lake env lean Checks/{Stmts,Skel,SkelAx,ChildA,ChildB,ChildC,Combined}.lean`
- `python3 -I scripts/gen_challenges.py (verifier lean_contract.validate_lean_statement and gmt-compare.child_modules in contract mode); lake env lean Checks/Challenge_{ball_right_inverse,inverse_c1,graph_map_fderiv,parent}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-regraph-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-regraph-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/prompts.py`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Avail.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Stmts.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Skel.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/SkelAx.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/ChildA.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/ChildB.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/ChildC.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Combined.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Challenge_ball_right_inverse.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Challenge_inverse_c1.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Challenge_graph_map_fderiv.lean`
- `/tmp/regraph-split-Bu1nSC/proj/Checks/Challenge_parent.lean`
- `/tmp/regraph-split-Bu1nSC/scripts/gen_challenges.py`
- `/tmp/regraph-split-Bu1nSC/draft/subproblems.json`

Snapshot and target
- The manifest pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- Contract.lean, Submission.lean and the Lake inputs are byte-identical to the workspace copies.

Library: every lemma the children cite is in the snapshot and in scope after `import GMT.Ch05.Submission`.
- ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse (ApproximatesLinearOn.lean:143), with ContinuousLinearMap.NonlinearRightInverse (Normed/Operator/Banach.lean:37)
- LinearEquiv.ofInjectiveEndo (FiniteDimensional/Basic.lean:412) and LinearMap.injective_iff_surjective
- HasFDerivAt.of_local_left_inverse (FDeriv/OfCompLeft.lean:165)
- NormedRing.inverse_continuousAt (Normed/Ring/Units.lean:183)
- ContinuousLinearEquiv.toUnit (Topology/Algebra/Module/Equiv/Basic.lean:610)
- Ring.inverse_unit (GroupWithZero/Units/Basic.lean:89)
- In ContDiff/Defs.lean: ContDiffOn.continuousOn_fderiv_of_isOpen (:916), contDiffOn_succ_iff_fderiv_of_isOpen (:891), contDiffOn_zero (:618), contDiffAt_succ_iff_hasFDerivAt (:1018), contDiffAt_zero (:1129)
- EuclideanSpace.finAddEquivProd (PiL2.lean:378)
- Fin.append_left and Fin.append_right (Data/Fin/Tuple/Basic.lean:312 and :323)
- Alternatives also in scope: OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881) and ApproximatesLinearOn.toOpenPartialHomeomorph.
- ContractingWith is not in scope, as the parent proof's Lean remark says.

Workflow constraints (flow runtime)
- A leaf child adds only its single theorem, with no helper declarations.
- A child's proof base overlays only its accepted depends_on siblings, so the children are self-contained and do not cite arp_rotatedPlane_graphPoint_coords.

Names and reuse
- arp_rgr_ball_right_inverse, arp_rgr_right_inverse_contDiffOn and arp_rgr_graph_map_fderiv occur in none of the DAG's 359 nodes (no duplicate names) and in no node file.
- They are also absent from GMT/, from the snapshot project, and from every .lean file on 563 git refs. Nothing is reused.

Lean checks
- All three child types and the parent type pass validate_lean_statement. They elaborate in the comparator's generated child scope (open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold), with only the expected sorry warning.
- Instances are as intended: ‖fderiv ℝ X w‖ is ContinuousLinearMap.hasOpNorm, ‖h‖ is the PiLp 2 norm, and ContDiffOn ℝ 1 uses (1 : WithTop ℕ∞). No Matrix or IsUnit construction occurs.
- The exact parent type compiles from stubs of the three children plus the sibling. #print axioms lists exactly those four besides propext, Classical.choice and Quot.sound.
- All three children have complete scratch proofs that use only the standard axioms.

No network sources were needed; the mathematics is the parent-supplied proof.
