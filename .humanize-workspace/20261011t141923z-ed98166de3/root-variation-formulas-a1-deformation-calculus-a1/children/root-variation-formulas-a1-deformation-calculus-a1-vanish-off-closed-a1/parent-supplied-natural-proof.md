# Parent-supplied natural-language proof

- Parent DAG node: `root.variation_formulas-a1.deformation_calculus-a1`
- Child DAG node: `root.variation_formulas-a1.deformation_calculus-a1.vanish_off_closed-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance: part (V) of the parent proof of variation_deformation_calculus. The hypotheses are reduced to what that argument uses: K is closed (in the parent K is compact, hence closed), and φ_t = id off K for |t| < 1. The proof below is self-contained.

Notation. For x ∈ ℝᴺ put g_x(s) := φ s x and h_x(t) := deriv g_x t. By definition X(x) = initialVelocity φ x = deriv g_x 0 and Z(x) = initialAcceleration φ x = deriv h_x 0. Here deriv and fderiv are Mathlib's derivatives, which depend only on the germ of the function at the point (Filter.EventuallyEq.deriv_eq, Filter.EventuallyEq.fderiv_eq).

1. Fix x ∉ K. For every s ∈ (−1,1) the hypothesis gives g_x(s) = φ s x = x.
2. Let t ∈ (−1,1). The open interval (−1,1) is a neighbourhood of t, so by 1, g_x coincides near t with the constant function s ↦ x. Hence deriv g_x t = deriv (s ↦ x) t = 0 (deriv_const).
3. Since 0 ∈ (−1,1), step 2 with t = 0 gives X(x) = deriv g_x 0 = 0.
4. By step 2, h_x(t) = deriv g_x t = 0 for every t ∈ (−1,1). Since (−1,1) is a neighbourhood of 0, h_x coincides near 0 with the constant function 0, so Z(x) = deriv h_x 0 = deriv (t ↦ 0) 0 = 0.
5. Steps 1–4 apply at every point of ℝᴺ ∖ K, so X(x′) = 0 and Z(x′) = 0 for all x′ ∉ K. K is closed, so ℝᴺ ∖ K is open. For x ∉ K it is therefore a neighbourhood of x on which X and Z are identically 0. So X and Z coincide near x with the constant map 0, and fderiv ℝ X x = fderiv ℝ (fun _ ↦ 0) x = 0 and fderiv ℝ Z x = 0 (fderiv_const_apply).
6. Steps 3, 4 and 5 give X(x) = 0, Z(x) = 0, DX(x) = 0 and DZ(x) = 0 for every x ∉ K.

## Key steps

1. For x ∉ K, s ↦ φ s x is constant (= x) on the open interval (−1,1), so deriv (s ↦ φ s x) t = 0 for every t ∈ (−1,1).
2. Taking t = 0 gives X(x) = 0. Since t ↦ deriv (s ↦ φ s x) t vanishes on a neighbourhood of 0, Z(x) = 0.
3. ℝᴺ ∖ K is open (K closed) and X, Z vanish on it. So X and Z are locally 0 at each x ∉ K, and fderiv ℝ X x = fderiv ℝ Z x = 0.

## Reference use

### local-project

Queries:
- `sed -n 1,270p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean (hasDerivAt_familySpatialDerivative, familySpatialDerivative_eq_fderiv, initialVelocity_eq_deriv, contDiffAt_initialVelocity)`
- `grep -rn 'abbrev Euclidean' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/*.lean`
- `grep -rn 'initialVelocity\|initialAcceleration\|IsAdmissibleDeformation' local-references/ff09f3909baeeae7/project/GMT --include=*.lean`
- `rg -n 'theorem ContDiffAt.isSymmSndFDerivAt|theorem IsSymmSndFDerivAt.eq|^def IsSymmSndFDerivAt|minSmoothness_of_isRCLikeNormedField' mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `grep -n 'theorem ContDiffOn.fderiv_of_isOpen\|theorem ContDiffOn.contDiffAt\|theorem ContDiffOn.congr\|theorem ContDiffAt.eventually\|theorem ContDiffAt.differentiableAt' mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `grep -n 'theorem ContDiffOn.clm_comp\|theorem ContDiffOn.clm_apply\|fderiv_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `grep -rn 'theorem hasFDerivAt_prodMk_right\|theorem HasFDerivAt.comp_hasDerivAt\|comp_hasDerivAt_of_eq\|theorem HasDerivAt.clm_comp\|theorem HasDerivAt.congr_of_eventuallyEq\|EventuallyEq.deriv_eq\|EventuallyEq.fderiv_eq\|theorem HasDerivAt.prodMk\|theorem fderiv_const_apply\|theorem deriv_const\|theorem fderiv_id' in mathlib/Mathlib/Analysis/Calculus/FDeriv/{Prod,Congr,Basic,Const}.lean and Deriv/{Comp,Mul,Basic,Prod}.lean`
- `python3 -I scripts/scope.py and scripts/gen_checks.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement) then lean NodeChallenge_00..03 against the frozen GMT.Ch02.Submission olean and NodeSolution_00..03 against a Submission containing the four proofs (built with lean -R root -o)`
- `lean checks/Stmts.lean, ChildV.lean, ChildP.lean, ChildM.lean, ChildM_noimport.lean, Assembly.lean (#print axioms)`
- `python3 -I scan of dag.json lean_name fields and nodes/*/*.json lean_name fields; git grep of all refs/heads and grep of simongmt/Poincare for the three proposed names`
- `git show <accepted candidate commits>:GMT/Ch02/Submission.lean | grep ^import (import-header practice); sed -n 300,384p verifier/gmt-compare.py (Submission.lean is not byte-checked)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-deformation-calculus-a1/parent-child-handoff.json`
- `/tmp/defcalc-decomp-6Hb6gC/checks/ChildV.lean`
- `/tmp/defcalc-decomp-6Hb6gC/checks/ChildP.lean`
- `/tmp/defcalc-decomp-6Hb6gC/checks/ChildM.lean`
- `/tmp/defcalc-decomp-6Hb6gC/checks/ChildM_noimport.lean`
- `/tmp/defcalc-decomp-6Hb6gC/checks/Assembly.lean`
- `/tmp/defcalc-decomp-6Hb6gC/rootP/GMT/Ch02/Submission.lean`
- `/tmp/defcalc-decomp-6Hb6gC/nodechecks/NodeChallenge_03_variation_deformation_calculus.lean`
- `/tmp/defcalc-decomp-6Hb6gC/nodechecks/NodeSolution_03_variation_deformation_calculus.lean`
- `/tmp/defcalc-decomp-6Hb6gC/scripts/gen_checks.py`
- `/tmp/defcalc-decomp-6Hb6gC/proposal/subproblems.json`

No lemma in the snapshot states the selected theorem or its children in the contract's fderiv/deriv form. The closest is SimonGMT Chapter08 hasDerivAt_familySpatialDerivative, which differs in three ways: it is stated only at t = 0; it uses an uncurried F with familySpatialDerivative = DF∘inr and its own initialVelocity F x = DF(0,x)(1,0), not the contract's deriv-based initialVelocity; and it needs an extra import. The children therefore state the interchange generally, at any (t,y), directly for fderiv ℝ (Φ s) y and deriv (s ↦ Φ s x) t. The pinned Mathlib supplies every ingredient: ContDiffAt.isSymmSndFDerivAt with minSmoothness_of_isRCLikeNormedField (FDeriv/Symmetric.lean, not reachable from the frozen header, so Submission.lean must add the import; gmt-compare.py does not byte-check Submission.lean), ContDiffOn.fderiv_of_isOpen, ContDiffOn.contDiffAt, ContDiffOn.congr, ContDiffAt.eventually, ContDiffAt.differentiableAt, ContDiffAt.fderiv_right, ContDiffOn.clm_comp/clm_apply, hasFDerivAt_prodMk_right, HasFDerivAt.comp_hasDerivAt(_of_eq), HasDerivAt.prodMk, HasDerivAt.clm_comp, HasDerivAt.congr_of_eventuallyEq, Filter.EventuallyEq.deriv_eq/fderiv_eq, fderiv_const_apply, deriv_const and fderiv_id. Lean results: the three children are proved in scratch, the parent is proved from them, and all comparator-style modules compile with propext, Classical.choice and Quot.sound only. The three names collide with nothing in dag.json, the decomposition proposals, any branch or SimonGMT.
