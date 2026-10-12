# Parent-supplied natural-language proof

- Parent DAG node: `root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1`
- Child DAG node: `root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1.first_order_at_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3(a), 3(b) and 4 of the supplied proof of variation_matrix_det_derivatives_at_one (Simon Ch. 2, p. 62: the first-order term tr A of det(I + A)).

Notation. Perm(ι) is the finite group of permutations of ι, id = 1 the identity permutation, and sgn(σ) ∈ {1, −1} the sign of σ, viewed as a real number. I is the identity matrix, so I_{ab} = δ_{ab}. For m ∈ ι, Π_{j≠m} denotes the product over the finite set ι∖{m} (Finset.univ.erase m).

1. Permutation fact. Let σ ≠ id and m ∈ ι. Then some j ≠ m has σ(j) ≠ j. Proof: if σ(y) = y for every y, then σ = id by extensionality (Equiv.ext). So there is a y with σ(y) ≠ y. If y ≠ m, take j := y. If y = m, take j := σ(m). Then j ≠ m because σ(m) ≠ m. Also σ(j) ≠ j, because σ(σ(m)) = σ(m) would give σ(m) = m by injectivity of σ.

2. Vanishing products. Let σ ≠ id and m ∈ ι, and let j be as in step 1. Then j ∈ ι∖{m}, and the factor I_{σ(j) j} is 0 because σ(j) ≠ j (Matrix.one_apply_ne). Hence Π_{j'∈ι∖{m}} I_{σ(j') j'} = 0 (Finset.prod_eq_zero). So for σ ≠ id every term of the inner sum is 0 · H_{σ(m) m} = 0. The σ-summand sgn(σ) · Σ_m (Π_{j≠m} I_{σ(j) j}) · H_{σ(m) m} therefore equals sgn(σ) · 0 = 0.

3. Reduction to σ = id. By step 2, every summand with σ ≠ id is 0. Since id ∈ Perm(ι) = Finset.univ, the whole sum equals its σ = id summand (Finset.sum_eq_single).

4. The identity term. For σ = id we have sgn(id) = 1. For every j, I_{id(j) j} = I_{jj} = 1 (Matrix.one_apply_eq), so each product Π_{j≠m} I_{jj} equals 1 (Finset.prod_eq_one). Also H_{id(m) m} = H_{mm}. Hence the σ = id summand is 1 · Σ_m 1 · H_{mm} = Σ_m H_{mm} = tr H, by the definition of Matrix.trace as the sum of the diagonal entries.

5. By steps 3 and 4 the sum equals tr H. If ι is empty, then Perm(ι) = {id}, the sum over m is empty and both sides are 0. Steps 1–4 cover this case verbatim.

## Key steps

1. A permutation σ ≠ id moves some j ≠ m: pick y with σ y ≠ y, and take j = y if y ≠ m, else j = σ m (then σ(σ m) ≠ σ m by injectivity).
2. Hence for σ ≠ id each product Π_{j≠m} I_{σ(j)j} has a zero factor, so the σ-summand is 0.
3. The sum reduces to σ = id (Finset.sum_eq_single), whose term is 1 · Σ_m 1 · H_{mm} = tr H.

## Reference use

### local-project

Queries:
- `python3 -I scope.py (gmt-compare.py contract_scope on GMT/Ch02/Contract.lean -> namespace GMT.Ch02, opens MeasureTheory Metric Set Filter Topology, ENNReal NNReal, Poincare.SimonGMT)`
- `rg -n "theorem det_apply|theorem det_apply'" mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `rg -n "finset_prod|finsetProd" mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `rg -n "theorem HasDerivAt.fun_sum|theorem HasDerivAt.sum|theorem HasDerivAt.const_mul|theorem HasDerivAt.mul |theorem HasDerivAt.congr_of_eventuallyEq|theorem Filter.EventuallyEq.deriv_eq" mathlib/Mathlib/Analysis/Calculus`
- `rg -n "theorem sign_swap" mathlib/Mathlib/GroupTheory/Perm/Sign.lean; rg -n "theorem swap_apply_of_ne_of_ne|theorem swap_apply_left|theorem swap_apply_right" mathlib/Mathlib/Logic/Equiv/*.lean; rg -n "theorem one_apply_ne|theorem one_apply_eq" mathlib/Mathlib/Data/Matrix/*.lean; rg -n "theorem prod_pair|theorem prod_subset" mathlib/Mathlib/Algebra/BigOperators/Group/Finset/*.lean; rg -n "def trace" mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean`
- `rg -n "theorem .*(hasDerivAt|HasDerivAt|hasFDerivAt|HasFDerivAt|deriv|fderiv).*[dD]et\b|theorem .*[dD]et.*(hasDerivAt|HasDerivAt|HasFDerivAt|hasFDerivAt|_deriv|_fderiv)" mathlib/Mathlib`
- `rg -n "det_one_add_X_smul|coeff_det_one_add_X_smul_one|det_one_add_smul" mathlib/Mathlib`
- `rg -n "coeff_det_one_add_X_smul_two|det_one_add_smul.*sq|trace_sq|trace_pow_two" mathlib/Mathlib`
- `rg -n "det_one_add|HasDerivAt.*\.det|deriv.*\.det\b|Equiv.Perm.sign" lake-packages-25730c7c/simongmt/Poincare`
- `rg -n "Matrix.det|\.det\b|trace" project/GMT/Ch02/Contract.lean`
- `python3 -I numcheck.py (exact rational brute-force check of the three child formulas, |ι| ≤ 4)`
- `lean -o cand/olean/GMT/Ch02/Submission.olean cand/src/Submission.lean; lean probe/Stmts.lean; lean probe/Children.lean; lean probe/Assembly.lean; lean probe/Inst.lean (pp.explicit instance check)`
- `python3 -I gen_checks.py (gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement); lean checks/NodeChallenge_0{0..3}_*.lean against pristine olean; lean checks/NodeSolution_0{0..3}_*.lean + #print axioms against candidate olean`
- `python3 -I scan of dag.json lean_name fields and nodes/*/decomposition-v*.json subproblem lean_names; rg of the three proposed names in simongmt/Poincare, GMT sources, dag.json and nodes/`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/GroupTheory/Perm/Sign.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Logic/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Matrix/Diagonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1-det-derivatives-at-one-a1/parent-child-handoff.json`
- `/tmp/detsplit-mTxVqt/probe/Stmts.lean`
- `/tmp/detsplit-mTxVqt/probe/Children.lean`
- `/tmp/detsplit-mTxVqt/probe/Assembly.lean`
- `/tmp/detsplit-mTxVqt/probe/Inst.lean`
- `/tmp/detsplit-mTxVqt/cand/src/Submission.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeChallenge_00_variation_matrix_det_hasDerivAt_leibniz.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeChallenge_01_variation_matrix_det_leibniz_first_order_at_one.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeChallenge_02_variation_matrix_det_leibniz_second_order_at_one.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeChallenge_03_variation_matrix_det_derivatives_at_one.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeSolution_00_variation_matrix_det_hasDerivAt_leibniz.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeSolution_01_variation_matrix_det_leibniz_first_order_at_one.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeSolution_02_variation_matrix_det_leibniz_second_order_at_one.lean`
- `/tmp/detsplit-mTxVqt/checks/NodeSolution_03_variation_matrix_det_derivatives_at_one.lean`
- `/tmp/detsplit-mTxVqt/proposal.json`
- `/tmp/detsplit-scripts/numcheck.py`
- `/tmp/detsplit-scripts/gen_checks.py`
- `/tmp/detsplit-scripts/scope.py`

The pinned snapshot (Mathlib 25730c7c, SimonGMT 2b36630) has no analytic derivative of Matrix.det along a matrix-valued function and no second-order coefficient of det(1 + A), so neither child can be taken from the library.

No-match and partial-match results:
- The det-with-derivative rg over Mathlib matched only measure-theoretic lemmas in MeasureTheory/Function/Jacobian.lean.
- Charpoly/Coeff.lean has only first-order polynomial lemmas: coeff_det_one_add_X_smul_one, det_one_add_X_smul and det_one_add_smul.
- The second-order coefficient search had no match.
- SimonGMT has only the first-order polynomial lemma derivative_eval_zero_det_one_add_X_smul_add_sq_smul, in Chapter08/FirstVariation.lean.
- The snapshot's Ch02 contract mentions det only in the areaJacobian and coarea definitions.

All ingredients the children need exist in the snapshot:
- Child A: Matrix.det_apply' (Determinant/Basic.lean:70), HasDerivAt.fun_finsetProd (Deriv/Mul.lean:398), HasDerivAt.const_mul (Mul.lean:344) and HasDerivAt.fun_sum (Deriv/Add.lean:218).
- Children B and C: Matrix.one_apply_eq/one_apply_ne (Data/Matrix/Diagonal.lean:238/242), Equiv.swap_apply_left/right/of_ne_of_ne (Logic/Equiv/Basic.lean:652–659), Equiv.Perm.sign_swap (GroupTheory/Perm/Sign.lean:388), Finset.prod_pair/prod_subset (BigOperators/Group/Finset/Basic.lean:86/203) and Matrix.trace (Trace.lean:43).
- Parent assembly: HasDerivAt.mul (Mul.lean:255) and HasDerivAt.congr_of_eventuallyEq (Deriv/Basic.lean:606).

Scratch Lean results:
- All three children were fully proved.
- The frozen parent type was proved from them.
- Every NodeChallenge module elaborates, and every NodeSolution module passes with only propext, Classical.choice and Quot.sound.
- An independent reviewer re-ran all of this, added a nanoda replay, and accepted.

The three proposed names do not occur in dag.json, any decomposition file, SimonGMT or the GMT sources.
