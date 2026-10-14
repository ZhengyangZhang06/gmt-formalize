# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.integrand_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1, 4 and the pointwise part of Step 5 of the supplied proof of the radial homotopy formula, specialized to arbitrary L and α.

Notation. E := ℝ^P. For w ∈ E^{k+2}, Alt(L)(w) := alternatizeUncurryFin L w. Write (y, v) := Fin.cons y v and û_j := Fin.removeNth j u ∈ E^k. Put a_j := L(u_j)(x, û_j) and b_j := α(u_j, û_j) for j = 0, …, k. A sign (−1)^i with i : Fin _ means (−1)^{(i : ℕ)}.

1. (Alternatization formula.) By Mathlib's ContinuousAlternatingMap.alternatizeUncurryFin_apply, for every continuous linear f : E → Λ^{r}(E) and every w ∈ E^{r+1}: alternatizeUncurryFin f w = Σ_{i ∈ Fin (r+1)} (−1)^i • f(w_i)(removeNth i w). Here (−1)^i ∈ ℤ acts on ℝ as multiplication by the real number (−1)^i (zsmul_eq_mul, push_cast).
2. (Expansion at w = (x, u).) Apply Step 1 with f := L, r := k+1, w := (x, u) ∈ E^{k+2}. Split the sum over Fin (k+2) into the index 0 and the indices j.succ with j ∈ Fin (k+1) (Fin.sum_univ_succ).
   - Index 0: (−1)^0 = 1, w_0 = x (Fin.cons_zero) and removeNth 0 w = tail (Fin.cons x u) = u (Fin.removeNth_zero, Fin.tail_cons). The term is L(x)(u).
   - Index j.succ: (−1)^{j+1} = −(−1)^j (Fin.val_succ, pow_succ) and w_{j.succ} = u_j (Fin.cons_succ). Also removeNth (j.succ) (Fin.cons x u) = (Fin.cons x u) ∘ (j.succ).succAbove = Fin.cons x (removeNth j u), by the definition removeNth p f = f ∘ p.succAbove and Fin.cons_comp_succ_succAbove. The term is −(−1)^j a_j.
   Hence Alt(L)(x, u) = L(x)(u) − Σ_j (−1)^j a_j.
3. (Alternating identity.) Mathlib's ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft states alternatizeUncurryFin (curryLeft α) = (k+1) • α. Evaluate both sides at u ∈ E^{k+1}.
   - Left side: apply Step 1 with f := curryLeft α, r := k, w := u. By curryLeft_apply_apply, (curryLeft α)(y)(v) = α(Matrix.vecCons y v), and Matrix.vecCons y v = Fin.cons y v by definition. So the left side is Σ_j (−1)^j α(u_j, û_j) = Σ_j (−1)^j b_j.
   - Right side: ((k+1) • α)(u) = (k+1)·α(u) (smul_apply, nsmul_eq_mul).
   Thus Σ_j (−1)^j b_j = ((k:ℝ)+1)·α(u).
4. (Distribution.) For each j, (−1)^j·(t^k·(t·a_j + b_j)) = t^{k+1}·((−1)^j a_j) + t^k·((−1)^j b_j), using t^k·t = t^{k+1} and commutativity of ℝ. Summing over j (Finset.sum_add_distrib, Finset.mul_sum) gives Σ_j (−1)^j(t^k(t a_j + b_j)) = t^{k+1}·Σ_j (−1)^j a_j + t^k·Σ_j (−1)^j b_j.
5. (Conclusion.) By Steps 2 and 4, the left-hand side equals t^{k+1}·(L(x)(u) − Σ_j (−1)^j a_j) + t^{k+1}·Σ_j (−1)^j a_j + t^k·Σ_j (−1)^j b_j. The cross terms cancel, leaving t^{k+1}·L(x)(u) + t^k·Σ_j (−1)^j b_j. By Step 3 this equals t^{k+1}·L(x)(u) + t^k·((k+1)·α(u)) = t^{k+1}·L(x)(u) + (k+1)·t^k·α(u), which is the right-hand side. ∎

## Key steps

1. Expand Alt(L)(x, u) with alternatizeUncurryFin_apply and Fin.sum_univ_succ. Using removeNth 0 (cons x u) = u and removeNth (j.succ) (cons x u) = cons x (removeNth j u) (Fin.cons_comp_succ_succAbove), this gives Alt(L)(x, u) = L(x)(u) − Σ_j (−1)^j L(u_j)(x, û_j).
2. Evaluate alternatizeUncurryFin_curryLeft at u, rewritten with alternatizeUncurryFin_apply and curryLeft_apply_apply (vecCons = Fin.cons), to get Σ_j (−1)^j α(u_j, û_j) = (k+1)α(u).
3. Distribute (−1)^j t^k(t a_j + b_j) = t^{k+1}(−1)^j a_j + t^k(−1)^j b_j and sum over j.
4. The t^{k+1} cross terms cancel against the expansion, and the α-sum becomes (k+1)t^kα(u).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `grep -rn 'theorem alternatizeUncurryFin_apply|theorem alternatizeUncurryFin_curryLeft|def alternatizeUncurryFin|theorem extDeriv_apply|def extDeriv\b|theorem curryLeft_apply_apply|theorem cons_comp_succ_succAbove|theorem removeNth_zero|theorem integral_eq_sub_of_hasDerivAt\b|theorem integral_finsetSum|theorem integral_finset_sum' <snapshot>/mathlib/Mathlib`
- `grep -rn 'continuous_eval_const|theorem apply_apply|def apply |continuousAlternatingMap_apply' <snapshot>/mathlib/Mathlib/Topology/Algebra/Module/Alternating/*.lean <snapshot>/mathlib/Mathlib/Analysis/Normed/Module/Alternating/*.lean <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean`
- `rg -n -i 'radial homotopy|poincare_lemma|poincaré lemma|homotopy formula|coneOperator|radialHomotopy' <snapshot>/mathlib/Mathlib <snapshot>/project/GMT`
- `rg -n -i 'radial|homotopy formula|alternatizeUncurryFin_curryLeft|cons_comp_succ_succAbove' lake-packages-25730c7c/simongmt/Poincare; grep -rn 'DifferentialForm\b' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `rg -n 'theorem integral_eq_sub_of_hasDerivAt\b|theorem integral_const_mul|theorem integral_add ' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/*.lean`
- `python3 -I: lean_name scan of dag.json and nodes/*/decomposition-v*.json; git log --all --oneline -S 'iwl_cr_rh_'; grep iwl_cr_rh_ dag.json issue-workers.json GMT/Ch06/Submission.lean`
- `python3 -I /tmp/rh-decomp/scripts/gen.py (verifier gmt-compare.py child_modules in contract mode + lean_contract.validate_lean_statement); lake env lean /tmp/rh-decomp/gen/*__NodeChallenge.lean /tmp/rh-decomp/gen/*__SolutionEmu.lean`
- `lake env lean /tmp/rh-decomp/Elab1.lean, Elab2.lean, Assembly.lean, ChildA.lean, ChildB.lean, ChildC.lean, Full.lean (#print axioms)`
- `WebSearch: Poincaré lemma star-shaped homotopy operator identity ω = I dω + d I ω`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-scope-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rh-decomp/scripts/gen.py`
- `/tmp/rh-decomp/Assembly.lean`
- `/tmp/rh-decomp/ChildA.lean`
- `/tmp/rh-decomp/ChildB.lean`
- `/tmp/rh-decomp/ChildC.lean`
- `/tmp/rh-decomp/Full.lean`

**Snapshot.** Project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…).

**Definitions used by the statements.**
- SimonGMT Chapter06/Forms.lean: Covector E n := E [⋀^Fin n]→L[ℝ] ℝ and DifferentialForm E n := E → Covector E n.
- Mathlib DifferentialForm/Basic.lean:72: extDeriv ω x := alternatizeUncurryFin (fderiv ℝ ω x), defined for every ω.

**Library inputs.**
- Normed Alternating/Uncurry/Fin.lean: alternatizeUncurryFin_apply (:137), with a ℤ-power coefficient (-1)^i • …, and alternatizeUncurryFin_curryLeft (:154).
- Normed Alternating/Curry.lean:57: curryLeft_apply_apply, stated with Matrix.vecCons, which equals Fin.cons by rfl (checked in Lean).
- Data/Fin/Tuple/Basic.lean:882: Fin.cons_comp_succ_succAbove; also Fin.removeNth_zero and Fin.tail_cons.
- IntervalIntegral/FundThmCalculus.lean:1148: integral_eq_sub_of_hasDerivAt.
- IntervalIntegral/Basic.lean: integral_add (:774), integral_finsetSum (:778; integral_finset_sum is deprecated) and integral_const_mul (:817).
- hasDerivAt_pow (derivative ↑n * x^(n-1)) and ContDiff.continuous_fderiv.
- Topology/Algebra/Module/Alternating/Topology.lean: ContinuousAlternatingMap.apply (:294, evaluation as a continuous linear map) and the ContinuousEvalConst instance (:189).

**No-match results.**
- No radial homotopy formula or Poincaré lemma for k-forms exists in the snapshot Mathlib. CurveIntegral/Poincare.lean covers only 1-forms via curve integrals on convex sets and does not apply.
- No such formula exists in the project or the SimonGMT package (rg found only unrelated 'radial' files in Chapters 04, 05 and 08).
- The names iwl_cr_rh_integrand_identity, iwl_cr_rh_radial_ftc and iwl_cr_rh_degree_zero are unused in dag.json, the decomposition files, Submission.lean and all git refs.

**Lean checks (lake env lean, contract scope after import GMT.Ch06.Submission).**
- The three child types pass validate_lean_statement and elaborate as the comparator's generated NodeChallenge modules.
- An assembly proves the frozen parent type from the three children.
- Scratch proofs of all children together with the assembled parent compile with no sorry. #print axioms shows [propext, Classical.choice, Quot.sound].
- Emulated NodeSolution checks (exact Submission.X) pass.

**Public citation.** Wikipedia, 'Poincaré lemma' (https://en.wikipedia.org/wiki/Poincar%C3%A9_lemma), states the homotopy formula h_1^* − h_0^* = dJ + Jd, here for the homotopy f_t(x) = tx. For background, see also the standard star-shaped Poincaré lemma in Spivak, Calculus on Manifolds, Thm 4-11. The children's proofs are self-contained direct computations extracted from the supplied parent proof.
