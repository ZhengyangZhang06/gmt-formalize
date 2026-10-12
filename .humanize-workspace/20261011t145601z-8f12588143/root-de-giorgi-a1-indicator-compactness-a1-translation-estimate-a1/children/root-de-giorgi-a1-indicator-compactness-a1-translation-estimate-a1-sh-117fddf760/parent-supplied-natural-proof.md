# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.shift_change_of_variables-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 5(a) of the parent proof. Substituting z = y + h and using translation invariance of Lebesgue measure gives ∫ χ(y+h)ψ(y) dy = ∫ χ(z)ψ(z−h) dz, hence ∫ wψ = ∫_F (ψ(z − h) − ψ(z)) dz. Here ψ is only assumed integrable.

Notation.
- 1_F is the real indicator of F.
- ψ_h(z) := ψ(z − h).
- G := 1_F·ψ_h (= F.indicator ψ_h) and H := 1_F·ψ (= F.indicator ψ).
- ∫_F f := ∫ f d(L^N⌞F).

1. (The translate is integrable.) L^N is invariant under translations, so ψ_h is integrable (Integrable.comp_sub_right).

2. (Integrability of the pieces.) F is null-measurable, and ψ_h and ψ are integrable, in particular on F. So G and H are integrable (integrable_indicator_iff₀). By translation invariance again, y ↦ G(y + h) is integrable (Integrable.comp_add_right).

3. (Pointwise rewriting.) For every y, (1_F(y + h) − 1_F(y))·ψ(y) = G(y + h) − H(y). Indeed:
- G(y + h) = 1_F(y + h)·ψ((y + h) − h) = 1_F(y + h)·ψ(y);
- H(y) = 1_F(y)·ψ(y).
Checking the four cases (y + h ∈ F or not, y ∈ F or not) confirms the identity.

4. (Linearity.) By step 2, ∫ (G(y + h) − H(y)) dy = ∫ G(y + h) dy − ∫ H(y) dy.

5. (Translation invariance.) The map y ↦ y + h preserves L^N, so ∫ G(y + h) dy = ∫ G(z) dz (integral_add_right_eq_self).

6. (Indicator integrals.) Since F is null-measurable, ∫ G = ∫_F ψ_h and ∫ H = ∫_F ψ (integral_indicator₀).

7. (Linearity on F.) ψ_h and ψ are integrable on F, so ∫_F ψ_h − ∫_F ψ = ∫_F (ψ_h − ψ) = ∫_F (ψ(z − h) − ψ(z)) dz.

8. (Conclusion.) Chaining steps 3–7 gives ∫ (1_F(y + h) − 1_F(y))·ψ(y) dy = ∫_F (ψ(z − h) − ψ(z)) dz. ∎

## Key steps

1. ψ(· − h) is integrable. So are F.indicator ψ(· − h), F.indicator ψ, and y ↦ F.indicator ψ(· − h) evaluated at y + h.
2. Pointwise, (1_F(y+h) − 1_F(y))ψ(y) = [1_F ψ(· − h)](y + h) − [1_F ψ](y).
3. Translation invariance: ∫ [1_F ψ(· − h)](y + h) dy = ∫ 1_F ψ(· − h) (integral_add_right_eq_self).
4. integral_indicator₀ for the null-measurable F, plus linearity, gives ∫_F (ψ(z − h) − ψ(z)) dz.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; cmp GMT/Ch03/Contract.lean GMT/Ch03/Submission.lean; git rev-parse HEAD; lake-manifest.json revs of mathlib and simongmt`
- `python3 -I lean_name collision check against dag.json (200 nodes) for indCompact_transEst_volume_symmDiff_eq_integral, indCompact_transEst_integral_indicator_shift_mul, indCompact_transEst_setIntegral_shift_sub_ftc, indCompact_transEst_abs_setIntegral_fderiv_le and any 'transEst' name; DAG metadata of translation_estimate-a1 and l1_duality-a1`
- `git log --all --oneline -S'indCompact_transEst_'; grep -rn 'indCompact_transEst_' GMT .lake/packages/simongmt/Poincare`
- `python3 -I /tmp/transest-v2/scripts/gen.py (importlib of verifier/gmt-compare.py layout/child_modules/contract_scope and verifier/lean_contract.py validate_lean_statement) on the 4 child types; lake env lean on each generated NodeChallenge.lean`
- `lake env lean /tmp/transest-v2/lean/FullCheckV1Copy.lean (attempt-1 scratch proofs; #print axioms)`
- `lake env lean /tmp/transest-v2/lean/AssemblyCheck.lean (4 child proofs, `exact Submission.X` comparator targets, parentFromChildren with the frozen l1_duality type as hypothesis, instance sanity examples, #print axioms)`
- `rg -n 'indicator_symmDiff|mulIndicator_symmDiff|integral_mul_right_eq_self|integrableOn_of_bounded|comp_homeomorph|tsupport_comp_eq_preimage|norm_integral_le_of_norm_le_const|trace_smulRight|fderiv_smul_const|fderiv_of_notMem_tsupport|prod_restrict|integral_integral_swap|fderiv_comp_sub|fderiv_const_mul|tsupport_smul_subset_left|tsupport_mul_subset_right|integrable_indicator_iff₀|integral_indicator₀|of_forall_sdiff_eq_zero' <snapshot>/mathlib/Mathlib`
- `rg -n 'euclideanDivergence' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean; rg -n -i 'translation|symmDiff|indicator' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `grep -n -i 'compactness' book/chapter-03.txt; sed -n 590,630p book/chapter-02.txt; sed -n 640,665p book/chapter-03.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Algebra/Order/Group/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/TransEstSplitDecisionFullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/TransEstSplitDecisionV2AssemblyCheck.lean`
- `/tmp/transest-v2/challenges/indCompact_transEst_volume_symmDiff_eq_integral/NodeChallenge.lean`
- `/tmp/transest-v2/challenges/indCompact_transEst_integral_indicator_shift_mul/NodeChallenge.lean`
- `/tmp/transest-v2/challenges/indCompact_transEst_setIntegral_shift_sub_ftc/NodeChallenge.lean`
- `/tmp/transest-v2/challenges/indCompact_transEst_abs_setIntegral_fderiv_le/NodeChallenge.lean`
- `/tmp/transest-v2/lean/AssemblyCheck.lean`

Snapshot consistency: the snapshot contract is byte-identical to the workspace Contract.lean, and Submission.lean is still a byte copy. HEAD is d09bc8a and the pins are Mathlib 25730c7c and simongmt 2b366308.

Library coverage. None of the four child statements exists in Mathlib or SimonGMT:
- SimonGMT Chapter02/BV.lean only defines euclideanDivergence g x := trace(fderiv g x) and proves coordinate, measurability and Lipschitz-bound lemmas.
- Neither library has a BV translation estimate.

Every ingredient the child proofs cite is present in the pinned snapshot:
- abs_indicator_symmDiff (via to_additive of mabs_mulIndicator_symmDiff); integral_add_right_eq_self (via integral_mul_right_eq_self).
- Measure.integrableOn_of_bounded and IntegrableOn.of_forall_sdiff_eq_zero.
- HasCompactSupport.comp_homeomorph and tsupport_comp_eq_preimage.
- intervalIntegral.norm_integral_le_of_norm_le_const.
- LinearMap.trace_smulRight, fderiv_smul_const, fderiv_of_notMem_tsupport, fderiv_comp_sub and fderiv_const_mul.
- Measure.prod_restrict (arbitrary sets) and integral_integral_swap.
- tsupport_smul_subset_left and tsupport_mul_subset_right.
- integrable_indicator_iff₀ and integral_indicator₀.

Lean results:
- All four child types validate and elaborate in the generated comparator scope.
- Complete child proofs compile with only propext, Classical.choice and Quot.sound.
- The exact frozen parent type compiles from them plus the frozen l1_duality type passed as a hypothesis, again with only those axioms.

Names: the four lean_names are unreserved in the 200-node DAG, in git history and in the GMT/SimonGMT sources.
