# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.slice_divergence_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 2 and 5(c) of the parent proof.
- Step 2 tests the hypothesis with ±G/λ.
- Step 5(c) uses the field Ψ_t(z) = ψ(z − th)h. It is C¹, has compact support in B_{R+1}(0) and |Ψ_t| ≤ |h|, and div Ψ_t(z) = Dψ(z − th)[h] by the trace of a rank-one map.
Here the shift is an arbitrary a with |a| ≤ 1 (the parent uses a = th), and F is an arbitrary set. Integrals over F are taken with respect to L^N⌞F, and constant factors can be pulled out of them (integral_const_mul). Recall div g(x) = trace(Dg(x)) (SimonGMT euclideanDivergence g x = LinearMap.trace (fderiv g x)).

1. (Case h = 0.) Then Dψ(z − a)[0] = 0 for all z, so the integral is 0 = C·|0|, and the claim holds. From now on h ≠ 0, so |h| > 0. Put I := ∫_F Dψ(z − a)[h] dz.

2. (Translated profile.) Let τ(y) := y − a, a homeomorphism of ℝ^N, and ψ_a(y) := ψ(y − a) = ψ(τ(y)).
- ψ_a has compact support (HasCompactSupport.comp_homeomorph).
- tsupport ψ_a = τ⁻¹(tsupport ψ) = {y : y − a ∈ tsupport ψ} (tsupport_comp_eq_preimage).
- If y ∈ tsupport ψ_a, then y − a ∈ tsupport ψ ⊆ B_R(0), so |y| ≤ |y − a| + |a| < R + 1.
Hence tsupport ψ_a ⊆ B_{R+1}(0). (The parent proof reaches the same inclusion through R' := max over tsupport ψ of |·| < R; the direct pointwise estimate suffices.)

3. (Claim: if c ∈ ℝ and |c| = |h|⁻¹, then cI ≤ C.) Fix such c and let G(y) := (c·ψ(y − a))·h.
 (a) G is C¹. The map y ↦ c·ψ(y − a) is C¹ (ψ composed with an affine map, times a constant), and multiplying it by the fixed vector h preserves C¹.
 (b) support G ⊆ support ψ_a, hence tsupport G ⊆ tsupport ψ_a (tsupport_smul_subset_left, tsupport_mul_subset_right). So G has compact support, being a closed subset of the compact set tsupport ψ_a, and tsupport G ⊆ B_{R+1}(0) by step 2.
 (c) For every y, |G(y)| = |c|·|ψ(y − a)|·|h| = |h|⁻¹·|ψ(y − a)|·|h| = |ψ(y − a)| ≤ 1.
 (d) (Divergence.) Put φ(y) := c·ψ(y − a). Then φ is differentiable everywhere and G(y) = φ(y)·h.
 - DG(z) = Dφ(z).smulRight h, i.e. DG(z)[v] = Dφ(z)[v]·h (fderiv_smul_const).
 - The trace of the rank-one linear map v ↦ ℓ(v)·h is ℓ(h) (LinearMap.trace_smulRight). So div G(z) = trace DG(z) = Dφ(z)[h].
 - By the constant-multiple and translation rules (fderiv_const_mul, fderiv_comp_sub), Dφ(z) = c·Dψ(z − a).
 Therefore div G(z) = c·Dψ(z − a)[h] for every z.
 (e) By (a)–(c), G satisfies the hypotheses of the assumption, so ∫_F div G ≤ C. By (d), ∫_F div G = ∫_F c·Dψ(z − a)[h] dz = c·I. Hence cI ≤ C.

4. (Two-sided bound.)
- With c = |h|⁻¹, step 3 gives |h|⁻¹·I ≤ C. Multiplying by |h| > 0 yields I ≤ C|h|.
- With c = −|h|⁻¹, it gives −|h|⁻¹·I ≤ C, hence −I ≤ C|h|.
Therefore |∫_F Dψ(z − a)[h] dz| = |I| ≤ C|h|. ∎

## Key steps

1. The case h = 0 is trivial; otherwise |h| > 0.
2. tsupport ψ(· − a) = a + tsupport ψ is compact and lies in B_{R+1}(0), since |y| ≤ |y − a| + |a| < R + 1.
3. For |c| = |h|⁻¹, the field G = cψ(· − a)h is C¹, compactly supported in B_{R+1}(0), and satisfies |G| ≤ 1.
4. div G(z) = c·Dψ(z − a)[h], by fderiv_smul_const, LinearMap.trace_smulRight and the chain rule for the translation.
5. The hypothesis gives c·I ≤ C. Taking c = ±|h|⁻¹ yields |I| ≤ C|h|.

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
