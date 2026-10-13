# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.ftc_fubini_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 5(b) and 5(d) of the parent proof: the fundamental theorem of calculus along t ↦ ψ(z − th), and Fubini for (z, t) ↦ 1_F(z)·Dψ(z − th)[h]. Here F is an arbitrary set. Let μ := L^N⌞F (so μ ≤ L^N, and μ is s-finite) and ν := L^1⌞(0,1].

1. (Continuity.) Since ψ is C¹, it is differentiable everywhere and x ↦ Dψ(x) is continuous (ContDiff.differentiable, ContDiff.continuous_fderiv). Hence f(z, t) := Dψ(z − th)[h] is continuous on ℝ^N × ℝ: it is the continuous map (z,t) ↦ z − th, followed by Dψ, evaluated at the fixed vector h.

2. (FTC for fixed z.) Fix z and let g(t) := ψ(z − th). The map t ↦ z − th has derivative −h, so by the chain rule g'(t) = Dψ(z − th)[−h] = −f(z, t). Since g' is continuous, it is interval-integrable on [0,1]. The fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt) gives g(1) − g(0) = ∫_0^1 g'(t) dt, i.e. ψ(z − h) − ψ(z) = −∫_0^1 f(z, t) dt.

3. (Reduction to Fubini.) Integrating the identity of step 2 over F:
∫_F (ψ(z − h) − ψ(z)) dz = ∫_F (−∫_0^1 f(z,t) dt) dz = −∫_F ∫_0^1 f(z,t) dt dz.
Since 0 ≤ 1, ∫_0^1 φ(t) dt = ∫ φ dν for every φ (intervalIntegral.integral_of_le). It therefore suffices to prove
∫ (∫ f(z,t) dν(t)) dμ(z) = ∫ (∫ f(z,t) dμ(z)) dν(t).
This is Fubini's theorem for s-finite measures (integral_integral_swap), once f is μ ⊗ ν-integrable.

4. (Integrability.) By Measure.prod_restrict, μ ⊗ ν = (L^N ⊗ L^1)⌞(F × (0,1]). Let K := {x + s h : x ∈ tsupport ψ, s ∈ [0,1]}. It is the image of the compact set tsupport ψ × [0,1] under the continuous map (x, s) ↦ x + s h, so K is compact.
 (a) f is continuous, K × [0,1] is compact, and L^N ⊗ L^1 is finite on compact sets. Hence f is integrable on K × [0,1] (ContinuousOn.integrableOn_compact).
 (b) f vanishes on (ℝ^N × [0,1]) \ (K × [0,1]). Indeed, let t ∈ [0,1] with f(z,t) ≠ 0. Then Dψ(z − th) ≠ 0. Since ψ ≡ 0 on the open set ℝ^N \ tsupport ψ, its derivative vanishes there (fderiv_of_notMem_tsupport). So z − th ∈ tsupport ψ, and z = (z − th) + t h ∈ K.
 (c) ℝ^N × [0,1] is measurable, so (a) and (b) show that f is integrable on ℝ^N × [0,1] (IntegrableOn.of_forall_sdiff_eq_zero). Hence f is integrable on the subset F × (0,1] (IntegrableOn.mono_set), i.e. f is μ ⊗ ν-integrable.

5. (Conclusion.) By Fubini, ∫_F ∫_0^1 f(z,t) dt dz = ∫_0^1 ∫_F f(z,t) dz dt. Together with step 3, ∫_F (ψ(z − h) − ψ(z)) dz = −∫_0^1 (∫_F Dψ(z − th)[h] dz) dt. ∎

## Key steps

1. f(z,t) := Dψ(z − th)[h] is continuous on ℝ^N × ℝ because ψ is C¹.
2. FTC along t ↦ ψ(z − th) gives ψ(z − h) − ψ(z) = −∫_0^1 f(z,t) dt for every z.
3. Integrate over F, write ∫_0^1 as the integral over (0,1], and reduce to Fubini for L^N⌞F ⊗ L^1⌞(0,1] (integral_integral_swap).
4. Integrability: f is continuous on the compact set K × [0,1], where K = tsupport ψ + [0,1]h, and vanishes on (ℝ^N × [0,1]) \ (K × [0,1]). Since F × (0,1] ⊆ ℝ^N × [0,1], f is integrable for the product measure.
5. Swap the integrals to obtain −∫_0^1 ∫_F Dψ(z − th)[h] dz dt.

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
