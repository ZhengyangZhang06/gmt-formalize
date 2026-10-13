# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.diagonal_arzela_ascoli-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 4 of the parent proof (the mollified functions are uniformly bounded and equicontinuous, uniformly in k) together with Step 5 (Arzelà–Ascoli on each B̄_m(0) and the diagonal subsequence φ(k) = ψ_k(k)). Here the kernels are arbitrary continuous compactly supported ρ_m instead of φ_{1/m}. The Lipschitz modulus ∫|∇φ_σ| of Step 4 is replaced by the modulus of continuity of ρ_m, which is all that Arzelà–Ascoli needs.

Notation.
- For m ∈ ℕ and S ⊆ ℝ^N, V_m(S)(y) := ∫_S ρ_m(y − z) dz, the integral of z ↦ ρ_m(y − z) against L^N⌞S.
- K_m := B̄_m(0), a compact metric space.
- No measurability of S is needed: the only property of L^N⌞S used is L^N⌞S ≤ L^N (Measure.restrict_le_self).

1. (Kernel facts.) ρ_m is continuous with compact support. Hence it is bounded, uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous) and integrable. For each y, the map z ↦ ρ_m(y − z) is L^N-integrable, with ∫ |ρ_m(y − z)| dz = A_m := ∫ |ρ_m|, by invariance of L^N under z ↦ y − z. Hence it is also integrable for L^N⌞S.

2. (Uniform bound.) For all S and y: |V_m(S)(y)| ≤ ∫_S |ρ_m(y − z)| dz ≤ ∫ |ρ_m(y − z)| dz = A_m.

3. (Equicontinuity, uniform in S.) Let y, y' ∈ ℝ^N, let S be any set, and put d := y' − y. Substituting u = y − z,
 |V_m(S)(y) − V_m(S)(y')| = |∫_S (ρ_m(y − z) − ρ_m(y' − z)) dz| ≤ ∫ |ρ_m(y − z) − ρ_m(y' − z)| dz = ∫ |ρ_m(u) − ρ_m(u + d)| du.
 Let T_m := tsupport ρ_m, which is compact, and T'_m := {u : dist(u, T_m) ≤ 1}, which is compact and has finite measure. For |d| ≤ 1 the last integrand vanishes off T'_m. So the right side is ≤ L^N(T'_m)·sup_u |ρ_m(u) − ρ_m(u + d)|, which tends to 0 as d → 0 by uniform continuity. Hence for every η > 0 there is δ > 0 such that, for every S, |y − y'| < δ implies |V_m(S)(y) − V_m(S)(y')| ≤ η. In particular every V_m(S) is continuous.

4. (Arzelà–Ascoli for fixed m.) By steps 2–3, each restriction V_m(S)|_{K_m} is a bounded continuous function on K_m. Consider the family 𝒜_m := {V_m(S)|_{K_m} : S ⊆ ℝ^N} ⊆ C_b(K_m), with the sup metric. It takes values in the compact interval [−A_m, A_m] and is equicontinuous. By the Arzelà–Ascoli theorem (Mathlib BoundedContinuousFunction.arzela_ascoli), the closure of 𝒜_m is compact.
 Consequently, for every sequence (S_j) of subsets of ℝ^N there is a strictly increasing θ such that (V_m(S_{θ(j)})|_{K_m})_j converges in C_b(K_m) (IsCompact.tendsto_subseq). A convergent sequence is Cauchy, and the sup distance dominates pointwise distances. So for every ε > 0 there is j₀ with |V_m(S_{θ(j)})(y) − V_m(S_{θ(j')})(y)| ≤ ε for all j, j' ≥ j₀ and all y ∈ K_m.

5. (Diagonal subsequence.) Put ψ_{−1} := id. Recursively, for m = 0, 1, 2, …, let θ_m be the strictly increasing map given by step 4 for the index m and the sequence S_j := F_{ψ_{m−1}(j)}, and put ψ_m := ψ_{m−1} ∘ θ_m. Then each ψ_m is strictly increasing, and (V_m(F_{ψ_m(j)}))_j is uniformly Cauchy on K_m. Define φ(k) := ψ_k(k).
 (a) φ is strictly increasing. A strictly increasing θ : ℕ → ℕ satisfies θ(n) ≥ n. Hence φ(k + 1) = ψ_k(θ_{k+1}(k + 1)) ≥ ψ_k(k + 1) > ψ_k(k) = φ(k).
 (b) Fix m. For k ≥ m, ψ_k = ψ_m ∘ τ_{m,k}, where τ_{m,k} := θ_{m+1} ∘ ⋯ ∘ θ_k (and τ_{m,m} = id). This map is strictly increasing, so τ_{m,k}(n) ≥ n. Hence φ(k) = ψ_m(τ(k)) with τ(k) := τ_{m,k}(k) ≥ k.
 (c) Given ε > 0, let j₀ be as in step 4 for the sequence (F_{ψ_m(j)})_j, and put k₀ := max(m, j₀). For k, l ≥ k₀ we have τ(k) ≥ j₀ and τ(l) ≥ j₀. So for all y ∈ K_m, |V_m(F_{φ(k)})(y) − V_m(F_{φ(l)})(y)| = |V_m(F_{ψ_m(τ(k))})(y) − V_m(F_{ψ_m(τ(l))})(y)| ≤ ε.
 This is the assertion.

 An equivalent packaging of step 5: the sequence k ↦ (V_m(F_k)|_{K_m})_{m∈ℕ} lies in ∏_m closure(𝒜_m). This product is compact by Tychonoff (isCompact_univ_pi) and sits in the first-countable countable product ∏_m C_b(K_m). So a subsequence φ converges in every coordinate, i.e. uniformly on every K_m, which again gives the uniform Cauchy property. ∎

## Key steps

1. V_m(S) := ∫_S ρ_m(· − z) dz satisfies |V_m(S)| ≤ ∫|ρ_m| for every set S, using only L^N⌞S ≤ L^N.
2. |V_m(S)(y) − V_m(S)(y')| ≤ ∫|ρ_m(u) − ρ_m(u + y' − y)| du → 0, uniformly in S, by uniform continuity and compact support.
3. Arzelà–Ascoli in C_b(B̄_m(0)): every sequence V_m(S_j) has a subsequence that is uniformly Cauchy on B̄_m(0).
4. Diagonal extraction: with ψ_m = ψ_{m−1} ∘ θ_m, the map φ(k) = ψ_k(k) is strictly increasing, and φ(k) = ψ_m(τ(k)) with τ(k) ≥ k for k ≥ m. This gives the uniform Cauchy property on every B̄_m(0).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope(Contract.lean, 'GMT.Ch03.main_theorem') + child_modules(...) -> /tmp/indcompact-decomp/challenges/Challenge_*.lean; lake env lean on each of the 5 files`
- `lake env lean /tmp/indcompact-decomp/Assembly.lean (#print axioms Submission.deGiorgi_indicator_compactness_assembly); lake env lean /tmp/indcompact-decomp/Interface.lean`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the 5 child types`
- `python3 -I lean_name collision check against dag.json (141 nodes) and grep -rn indCompact GMT/ .lake/packages/simongmt/Poincare`
- `grep -n -i 'compactness|arzela|subsequence|mollif|convolution|translation|duality' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `grep -n 'theorem|def |lemma' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; grep -rn 'ae_convolution_tendsto|ContDiffBump.normed' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'theorem integral_normed|theorem support_normed_eq|theorem nonneg_normed|theorem continuous_normed|theorem hasCompactSupport_normed|theorem integrable_normed|def normed' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/*.lean`
- `grep -rn 'theorem ae_convolution_tendsto_right_of_locallyIntegrable|theorem arzela_ascoli|theorem IsCompact.tendsto_subseq|theorem extraction_forall_of_eventually' <snapshot>/mathlib/Mathlib`
- `rg -n -i 'kolmogorov|riesz.?kolmogorov|frechet.?kolmogorov' <snapshot>/mathlib/Mathlib`
- `rg -n 'contDiff_convolution_left|continuous_convolution_left|theorem restrict_le_self' <snapshot>/mathlib/Mathlib`
- `grep -rn 'uniformContinuous_of_continuous|trace_smulRight' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem symmDiff_triangle|theorem abs_indicator_symmDiff|theorem integral_indicator_const|theorem toMeasurable_ae_eq|theorem tendsto_integral_of_dominated_convergence|theorem integral_eq_sub_of_hasDerivAt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem lintegral_lintegral_swap|theorem integral_integral_swap|theorem setIntegral_congr_set|theorem restrict_congr_set|theorem setLIntegral_const|theorem ofReal_integral_eq_lintegral_ofReal' <snapshot>/mathlib/Mathlib`
- `grep -rn 'FirstCountableTopology (∀ i' <snapshot>/mathlib/Mathlib/Topology/Bases.lean`
- `grep -n -i 'import' verifier/gmt-compare.py verifier/lean_contract.py; git show <branch>:GMT/Ch03/Submission.lean | grep '^import' over humanize-recursive branches`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1/parent-supplied-natural-proof.md`
- `/tmp/indcompact-decomp/Assembly.lean`
- `/tmp/indcompact-decomp/Interface.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c).

Missing from the libraries, so these become children:
- Mathlib has no BV or Kolmogorov–Riesz compactness: rg 'kolmogorov' matches only the extension theorem and T0 spaces.
- SimonGMT Chapter02/BV.lean provides only the closure half and states that 'Extracting a convergent subsequence remains the compactness obligation'.
- Neither library has an L¹-duality lemma for balls, a BV translation estimate, or a completeness lemma for local symmetric-difference convergence.

Library support found for the child proofs:
- ContDiffBump.normed API (nonneg/continuous/integral/support/hasCompactSupport_normed).
- ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable. SimonGMT Chapter08 already reuses it in constancyMollifier / ae_constancyMollifier_convolution_tendsto.
- HasCompactSupport.contDiff_convolution_left and continuous_convolution_left.
- BoundedContinuousFunction.arzela_ascoli, IsCompact.tendsto_subseq, and the countable-pi FirstCountableTopology instance.
- HasCompactSupport.uniformContinuous_of_continuous.
- LinearMap.trace_smulRight, which gives div(ψ(·−th)h) = Dψ(·−th)[h].
- integral_integral_swap, lintegral_lintegral_swap and intervalIntegral.integral_eq_sub_of_hasDerivAt.
- symmDiff_triangle, abs_indicator_symmDiff, integral_indicator_const, toMeasurable_ae_eq, Measure.restrict_le_self, Measure.restrict_congr_set, setLIntegral_const and ofReal_integral_eq_lintegral_ofReal.
- SimonGMT euclideanDivergence_eq_sum_inner, measurable_euclideanDivergence and support_euclideanDivergence_subset.

Lean results:
- All five child types elaborate in the exact NodeChallenge scope and pass lean_contract validation.
- The parent assembly compiles from the child stubs with only propext, Classical.choice, Quot.sound and the stubs' sorryAx. It needs the Mathlib BumpFunction.Normed and BumpFunction.InnerProduct imports; one existing DAG branch already adds a Submission import.
- No lean_name collides with dag.json.
