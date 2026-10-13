# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This combines two steps of the parent proof, with the kernels ρ_m (support in B̄_{1/(m+1)}(0)) in place of φ_{1/m}:
- Step 3, the mollification error ‖φ_σ * χ_k − χ_k‖_{L¹(B_R)} ≤ σC_{R+1}, obtained from (φ_σ * χ_k)(y) − χ_k(y) = ∫ φ_σ(h)(χ_k(y − h) − χ_k(y)) dh, Fubini, and the translation estimate at −h;
- Step 6, the Cauchy property in L¹(B_R) via the three-term triangle inequality.

Notation.
- χ_k := 1_{F_k}, and v_{m,k}(y) := ∫_{F_k} ρ_m(y − z) dz.
- σ_m := 1/(m+1) ∈ (0, 1].
- For a set S and h ∈ ℝ^N, S_h := {y : y + h ∈ S}.
- B_R := B_R(0), and ∫⁻ denotes the [0, ∞]-valued lower integral.

0. (WLOG F_k measurable.) Replace each F_k by a measurable F'_k with F'_k = F_k a.e.
- The measures L^N⌞F_k and L^N⌞F'_k coincide, so every v_{m,k} is unchanged.
- Translation preserves L^N, so (F'_k)_h = (F_k)_h a.e., and the translation hypothesis is unchanged.
- B_R ∩ (F'_k Δ F'_l) = B_R ∩ (F_k Δ F_l) a.e., so the conclusion is unchanged.
Assume all F_k are measurable.

1. (Kernel facts.)
- Each ρ_m is continuous with compact support, hence bounded and integrable.
- If ρ_m(h) ≠ 0, then |h| ≤ σ_m ≤ 1.
- Each v_{m,k} is continuous. Let y_n → y. Then ρ_m(y_n − z) → ρ_m(y − z) for every z. Once |y_n − y| ≤ 1, we have |ρ_m(y_n − z)| ≤ (sup |ρ_m|)·1_{B̄_{|y|+2}(0)}(z). Dominated convergence gives v_{m,k}(y_n) → v_{m,k}(y).
In particular each v_{m,k} is measurable.

2. (Mollification error.) Claim: let m, k, R ∈ ℕ and C' ≥ 0 satisfy L^N(B_R ∩ ((F_k)_h Δ F_k)) ≤ ofReal(C'|h|) for all |h| ≤ 1. Then ∫⁻_{B_R} ofReal|v_{m,k}(y) − χ_k(y)| dy ≤ ofReal(σ_m C').
 (i) Fix y and substitute z = y − h; L^N is invariant under z ↦ y − z. This gives v_{m,k}(y) = ∫ ρ_m(y − z)χ_k(z) dz = ∫ ρ_m(h)χ_k(y − h) dh. Since ∫ρ_m = 1, χ_k(y) = ∫ ρ_m(h)χ_k(y) dh. Hence v_{m,k}(y) − χ_k(y) = ∫ ρ_m(h)(χ_k(y − h) − χ_k(y)) dh. As ρ_m ≥ 0, ofReal|v_{m,k}(y) − χ_k(y)| ≤ ∫⁻ ofReal(ρ_m(h))·ofReal|χ_k(y − h) − χ_k(y)| dh.
 (ii) The function (y, h) ↦ ofReal(ρ_m(h))·ofReal|χ_k(y − h) − χ_k(y)| is measurable on ℝ^N × ℝ^N. By (i) and Tonelli, ∫⁻_{B_R} ofReal|v_{m,k} − χ_k| ≤ ∫⁻ ofReal(ρ_m(h)) (∫⁻_{y ∈ B_R} ofReal|χ_k(y − h) − χ_k(y)| dy) dh.
 (iii) Since |χ_k(y − h) − χ_k(y)| = 1_{(F_k)_{−h} Δ F_k}(y), the inner integral equals L^N(B_R ∩ ((F_k)_{−h} Δ F_k)). If ρ_m(h) ≠ 0, then |−h| = |h| ≤ σ_m ≤ 1, so the inner integral is ≤ ofReal(C'|h|) ≤ ofReal(C'σ_m). Hence the outer integrand is ≤ ofReal(ρ_m(h))·ofReal(C'σ_m) for every h; this is trivial when ρ_m(h) = 0.
 (iv) Since ρ_m ≥ 0 is integrable, ∫⁻ ofReal(ρ_m) = ofReal(∫ρ_m) = 1. So the left side is ≤ ofReal(σ_m C').

3. (Cauchy estimate.) Fix R ∈ ℕ and ε ∈ (0, ∞]. If ε = ∞, any k₀ works. Otherwise put e := ε.toReal > 0, so that ofReal(e) = ε.
 (a) The translation hypothesis at R gives C ∈ ℝ and k₁. Put C' := max(C, 0) ≥ 0. Since C|h| ≤ C'|h|, the claim of step 2 applies to every k ≥ k₁ and every m.
 (b) Choose m ∈ ℕ with m ≥ R and C'σ_m ≤ e/4; this is possible because σ_m → 0.
 (c) Let V := L^N(B_R) < ∞ and η := e/(2(V.toReal + 1)) > 0. The uniform-Cauchy hypothesis at (m, η) gives k₂. Put k₀ := max(k₁, k₂).
 (d) Let k, l ≥ k₀. If y ∈ B_R, then |y| < R ≤ m, so y ∈ B̄_m(0) and |v_{m,k}(y) − v_{m,l}(y)| ≤ η. Since |χ_k − χ_l| = 1_{F_k Δ F_l}, the triangle inequality gives, for y ∈ B_R,
 1_{F_k Δ F_l}(y) ≤ |v_{m,k}(y) − χ_k(y)| + η + |v_{m,l}(y) − χ_l(y)|.
 (e) All three summands are measurable (step 1), so ∫⁻ over B_R is additive on them. Integrate over B_R, use step 2 for k and for l, and use ∫⁻_{B_R} ofReal(η) = ofReal(η)·V ≤ ofReal(e/2). This gives
 L^N(B_R ∩ (F_k Δ F_l)) = ∫⁻_{B_R} 1_{F_k Δ F_l} ≤ ofReal(e/4) + ofReal(e/2) + ofReal(e/4) = ofReal(e) = ε. ∎

## Key steps

1. WLOG every F_k is measurable; each v_{m,k}(y) = ∫_{F_k} ρ_m(y − z) dz is continuous by dominated convergence.
2. Mollification error: v_{m,k} − χ_k = ∫ ρ_m(h)(χ_k(·−h) − χ_k) dh. Tonelli and the translation estimate at −h (|h| ≤ σ_m ≤ 1) give ∫⁻_{B_R}|v_{m,k} − χ_k| ≤ σ_m·max(C, 0).
3. Given R and ε = ofReal(e): choose m ≥ R with σ_m C' ≤ e/4, put η := e/(2(L^N(B_R) + 1)), and take k₀ from both hypotheses.
4. On B_R ⊆ B̄_m(0), pointwise 1_{F_k Δ F_l} ≤ |v_{m,k} − χ_k| + η + |v_{m,l} − χ_l|. Integrating gives L^N(B_R ∩ (F_k Δ F_l)) ≤ ε.

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
