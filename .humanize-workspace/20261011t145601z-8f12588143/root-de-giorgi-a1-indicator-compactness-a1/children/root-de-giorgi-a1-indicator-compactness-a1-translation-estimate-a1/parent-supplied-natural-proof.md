# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This combines two parts of the parent proof:
- Step 1: apply the hypothesis to ±g and normalize.
- Step 2: the translation estimate, via translation invariance, the identity ψ(z − h) − ψ(z) = −∫_0^1 div Ψ_t(z) dt with Ψ_t(z) = ψ(z − th)h, and Fubini.
The final L¹-duality step of Step 2 is the sibling l1_duality (indCompact_ball_integral_abs_le_of_test_bound).

Notation.
- χ := 1_F.
- For h ∈ ℝ^N, F_h := {y : y + h ∈ F}. So 1_{F_h}(y) = χ(y + h) and |χ(y + h) − χ(y)| = 1_{F_h Δ F}(y).
- div G := trace(DG) = euclideanDivergence G.
- A vector field G is admissible if it is C¹, has compact support, satisfies tsupport G ⊆ B_{R+1}(0), and has |G| ≤ 1 everywhere.

1. (WLOG F measurable.) Choose a measurable F' with F' = F L^N-a.e., e.g. F' = toMeasurable F.
- The restricted measures L^N⌞F and L^N⌞F' coincide (Measure.restrict_congr_set). So ∫_F f = ∫_{F'} f for all f, and the hypothesis holds for F'.
- The map y ↦ y + h preserves L^N, so F'_h = F_h a.e. Hence B_R(0) ∩ (F'_h Δ F') = B_R(0) ∩ (F_h Δ F) a.e., and the left side of the claim is unchanged.
So assume F is measurable.

2. (Consequences of the hypothesis.) Note that div G is continuous with compact support, hence integrable, whenever G is C¹ with compact support.
 (a) G = 0 is admissible and div 0 = 0, so 0 ≤ C.
 (b) If G is admissible, so is −G, and div(−G) = −div G. Hence −∫_F div G ≤ C, i.e. |∫_F div G| ≤ C for every admissible G.
 (c) Let G be C¹ with compact support, tsupport G ⊆ B_{R+1}(0), and |G| ≤ λ for some λ > 0. Then G/λ is admissible and div(G/λ) = (div G)/λ, so |∫_F div G| ≤ λC.

3. (Trivial cases.) If R ≤ 0, then B_R(0) = ∅ and the left side is 0. If h = 0, then F_h = F, so F_h Δ F = ∅ and the left side is 0. Assume from now on R > 0 and 0 < |h| ≤ 1.

4. (Reduction to test functions.) Let w(y) := χ(y + h) − χ(y).
- w is measurable and |w| ≤ 1, so w is integrable on the bounded ball B_R(0).
- |w| = 1_{F_h Δ F}, so ∫_{B_R(0)} |w| = L^N(B_R(0) ∩ (F_h Δ F)) < ∞. That is, L^N(B_R(0) ∩ (F_h Δ F)) = ofReal(∫_{B_R(0)} |w|).
By the sibling l1_duality, applied to w, R and M := C|h|, it therefore suffices to prove ∫ w ψ ≤ C|h| for every C¹ function ψ : ℝ^N → ℝ with compact support, tsupport ψ ⊆ B_R(0) and |ψ| ≤ 1.

5. (Test-function bound.) Fix such a ψ.
 (a) (Translation invariance.) Substituting z = y + h gives ∫ χ(y + h)ψ(y) dy = ∫ χ(z)ψ(z − h) dz. This uses translation invariance of Lebesgue measure; all integrands are bounded with compact support. Hence ∫ w ψ = ∫_F (ψ(z − h) − ψ(z)) dz.
 (b) (Fundamental theorem of calculus.) For fixed z, the map t ↦ ψ(z − th) is C¹ on ℝ with derivative −Dψ(z − th)[h]. Hence ψ(z − h) − ψ(z) = −∫_0^1 Dψ(z − th)[h] dt.
 (c) (Divergence form.) For t ∈ [0, 1] let Ψ_t(z) := ψ(z − th)·h.
 - Ψ_t is C¹ with DΨ_t(z)[v] = Dψ(z − th)[v]·h, i.e. DΨ_t(z) = (Dψ(z − th)).smulRight h.
 - Hence div Ψ_t(z) = trace(v ↦ Dψ(z − th)[v]·h) = Dψ(z − th)[h], because the trace of the rank-one map ℓ(·)h is ℓ(h) (Mathlib LinearMap.trace_smulRight).
 - |Ψ_t| ≤ |h|, and tsupport Ψ_t = tsupport ψ + th is compact.
 - tsupport ψ is a compact subset of the open ball B_R(0), so there is R' < R with tsupport ψ ⊆ B̄_{R'}(0). For example, take R' to be the maximum of |·| on tsupport ψ, or R' = 0 if tsupport ψ = ∅. Since t|h| ≤ 1, tsupport Ψ_t ⊆ B̄_{R'+1}(0) ⊆ B_{R+1}(0).
 By step 2(c) with λ = |h|, |∫_F div Ψ_t| ≤ C|h| for every t ∈ [0, 1].
 (d) (Fubini.) Consider the function (z, t) ↦ 1_F(z)·Dψ(z − th)[h] on ℝ^N × [0, 1].
 - It is measurable, since Dψ is continuous.
 - It is bounded by (sup |Dψ|)·|h| < ∞, since Dψ is continuous with compact support.
 - It vanishes unless z ∈ B̄_{R+1}(0).
 Hence it is integrable for L^N ⊗ (L^1 restricted to [0, 1]), and ∫_F ∫_0^1 Dψ(z − th)[h] dt dz = ∫_0^1 ∫_F Dψ(z − th)[h] dz dt.
 (e) Combining (a)–(d): ∫ w ψ = −∫_0^1 (∫_F div Ψ_t(z) dz) dt ≤ ∫_0^1 |∫_F div Ψ_t| dt ≤ C|h|.

6. (Conclusion.) By step 5, the hypothesis of the sibling l1_duality holds for w with M = C|h|. Hence ∫_{B_R(0)} |w| ≤ C|h|. By step 4, L^N(B_R(0) ∩ (F_h Δ F)) = ofReal(∫_{B_R(0)} |w|) ≤ ofReal(C|h|). ∎

## Key steps

1. WLOG F measurable. Testing with g = 0 and ±G/λ shows C ≥ 0 and |∫_F div G| ≤ λC for every C¹_c field G in B_{R+1}(0) with |G| ≤ λ.
2. Trivial cases R ≤ 0 or h = 0. The function w := 1_F(·+h) − 1_F satisfies ∫_{B_R}|w| = L^N(B_R ∩ (F_h Δ F)).
3. For admissible ψ: ∫ w ψ = ∫_F (ψ(z−h) − ψ(z)) dz = −∫_0^1 ∫_F div(ψ(·−th)h) dz dt, by translation invariance, the FTC, the trace of a rank-one map, and Fubini.
4. tsupport ψ(·−th)h ⊆ B̄_{R'+1}(0) ⊆ B_{R+1}(0) and |ψ(·−th)h| ≤ |h|, so ∫ w ψ ≤ C|h|.
5. The sibling l1_duality gives ∫_{B_R}|w| ≤ C|h|, i.e. L^N(B_R ∩ (F_h Δ F)) ≤ ofReal(C|h|).

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
