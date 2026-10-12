# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1`
- Child DAG node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1.uniform_limit_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1-2 of the parent proof (the estimate and the limit criterion), stated for arbitrary F_k, G and K.
Hypotheses:
- μ is a measure on ℝ^N = Euclidean N (Borel σ-algebra) with μ(C) < ∞ for every compact C (IsFiniteMeasureOnCompacts μ).
- K ⊆ ℝ^N is compact.
- G and every F_k (k ∈ ℕ) are μ-integrable real functions.
- (V) F_k(y) = G(y) for every k and every y ∉ K.
- (U) For every ε > 0 there is k₀ ∈ ℕ with |F_k(y) − G(y)| ≤ ε for all k ≥ k₀ and all y.
We prove ∫ F_k dμ → ∫ G dμ as k → ∞.
1. (Finite mass of K.) K is compact and μ is finite on compact sets, so μ(K) < ∞ (IsCompact.measure_lt_top). Let c := μ.real K = (μ K).toReal be μ(K) read as a real number. Then c ≥ 0, so c + 1 > 0.
2. (Estimate.) Let h : ℝ^N → ℝ and η ∈ ℝ satisfy h(y) = 0 for every y ∉ K and |h(y)| ≤ η for every y ∈ K. Then |∫ h dμ| ≤ η·c.
 Indeed, h vanishes off K, so ∫ h dμ = ∫_K h dμ (setIntegral_eq_integral_of_forall_compl_eq_zero, which needs no measurability of K). Since μ(K) < ∞ and |h| ≤ η on K, |∫_K h dμ| ≤ η·μ.real K = η·c (norm_setIntegral_le_of_norm_le_const).
3. (Choice of k₀.) Let ε > 0 and put η := ε/(c + 1) > 0. By (U) choose k₀ with |F_k(y) − G(y)| ≤ η for all k ≥ k₀ and all y.
4. (Bound for k ≥ k₀.) Fix k ≥ k₀ and set h := F_k − G.
 By (V), h(y) = G(y) − G(y) = 0 for every y ∉ K. By step 3, |h(y)| ≤ η for every y.
 F_k and G are integrable, so ∫ h dμ = ∫ F_k dμ − ∫ G dμ (integral_sub).
 Step 2 then gives |∫ F_k dμ − ∫ G dμ| = |∫ h dμ| ≤ η·c = ε·c/(c + 1). This is < ε, because ε > 0 and c < c + 1 give ε·c < ε·(c + 1).
5. (Conclusion.) For every ε > 0 we found k₀ with dist(∫ F_k dμ, ∫ G dμ) = |∫ F_k dμ − ∫ G dμ| < ε for all k ≥ k₀. This is exactly ∫ F_k dμ → ∫ G dμ in ℝ along atTop (Metric.tendsto_atTop). ∎

## Key steps

1. μ(K) < ∞ because K is compact and μ is finite on compacts; c := μ.real K ≥ 0.
2. If h = 0 off K and |h| ≤ η on K, then ∫ h dμ = ∫_K h dμ and |∫_K h dμ| ≤ η·c (setIntegral_eq_integral_of_forall_compl_eq_zero, norm_setIntegral_le_of_norm_le_const).
3. Given ε > 0, take η = ε/(c+1) and k₀ from the uniform hypothesis.
4. For k ≥ k₀, h = F_k − G vanishes off K and |h| ≤ η, so |∫F_k − ∫G| = |∫(F_k − G)| ≤ εc/(c+1) < ε (integral_sub).
5. Hence ∫ F_k dμ → ∫ G dμ (Metric.tendsto_atTop).

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in snapshot mathlib and .lake/packages/mathlib (both 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n 'theorem dist_normed_convolution_le|contDiff_normed|support_normed_eq|hasCompactSupport_normed|nonneg_normed|integral_normed' snapshot mathlib/Mathlib/Analysis/Calculus/BumpFunction/*.lean (Convolution.lean:71; Normed.lean:37,40,68,72,79); grep -n '^structure ContDiffBump' BumpFunction/Basic.lean (:70)`
- `grep -n 'HasCompactSupport.contDiff_convolution_left' Analysis/Calculus/ContDiff/Convolution.lean (:427, {n : ℕ∞}); grep -n 'theorem support_convolution_subset' Analysis/Convolution.lean (:670)`
- `grep -n 'setIntegral_eq_integral_of_forall_compl_eq_zero|norm_setIntegral_le_of_norm_le_const' MeasureTheory/Integral/Bochner/Set.lean (:486 no measurability, :613 needs only μ s < ∞); rg 'theorem integral_sub' Bochner/Basic.lean (:263); rg 'IsCompact.measure_lt_top' Measure/Typeclasses/Finite.lean (:346); rg 'theorem tendsto_atTop|theorem uniformContinuous_iff' Topology/MetricSpace/Pseudo/Defs.lean (:908, :755)`
- `rg 'uniformContinuous_of_continuous' Topology/UniformSpace/HeineCantor.lean (:91); 'Continuous.integrable_of_hasCompactSupport' MeasureTheory/Function/LocallyIntegrable.lean (:622); 'HasCompactSupport.comp_smul|IsCompact.smul' Topology/Algebra/ConstMulAction.lean (:466, :142); 'mem_smul_set_iff_inv_smul_mem₀' Algebra/GroupWithZero/Action/Pointwise/Set.lean (:130); 'IsCompact.mul' Topology/Algebra/Monoid.lean (:671, to_additive IsCompact.add); 'theorem intro' Topology/Algebra/Support.lean (:232); 'exists_nat_one_div_lt' Algebra/Order/Archimedean/Basic.lean (:211); 'tendsto_nhds_unique' Topology/Separation/Hausdorff.lean (:180)`
- `grep -rn TendstoUniformly MeasureTheory | grep -i integral (only interval/circle versions: DominatedConvergence.lean:182, CircleIntegral.lean:448); rg 'theorem .*(exists_contDiff|exists_smooth).*(approx|dense|tendsto)' Mathlib (Continuous.exists_contDiff_approx, Geometry/Manifold/SmoothApprox.lean:132)`
- `rg -n 'ContDiffBump|convolution|mollif|uniformContinuous_of_continuous|tendsto_integral' snapshot project/ (no match); rg -ln 'ContDiffBump|dist_normed_convolution_le|contDiff_convolution_left|mollif' .lake/packages/simongmt/Poincare (only Chapter08/DistributionalConstancy.lean constancyMollifier, Chapter08/ConstancyTangentTests.lean, Chapter02/BV.lean, Chapter02/WhitneyPartition.lean; no general C_c uniform-approximation or uniform-limit-integral lemma)`
- `#check @ContDiffBump.contDiff_normed and @ContDiffBump.dist_normed_convolution_le after import GMT.Ch08.Submission in the contract scope (Unknown constant: bump-function modules are outside the Submission import closure)`
- `python3 -I verifier/gmt-compare.py child_modules + contract_scope (scope: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section/end Definitions) and verifier/lean_contract.validate_lean_statement on both child statements and the parent frozen type (all unchanged)`
- `lake env lean /tmp/dmc-decomp/Final.lean (children and parent fully proved; HumanizeNodeComparator.targetN := by exact Submission.X replays; #print axioms = [propext, Classical.choice, Quot.sound])`
- `lake env lean /tmp/dmc-decomp/Stub.lean (import GMT.Ch08.Submission only; children sorry; parent glue compiles with no sorry of its own)`
- `lake env lean on the three generated <lean_name>_NodeChallenge.lean files (only 'declaration uses sorry') and /tmp/dmc-decomp/SubmissionTest.lean (full Submission.lean + import Mathlib.Analysis.Calculus.BumpFunction.Convolution + three theorems: compiles)`
- `python3 -I json scan of dag.json lean_name and lean_statement (193 nodes; no varifold_tangents_rh_mc_* reservation; no identical or analogous statement; radon_compactlySupported_countable_approx is a different statement)`
- `independent reviewer subagent replay in /tmp/dmc-review (verdict ACCEPT, no blocking findings)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Monoid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-dilation-mollify-cc-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1/decomposition-v1.json`

The snapshot is project 63436ae6 plus Mathlib 25730c7c, the same Mathlib revision as .lake/packages/mathlib. The snapshot's Contract.lean is byte-identical to the workspace's Contract.lean and Submission.lean.

Mathlib supplies every tool the split needs:
- Child A: setIntegral_eq_integral_of_forall_compl_eq_zero (Set.lean:486, no measurability), norm_setIntegral_le_of_norm_le_const (Set.lean:613, needs only μ K < ∞), integral_sub, IsCompact.measure_lt_top and Metric.tendsto_atTop.
- Child B: the ContDiffBump normed API (Normed.lean:37-79), dist_normed_convolution_le (BumpFunction/Convolution.lean:71), HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean:427), support_convolution_subset (Convolution.lean:670), HasCompactSupport.uniformContinuous_of_continuous, IsCompact.add and exists_nat_one_div_lt.
- Parent glue: Continuous.integrable_of_hasCompactSupport, HasCompactSupport.comp_smul, IsCompact.smul, mem_smul_set_iff_inv_smul_mem₀, HasCompactSupport.intro and tendsto_nhds_unique.

The bump-function modules are not in GMT.Ch08.Submission's import closure: #check reports Unknown constant. So child B's proof must add import Mathlib.Analysis.Calculus.BumpFunction.Convolution. This was checked to compile with the whole Submission file.

No library has either child as a direct lemma:
- Mathlib's uniform-limit integral results cover only interval and circle integrals.
- Continuous.exists_contDiff_approx (SmoothApprox.lean:132) is a possible alternative route for child B, but it is also outside the closure and is not needed.
- The project has no match.
- SimonGMT only has the constancy-specific constancyMollifier.

Lean checks, in the comparator's replayed scope:
- Both child statements and the parent frozen type elaborate with import GMT.Ch08.Submission alone and validate unchanged.
- The parent glue compiles against sorry'd children.
- Both children and the parent were fully proved, with only standard axioms.

Neither child name is reserved in dag.json.
