# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.finite_mass_approximation-a1`
- Child DAG node: `root.polyhedral_approximation-a1.finite_mass_approximation-a1.scale_sequence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (Scales) of the parent proof, which chooses the scales ρ_k ↓ 0 of Simon 6.2 according to the masses. The parent applies this with a_k = (M(X_k) + M(∂X_k)).toReal ≥ 0. Here a_k is arbitrary, so 1 + a_k is replaced by b_k := 1 + |a_k|; this equals 1 + a_k when a_k ≥ 0, giving exactly the parent's construction.

1. Put b_k := 1 + |a_k|. Then b_k ≥ 1 > 0 for every k.
2. Define ρ recursively: ρ_0 := 1/b_0 and ρ_{j+1} := min{ρ_j, 1/((j+2)·b_{j+1})} for j ∈ ℕ. (In Lean, use Nat.rec; both defining equations then hold by rfl.)
3. (Positivity.) By induction on k.
   - ρ_0 = 1/b_0 > 0.
   - If ρ_j > 0, then ρ_{j+1} is the minimum of ρ_j > 0 and 1/((j+2)·b_{j+1}) > 0, hence positive (lt_min).
4. (Antitone.) ρ_{j+1} ≤ ρ_j for every j (min_le_left), so ρ is antitone (antitone_nat_of_succ_le).
5. (Upper bound.) For every k, ρ_k ≤ 1/((k+1)·b_k).
   - For k = 0: ρ_0 = 1/b_0 = 1/((0+1)·b_0).
   - For k = j+1: ρ_{j+1} ≤ 1/((j+2)·b_{j+1}) (min_le_right). Moreover (j+1)+1 = j+2; for the casts ℕ → ℝ, ((j+1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 (push_cast, ring).
6. (Limit.)
   - Since b_k ≥ 1, (k+1)·b_k ≥ k+1 > 0. So step 5 gives ρ_k ≤ 1/((k+1)·b_k) ≤ 1/(k+1) (one_div_le_one_div_of_le).
   - Thus 0 < ρ_k ≤ 1/(k+1) for all k, and 1/(k+1) → 0 (tendsto_one_div_add_atTop_nhds_zero_nat). By the squeeze theorem (squeeze_zero), ρ_k → 0.
7. (Product bound.) Fix k.
   - Since ρ_k > 0 and a_k ≤ |a_k|: ρ_k·a_k ≤ ρ_k·|a_k|.
   - By step 5 and |a_k| ≥ 0: ρ_k·|a_k| ≤ |a_k|/((k+1)·b_k).
   - Since 0 ≤ |a_k| ≤ 1 + |a_k| = b_k and (k+1)·b_k > 0: |a_k|/((k+1)·b_k) ≤ b_k/((k+1)·b_k) = 1/(k+1).
   - Hence ρ_k·a_k ≤ 1/(k+1).
Steps 3, 4, 6 and 7 give the four required properties. ∎

## Key steps

1. b_k = 1 + |a_k| ≥ 1; ρ_0 = 1/b_0 and ρ_{j+1} = min(ρ_j, 1/((j+2)b_{j+1})).
2. ρ_k > 0 by induction; ρ is antitone because ρ_{j+1} ≤ ρ_j.
3. ρ_k ≤ 1/((k+1)b_k) ≤ 1/(k+1), so ρ_k → 0 by squeezing.
4. ρ_k a_k ≤ ρ_k|a_k| ≤ |a_k|/((k+1)b_k) ≤ 1/(k+1).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def DeformationTheorem|^def IsLatticeChain|^abbrev LatticeFaceIndex' project/GMT/Ch06/Contract.lean`
- `rg -n 'polyhedral_approx_testForm_covectorNorm_bounded|polyhedral_approx_scale_seq|polyhedral_approx_flat_seq_tendsto|br_la_abs_apply_le_mul_mass' project (no match)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean at frozen d8d46c9 and against snapshot project/GMT/Ch06/Submission.lean (byte-identical)`
- `rg -n 'theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem antitone_nat_of_succ_le' mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean mathlib/Mathlib/Order/Monotone/Basic.lean`
- `rg -n 'theorem tendsto_toReal |protected theorem Tendsto.const_mul|theorem tendsto_ofReal ' mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `rg -n 'instance instContinuousEvalConst' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -n 'bounded_above_of_compact_support|squeeze_zero_norm' mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean; rg -n 'theorem mono'' mathlib/Mathlib/Topology/Algebra/Support.lean`
- `rg -n 'theorem mul_le_mul_right ' mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean (mul_le_mul_left' no longer exists at this pin)`
- `grep -n 'def covectorEuclideanNorm|covectorEuclideanNorm_zero|covectorEuclideanNorm_neg|def massAdmissibleOn|massOn|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'def exteriorDerivativeTestOn|boundary_apply|abbrev TestFormOn|structure GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `python3 scan of dag.json: br_la_abs_apply_le_mul_mass has an identical lean_statement, status accepted, candidate d771ac3; br_la_testForm_covectorNorm_bounded is status comparing (not shareable); the three new names are absent; grep -rl over the run directory and git refs (no match)`
- `git show d771ac3 -- GMT/Ch06/Submission.lean (accepted mass-estimate proof)`
- `sed -n 6532,6570p /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py (_existing_lean_name_problem: an accepted node may be shared under an identical frozen type)`
- `sed -n 1960,1992p book/chapter-06.txt (printed 6.2 proof)`
- `python3 contract_scope(Contract.lean, GMT.Ch06.main_theorem) from verifier/gmt-compare.py`
- `lake build GMT.Ch06.Submission (scratch /tmp/fms_decomp_check_ch06, frozen d8d46c9, pinned packages); lake env lean Scratch/Stmts.lean; lake env lean Scratch/Children.lean; lake env lean Scratch/NodeSolutions.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-finite-mass-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/tmp/fms_decomp_check_ch06/Scratch/Stmts.lean`
- `/tmp/fms_decomp_check_ch06/Scratch/Children.lean`
- `/tmp/fms_decomp_check_ch06/Scratch/NodeSolutions.lean`

The snapshot pins project d8d46c95 and Mathlib 25730c7c. Its Contract and Submission for Ch06 are byte-identical to the frozen workspace copies and contain no Submission.* declarations. None of the proposed names occurs in the snapshot project (no match).

The contract supplies DeformationTheorem, IsLatticeChain, LatticeFaceIndex and IsIntegerMultiplicity. SimonGMT supplies GeometricCurrentOn, mass/massOn/massAdmissibleOn/le_massOn, covectorEuclideanNorm (with _zero and _neg), TestFormOn, exteriorDerivativeTestOn and GeometricCurrentOn.boundary_apply.

The pinned Mathlib provides every tool the child proofs cite: continuous_eval_const (ContinuousAlternatingMap.instContinuousEvalConst), Continuous.bounded_above_of_compact_support, HasCompactSupport.mono', squeeze_zero, squeeze_zero_norm', tendsto_one_div_add_atTop_nhds_zero_nat, antitone_nat_of_succ_le, eventually_ne_nhds, ENNReal.tendsto_toReal, ENNReal.tendsto_ofReal and ENNReal.Tendsto.const_mul. At this pin the monotonicity lemma is named mul_le_mul_right, because mul_le_mul_left' is gone.

The mass estimate already exists as the accepted DAG declaration br_la_abs_apply_le_mul_mass (candidate d771ac3) with a byte-identical frozen type, so it is reused. The test-form bound exists only as the unaccepted br_la_testForm_covectorNorm_bounded, so it gets a fresh name.

In a scratch build of the frozen project:
- All four child types and the selected parent type elaborate in the comparator child scope.
- Full proofs of testform_bounded, scale_sequence and flat_convergence compile, as does the complete assembly of the selected theorem from scale_sequence, flat_convergence and the DeformationTheorem hypothesis.
- The NodeSolution-style 'exact Submission.X' check passes for every child and the parent.
- #print axioms reports only propext, Classical.choice and Quot.sound.
