# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.cauchy_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent-supplied proof (Simon Ch. 6, proof of Theorem 7.2: 'apply (1) with ε = 1, 1/2, 1/4 etc. to extract a subsequence {T_{j_r}} with d(T_{j_{r+1}}, T_{j_r}) < 2^{−r}', chapter-06.txt lines 2103–2117). Tool: the sibling (IMC) the reused accepted sibling cmc_imRep_locality_restrict_sub: (a) if U is open, M ⊆ M' ⊆ U are Borel and Hᵈ(M' ∩ K) < ∞ for every compact K ⊆ U, then for Hᵈ-a.e. x ∈ M and every linear subspace Q, M has approximate tangent space Q at x iff M' has (HasApproximateTangentSpaceAt d · x Q); (b) if U is open, R = (M, θ, ξ) is an IMRep in U and E is Borel, there are A ∈ 𝒟_d(U) and an IMRep R' in U with carrier M ∩ E, multiplicity θ and orientation ξ that represents A (so μ_{R'} = μ_R⌞E); (c) if U is open and A, B ∈ 𝒟_d(U) are IM, then A − B is IM; (d) for every IMRep R = (M, θ, ξ) in any U and Hᵈ-a.e. x ∈ M, |ξ(x)(α)| ≤ |α| for every d-covector α.
1. Mass of a difference. For A, B ∈ 𝒟_d(U), M(A − B) ≤ M(A) + M(B): if ω is admissible for M_U then so is −ω, and (A − B)(ω) = A(ω) + B(−ω) ≤ M(A) + M(B).
2. Choices. For r ∈ ℕ let ε_r := 2^{−r−1} > 0 and let 𝒬_r be a finite set given by the hypothesis for ε_r. For every r and j choose Q_r(j) ∈ 𝒬_r and IM R_r(j) ∈ 𝒟_{n+1}(U), S_r(j) ∈ 𝒟_n(U) with X_j − Q_r(j) = ∂R_r(j) + S_r(j) on 𝒟ⁿ(U) and M(R_r(j)) + M(S_r(j)) < ε_r.
3. Nested infinite index sets (pigeonhole). Put J_{−1} := ℕ. If J_{r−1} ⊆ ℕ is infinite, the map j ↦ Q_r(j) on J_{r−1} takes values in the finite set 𝒬_r, so some value q_r has an infinite fibre (Finite.exists_infinite_fiber); let J_r := {j ∈ J_{r−1} : Q_r(j) = q_r}. This gives infinite sets J_0 ⊇ J_1 ⊇ J_2 ⊇ ⋯ with Q_r(j) = q_r for all j ∈ J_r.
4. Diagonal choice. Choose θ(0) ∈ J_0 and, inductively, θ(r + 1) ∈ J_{r+1} with θ(r + 1) > θ(r) (possible since J_{r+1} is infinite). Then θ is strictly increasing and θ(r), θ(r + 1) ∈ J_r for every r (as J_{r+1} ⊆ J_r).
5. Differences. Fix r, put j := θ(r), j' := θ(r + 1), so Q_r(j) = Q_r(j') = q_r. Let R_r := R_r(j') − R_r(j) and S_r := S_r(j') − S_r(j) (contract subtraction); both are IM by (IMC)(c). For ω ∈ 𝒟ⁿ(U), using ∂(A − B)(ω) = A(dω) − B(dω): X_{j'}(ω) − X_j(ω) = (q_r(ω) + R_r(j')(dω) + S_r(j')(ω)) − (q_r(ω) + R_r(j)(dω) + S_r(j)(ω)) = ∂R_r(ω) + S_r(ω). By step 1, M(R_r) + M(S_r) ≤ M(R_r(j')) + M(S_r(j')) + M(R_r(j)) + M(S_r(j)) < 2ε_r = 2^{−r}. ∎

## Key steps

1. Mass of a difference is at most the sum of the masses (−ω is admissible whenever ω is).
2. For ε_r = 2^{−r−1} pick the finite net 𝒬_r and a decomposition X_j − Q_r(j) = ∂R + S for every j.
3. Pigeonhole gives nested infinite index sets J_r on which Q_r(j) is a fixed q_r; choose θ(r) ∈ J_r increasing.
4. Subtracting the two decompositions of X_{θ(r+1)} and X_{θ(r)} with the same q_r gives IM R_r, S_r ((IMC)(c)) with mass < 2ε_r = 2^{−r}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n "^theorem" local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean (LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt)`
- `rg -n "theorem lipschitz_infDist_pt|theorem infDist_le_dist_of_mem" local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -l -i "retraction|skeleton|cubical|radial retract|latticeFace|deformation theorem" .lake/packages/simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project -g "*.lean" (only GMT/Ch06 Contract/Submission; SimonGMT hits are unrelated: "cubically small" remainders in Chapter05, a local chart retraction in Chapter08/ConstancyNormalCharts.lean, a unit-ball retraction in Chapter08/PolarNorm.lean)`
- `rg -n -i "latticeFace|DeformationTheorem|def IsLatticeChain" local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean (sorry-frozen Ch06 statements, not imported by GMT.Ch07.Submission)`
- `sed -n 1400,1935p book/chapter-06.txt (Deformation Theorem 5.1-5.3, Lemma 5.4 with the printed induction for (3), proof (1)-(38))`
- `python3 -I scans of dag.json (818 nodes, updated 2026-10-13T09:07Z): statuses and byte-identical frozen types of dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, dor_ims_unitOrientation_dual (accepted); dor_lmb_slicing_lipschitz (decomposing; frozen type equals the (SL) antecedent of localize/total_bounded/deformation/deformation_top); no collision for the seven dor_lmb_fc_* names; child dependency graph acyclic`
- `python3 -I parse of nodes/.../decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json (only deformation step 1 rejected)`
- `python3 -I /tmp/fc-decomp-v2/scripts/check_retraction.py 1 and 7; python3 -I /tmp/fc-decomp-v2/scripts/check_global2.py 3 and 11 (numerical checks of Claims A, B, C and the global Lipschitz bound; audit counterexample ratio 62/69)`
- `python3 -I /tmp/fc-decomp-v2/gen_types.py (gmt-compare.py contract_scope replay; exact comparator challenge file per child) and lean_contract.validate_lean_statement on all ten lean_statement strings`
- `lake env lean /tmp/fc-decomp-v2/lean/Challenge_*.lean and AllProps.lean (0 errors; #check of the cited Mathlib lemmas)`
- `python3 -I /tmp/fc-decomp-v2/check_assembly_types.py; lake env lean /tmp/fc-decomp-v2/lean/Assembly.lean and Slim.lean (#print axioms: [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/PolarNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/ScalarAreaRemainder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/fc-decomp-v2/lean/AllProps.lean`
- `/tmp/fc-decomp-v2/lean/Assembly.lean`
- `/tmp/fc-decomp-v2/lean/Slim.lean`
- `/tmp/fc-decomp-v2/scripts/check_retraction.py`
- `/tmp/fc-decomp-v2/scripts/check_global2.py`

Snapshot: project b4d606db and mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
Neither SimonGMT nor the snapshot contains a cubical-skeleton retraction, Lemma 5.4, or a proved Deformation Theorem. The skeleton/retraction keyword hits are unrelated (Chapter05 "cubically small" remainders, a local chart retraction in Chapter08/ConstancyNormalCharts.lean, a unit-ball retraction in Chapter08/PolarNorm.lean). The Ch06 contract has only sorry-frozen latticeFace/DeformationTheorem statements, not imported by GMT.Ch07.Submission. So the corrected Lemma 5.4 argument is written out in deformation step 1 and cites only Mathlib basics present in the snapshot: Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt) and lipschitz_infDist_pt.
DAG state: the reused declarations dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub and dor_ims_unitOrientation_dual are accepted with byte-identical frozen types. dor_lmb_slicing_lipschitz is still decomposing, and its frozen type equals the (SL) antecedent. The seven dor_lmb_fc_* names are fresh.
Lean: all ten child types compile as exact comparator challenges in the replayed contract scope with 0 errors. The conditional assembly of the exact parent type and the derivation of series_limit from im_series compile with only propext, Classical.choice and Quot.sound.
