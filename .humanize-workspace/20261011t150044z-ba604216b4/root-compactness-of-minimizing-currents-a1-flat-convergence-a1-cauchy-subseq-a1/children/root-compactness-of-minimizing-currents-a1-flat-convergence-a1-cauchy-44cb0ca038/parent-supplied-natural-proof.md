# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.close_pair-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (close pairs) of the parent-supplied proof of cmc_fc_cauchy_subseq (Simon Ch. 6, proof of 7.2). The mass bound is kept as the sum of the two given masses.
1. Put R := R₁ − R₂ ∈ 𝒟_{m+2}(U) and S := S₁ − S₂ ∈ 𝒟_{m+1}(U) (contract Sub instance). U is open and R₁, R₂ are integer multiplicity, so (IS) with n = m + 2 shows that R is integer multiplicity. Likewise S₁, S₂ are integer multiplicity, so (IS) with n = m + 1 shows that S is integer multiplicity.
2. (Pointwise hypotheses.) Fix ω ∈ 𝒟^{m+1}(U) (TestFormOn U (m + 1)) and write dω := exteriorDerivativeTestOn U (m + 1) ω ∈ 𝒟^{m+2}(U). Then T.boundary(ω) = T(dω) for every T ∈ 𝒟_{m+2}(U), definitionally (GeometricCurrentOn.boundary_apply). Also (A − B)(ω) = A(ω) − B(ω) definitionally for the contract Sub instance. Evaluating the hypotheses Y − Q − S₁ = ∂R₁ and Z − Q − S₂ = ∂R₂ at ω (congrArg) therefore gives Y(ω) − Q(ω) − S₁(ω) = R₁(dω) and Z(ω) − Q(ω) − S₂(ω) = R₂(dω).
3. (The identity.) For the same ω, (Y − Z − S)(ω) = Y(ω) − Z(ω) − (S₁(ω) − S₂(ω)), and ∂R(ω) = R(dω) = R₁(dω) − R₂(dω). Subtracting the two equalities of step 2 gives R₁(dω) − R₂(dω) = (Y(ω) − Q(ω) − S₁(ω)) − (Z(ω) − Q(ω) − S₂(ω)) = Y(ω) − Z(ω) − (S₁(ω) − S₂(ω)), since the Q(ω) terms cancel (linear arithmetic over ℝ). Hence (Y − Z − S)(ω) = ∂R(ω) for every ω, and Y − Z − S = ∂R by extensionality of currents (GeometricCurrentOn.ext).
4. (The mass bound.) Total mass is M(T) = T.mass = T.massOn U. Apply the sibling lemma cmc_fc_cs_massOn_sub_le (M_G(A − B) ≤ M_G(A) + M_G(B)) with G = U. This gives M(R) = M(R₁ − R₂) ≤ M(R₁) + M(R₂), with A = R₁, B = R₂ in degree m + 2, and M(S) = M(S₁ − S₂) ≤ M(S₁) + M(S₂), with A = S₁, B = S₂ in degree m + 1. Adding (add_le_add) gives M(R) + M(S) ≤ (M(R₁) + M(R₂)) + (M(S₁) + M(S₂)). The right side equals (M(R₁) + M(S₁)) + (M(R₂) + M(S₂)) by commutativity and associativity of addition in [0, ∞] (add_add_add_comm).
5. So R and S are integer multiplicity (step 1), Y − Z − S = ∂R (step 3) and M(R) + M(S) ≤ (M(R₁) + M(S₁)) + (M(R₂) + M(S₂)) (step 4), as claimed. ∎

## Key steps

1. Take R := R₁ − R₂ and S := S₁ − S₂; both are integer multiplicity by (IS), since U is open.
2. Evaluate both hypotheses at a test form ω, using (A − B)(ω) = A(ω) − B(ω) and ∂T(ω) = T(dω).
3. Subtract them: Q cancels, giving (Y − Z − S)(ω) = R(dω) = ∂R(ω); conclude by GeometricCurrentOn.ext.
4. Mass bound from cmc_fc_cs_massOn_sub_le with G = U for R and for S, then add_le_add and add_add_add_comm.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical; workspace HEAD b4d606db = manifest project_commit)`
- `rg -n "massOn_sub|mass_sub|massOn_add|sub_massOn|diagonal|exists_infinite_fiber|cmc_fc_cs_" local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n "theorem tsupport_neg|theorem ofReal_add_le|theorem inv_two_add_inv_two|theorem _root_.Set.Infinite.exists_gt|theorem strictMono_nat_of_lt_succ|protected theorem Finite.biUnion|theorem Finite.biUnion " local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "tsupport_inv|tsupport_neg|mulTSupport_inv" local-references/123e8435b4a2469b/mathlib/Mathlib; rg -n "theorem pow_pos" local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal`
- `rg -n "theorem Finite.exists_infinite_fiber|infinite_fiber|Infinite.exists_gt|Infinite.exists_ne_map_eq_of_mapsTo|theorem Finite.biUnion" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -n '^theorem \|^def \|^@\[simp\] theorem \|^@\[ext\]' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass}.lean (massAdmissibleOn, GeometricCurrentOn.massOn/mass/le_massOn, covectorEuclideanNorm_neg, GeometricCurrentOn.ext, GeometricCurrentOn.boundary_apply); sed -n 25,50p Chapter06/Forms.lean (DifferentialForm = E → Covector E n)`
- `python3 scan of dag.json: lean_name collisions for cmc_fc_cs_massOn_sub_le / cmc_fc_cs_close_of_common_center / cmc_fc_cs_diagonal_subseq (none); statements containing (X - Y).mass, massOn _ + _.massOn, Set.Infinite, StrictMono φ ∧ ∀ r, 2⁻¹ (only lcmp_massOn_le_add_of_eval_eq, decomposing, other parent, different type); frozen parent type string-equality check (True)`
- `sed -n 2755,2870p, 2000,2060p, 3159,3200p, 6500,6600p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (speculative stubs, sibling-dependency wait, accepted-child overlay, _dependency_problem, _existing_lean_name_problem)`
- `git show 44ef61f:GMT/Ch07/Submission.lean (placement of accepted child theorem Submission.dtc_vanish_off_support inside namespace GMT.Ch07)`
- `sed -n 2085,2125p book/chapter-06.txt (Simon Ch. 6, 7.2: 'apply (1) with ε = 1, 1/2, 1/4 etc. to extract a subsequence … d(T_{j_{r+1}}, T_{j_r}) < 2^{-r}')`
- `lake env lean /tmp/cauchy_dec/Types.lean (three child types + pp.explicit Sub instance); lake env lean /tmp/cauchy_dec/Assembly.lean (#print axioms cs_assembly); lake env lean /tmp/cauchy_dec/Children.lean (full child proofs); lake env lean /tmp/cauchy_dec/EndToEnd.lean (exact frozen parent from the three children, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Lattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Interval/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-subseq-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-subseq-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-subseq-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cauchy_dec/Types.lean`
- `/tmp/cauchy_dec/Assembly.lean`
- `/tmp/cauchy_dec/Children.lean`
- `/tmp/cauchy_dec/EndToEnd.lean`

The snapshot (project b4d606db, mathlib 25730c7c) has a Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot project nor SimonGMT Chapter06 has a mass-subadditivity lemma for differences (Mass.lean has only massOn_mono, le_massOn and massOn_le_liminf), a close-pair lemma or a diagonal-extraction lemma. Among DAG nodes, the only related statement is lcmp_massOn_le_add_of_eval_eq, which is unaccepted, under another parent and of a different type, so it cannot be reused and the three new names are globally unique. The pinned Mathlib supplies every tool the child proofs cite: tsupport_neg (to_additive of mulTSupport_inv), covectorEuclideanNorm_neg (SimonGMT), ENNReal.ofReal_add_le, GeometricCurrentOn.le_massOn, GeometricCurrentOn.ext, Set.Infinite.exists_gt, strictMono_nat_of_lt_succ, Set.Finite.biUnion, ENNReal.pow_pos and ENNReal.inv_two_add_inv_two. Lean checks: all three child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens, using the contract Sub instance GMT.Ch07.instSubGeometricCurrentOnEuclid. Full scratch proofs of the three children and of the exact frozen parent type from them compile, and #print axioms reports [propext, Classical.choice, Quot.sound] for all four declarations.
