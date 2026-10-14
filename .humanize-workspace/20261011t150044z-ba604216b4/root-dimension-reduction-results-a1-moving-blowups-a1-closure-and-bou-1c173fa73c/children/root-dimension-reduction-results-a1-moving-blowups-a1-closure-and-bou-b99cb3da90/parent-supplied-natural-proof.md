# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_bound-a1.liminf_add-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. [0, ∞] is a complete lattice, so for every w : ι → [0, ∞], liminf_F w = sup_{s ∈ F} inf_{i ∈ s} w(i) (Mathlib Filter.liminf_eq_iSup_iInf). Apply this to u, v and w := (i ↦ u(i) + v(i)). Write a(s) := inf_{i∈s} u(i), b(s) := inf_{i∈s} v(i) and Λ := liminf_F w = sup_{r∈F} inf_{i∈r} (u(i) + v(i)). The claim becomes sup_{s∈F} a(s) + sup_{s'∈F} b(s') ≤ Λ.
2. Pairwise bound. Let s, s' ∈ F. For each i ∈ s ∩ s', a(s) ≤ u(i) because i ∈ s, and b(s') ≤ v(i) because i ∈ s'. Since addition is monotone in [0, ∞], a(s) + b(s') ≤ u(i) + v(i). Taking the infimum over i ∈ s ∩ s' gives a(s) + b(s') ≤ inf_{i ∈ s∩s'} (u(i) + v(i)). As F is a filter, s ∩ s' ∈ F, so this infimum is one of the terms of the supremum Λ. Therefore a(s) + b(s') ≤ Λ.
3. Both index families are nonempty because univ ∈ F. In [0, ∞], adding a constant commutes with nonempty suprema. This gives the following: if p and q are predicates, some i satisfies p, some j satisfies q, and f(i) + g(j) ≤ c whenever p(i) and q(j), then (sup_{p(i)} f(i)) + (sup_{q(j)} g(j)) ≤ c (Mathlib ENNReal.biSup_add_biSup_le'). Apply it with p = q = (· ∈ F), f = a, g = b and c = Λ; its main hypothesis is step 2. This gives sup_{s∈F} a(s) + sup_{s'∈F} b(s') ≤ Λ.
4. By step 1, this inequality is liminf_F u + liminf_F v ≤ liminf_F (i ↦ u(i) + v(i)). No finiteness or boundedness assumption is used, and the argument also covers the trivial filter. ∎

## Key steps

1. liminf_F w = sup_{s∈F} inf_{i∈s} w(i) in the complete lattice [0, ∞] (liminf_eq_iSup_iInf).
2. For s, s' ∈ F: inf_s u + inf_{s'} v ≤ inf_{s∩s'} (u + v) ≤ liminf_F (u + v), since s ∩ s' ∈ F.
3. The index families are nonempty (univ ∈ F), so ENNReal.biSup_add_biSup_le' turns the pairwise bound into liminf_F u + liminf_F v ≤ liminf_F (u + v).

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean SNAP/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean SNAP/project/GMT/Ch07/Contract.lean; python3 read of lake-manifest.json revs (mathlib, simongmt)`
- `python3 scans of RUN/dag.json: selected node (depth 5, decomposing, no children); lean_name collision check for dmcbr_sl_sb_massOn_eq_of_apply_eq_neg, dmcbr_sl_sb_ennreal_liminf_add_le, dmcbr_sl_sb_boundaryMassOn_slice_le (no match); twin nodes cmcsd_sh_slice_boundaryMassOn_le (byte-identical frozen type to the boundary_slice child, status decomposing) and cbrsl_slice_boundary_mass_bound (queued); short statements mentioning liminf, massOn or neg (no accepted generic lemma)`
- `grep -n '_existing_lean_name_problem|_reference_use_problem|max_depth' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and prompts.py`
- `rg/grep over SNAP/mathlib/Mathlib: le_liminf_add, liminf_add_le, biSup_add_biSup_le', limsup_eq_iInf_iSup (to_dual liminf_eq_iSup_iInf), aestronglyMeasurable_zero_measure, integral_zero_measure, ae_zero, tsupport_neg; grep liminf.*add in Topology/Instances/ENNReal/Lemmas.lean and Order/Filter/ENNReal.lean`
- `rg over SNAP/project for massOn_neg, liminf sum lemmas, dmcbr_sl_sb (no match)`
- `grep over .lake/packages/simongmt/Poincare for massOn_neg, massOn_sub, Neg instances on GeometricCurrentOn (no match); sed of Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn) and Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn, boundary, ext, boundary_boundary, zero_apply)`
- `grep -n -i slic book/chapter-06.txt; sed -n 1330,1400p (Simon Ch. 6 (4.6)-(4.10))`
- `lake env lean /tmp/dmcbr-sb-decomp/Probe.lean (#check of all used names) and /tmp/dmcbr-sb-decomp/Check.lean (three child proofs, exact frozen parent type from them, #print axioms); validate_lean_statement from verifier/lean_contract.py and runtime lean_contract.py on all four types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-1c173fa73c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dmcbr-sb-decomp/Probe.lean`
- `/tmp/dmcbr-sb-decomp/Check.lean`

Pins match. HEAD b4d606d is the snapshot project commit. Mathlib 25730c7c and SimonGMT 2b366308 match lake-manifest.json. Submission.lean and Contract.lean are byte-identical to the snapshot contract. The snapshot project has no mass-negation lemma, no ENNReal liminf-sum lemma and no dmcbr_sl_sb declaration. SimonGMT Chapter06 provides massOn_mono, le_massOn, covectorEuclideanNorm_neg, GeometricCurrentOn.ext, boundary_boundary and zero_apply, but no mass-under-negation lemma. Mathlib's le_liminf_add requires AddCommGroup. The EReal le_liminf_add and ENNReal.liminf_add_of_*_tendsto_zero do not give ℝ≥0∞ superadditivity, so liminf_add is derived from liminf_eq_iSup_iInf (to_dual of limsup_eq_iInf_iSup, Order/LiminfLimsup.lean:296) and ENNReal.biSup_add_biSup_le' (Basic/ENNReal/Operations.lean:674). The zero-representation step uses aestronglyMeasurable_zero_measure, integral_zero_measure and ae_zero. The three child names collide with no DAG node. The boundary_slice type is byte-identical to the unaccepted twin cmcsd_sh_slice_boundaryMassOn_le, so that name cannot be reused. All four types pass both validate_lean_statement implementations and elaborate in the contract scope. In /tmp/dmcbr-sb-decomp/Check.lean (sha256 efc82f98c106b99309b59da4cbe01b9195da6d79bad62e438977befb63e50dfe), all three children are proved and the exact frozen parent type is proved from them; #print axioms reports only propext, Classical.choice and Quot.sound.
