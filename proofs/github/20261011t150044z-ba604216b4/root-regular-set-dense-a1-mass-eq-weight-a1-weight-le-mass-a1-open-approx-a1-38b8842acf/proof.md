# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1.open_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (choice of K and V), including its stated alternative for K.

Notation: H := μHE[n], M := R.carrier, θ := R.mult, μ := R.measure = (H⌞M).withDensity (x ↦ (θ(x) : [0, ∞])). All sets below are subsets of ℝ^P = Euclid P with its Borel σ-algebra.

1. A compact core K. ℝ^P is a σ-compact metric space and μ is a measure on its Borel sets.
- Every open set is inner regular for μ with respect to closed sets. An open set W is the increasing union of the closed sets F_j := {y : dist(y, ℝ^P ∖ W) ≥ 1/j} (F_j := ℝ^P if W = ℝ^P), so μ(F_j) ↑ μ(W) by continuity from below (Mathlib: Measure.InnerRegularWRT.of_pseudoMetrizableSpace μ).
- Every closed set F is inner regular for μ with respect to compact sets. F is the increasing union of the compact sets F ∩ B̄(0, j), so μ(F ∩ B̄(0, j)) ↑ μ(F) (Mathlib: Measure.InnerRegularWRT.isCompact_isClosed μ, which uses σ-compactness).
- Compose the two (Measure.InnerRegularWRT.trans) and use c < μ(W) with W open. This gives a compact K ⊆ W with c < μ(K).
- Equivalently, use the exhaustion of parent step 3: K_j := {y : ‖y‖ ≤ j and B(y, 1/j) ⊆ W} is compact and increasing with union W, so μ(K_j) ↑ μ(W) > c.
2. An open V with compact closure. ℝ^P is locally compact and regular, K is compact, W is open and K ⊆ W. So there is an open set V with K ⊆ V, closure V ⊆ W and closure V compact (exists_open_between_and_isCompact_closure). In particular V ⊆ closure V ⊆ W.
3. Lower bound. By monotonicity, μ(V) ≥ μ(K) > c.
4. Finiteness. closure V is closed, hence Borel measurable.
- By the definition of a measure with density on measurable sets (withDensity_apply) and of restriction (Measure.restrict_restrict, which uses the measurability of closure V): μ(closure V) = ∫⁻_{closure V} θ d(H⌞M) = ∫⁻_{closure V ∩ M} θ dH = ∫⁻_{M ∩ closure V} θ dH.
- closure V is compact and closure V ⊆ W ⊆ U. So the structure field R.locallyIntegrable_mult, applied to the compact set closure V, says that this lower integral is ≠ ∞.
- Hence μ(V) ≤ μ(closure V) < ∞.
5. Conclusion. V is open, V ⊆ W, c < μ(V) and μ(V) < ∞. The openness of U is not used.

Lean route (kernel-checked in the frozen contract scope; axioms propext, Classical.choice, Quot.sound):
  intro P n U R W hW hWU c hc
  obtain ⟨K, hKW, hK, hcK⟩ := ((Measure.InnerRegularWRT.isCompact_isClosed R.measure).trans (Measure.InnerRegularWRT.of_pseudoMetrizableSpace R.measure)) hW c hc
  obtain ⟨V, hVo, hKV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  refine ⟨V, hVo, subset_closure.trans hVW, hcK.trans_le (measure_mono hKV), ?_⟩
  have hcl : R.measure (closure V) ≠ ∞ := by
    unfold IMRep.measure
    rw [withDensity_apply _ isClosed_closure.measurableSet, Measure.restrict_restrict isClosed_closure.measurableSet, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hVc (hVW.trans hWU)
  exact (measure_mono subset_closure).trans_lt hcl.lt_top

## Key steps

1. Inner regularity (open sets by closed sets, closed sets by compact sets) gives a compact K ⊆ W with c < μ(K).
2. exists_open_between_and_isCompact_closure gives an open V ⊇ K with closure V compact and contained in W.
3. μ(V) ≥ μ(K) > c by monotonicity.
4. μ(closure V) = ∫⁻_{M ∩ closure V} θ dH^n ≠ ∞ by withDensity_apply, restrict_restrict and R.locallyIntegrable_mult, so μ(V) < ∞.

## Reference use

### local-project

Queries:
- `cat nodes/root-regular-set-dense-a1-mass-eq-weight-a1-weight-le-mass-a1/{parent-child-handoff.json,decomposition-v1.json}`
- `python3 -I scans of dag.json (298 nodes): lean_name, theorems, status and depth of this node, its siblings and root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_norm_bound-a1`
- `grep -rl rsd_mw_wlm GMT .humanize; git log --all --oneline -S rsd_mw_wlm; git log --all --oneline -S orient_opNorm_le_one`
- `git show 0325970d8b47298803106a41abbcdb3c8c9ac103 -- GMT`
- `rg -n 'measure_le_massOn|massOn_le_measure|orient_opNorm|opNorm_le_one|unit_orientation_norm' local-references/123e8435b4a2469b/project -t lean`
- `rg -n 'theorem of_pseudoMetrizableSpace|theorem isCompact_isClosed|theorem trans ' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem exists_open_between_and_isCompact_closure' mathlib/Mathlib/Topology/Separation/Regular.lean`
- `rg -n 'theorem withDensity_apply |theorem withDensity_absolutelyContinuous ' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `rg -n 'theorem integral_withDensity_eq_integral_smul ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean; rg -n 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean; rg -n 'theorem ofReal_integral_eq_lintegral_ofReal' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `rg -n 'isBoundedBilinearMap_apply :' mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n 'theorem opNorm_smul_le|theorem opNorm_le_bound ' mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `rg -n 'lemma isFiniteMeasure_restrict' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean; rg -n 'theorem le_of_forall_lt ' mathlib/Mathlib/Order/Basic.lean`
- `sed -n 420,640p verifier/gmt-compare.py; cat verifier/lean_contract.py`
- `python3 -I /tmp/rsd-mw-wlm-v2-scripts/build.py`
- `lake env lean /tmp/rsd-mw-wlm-v2/{Full,FromProofs}.lean; lake env lean /tmp/rsd-mw-wlm-v2/cmp/*_{Challenge,SolutionEmu}.lean`
- `lake env lean /tmp/rsd-mw-wlm-v2-review/{Stubbed,AxStubbed,FromProofsUncleAx,Probe}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-weight-le-mass-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-weight-le-mass-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rsd-mw-wlm-v2/FromProofs.lean`
- `/tmp/rsd-mw-wlm-v2/subproblems.json`
- `/tmp/rsd-mw-wlm-v2-review/Stubbed.lean`
- `/tmp/rsd-mw-wlm-v2-review/FromProofsUncleAx.lean`

Snapshot (project b4d606d, Mathlib 25730c7c): the workspace Contract.lean and Submission.lean are identical (457 lines).

No snapshot project declaration proves any child. rg for measure_le_massOn, massOn_le_measure, orient_opNorm, opNorm_le_one and unit_orientation_norm over the project finds no match.

The proposition of child 1 is proved in another branch as unit_orientation_norm_le_one (commit 0325970d). That name is reserved by an active node there and is not merged into this branch, so attempt 1's reuse was rejected. Child 1 is re-proved under the fresh name rsd_mw_wlm_orient_opNorm_le_one.

Mathlib tools located in the snapshot:
- InnerRegularWRT.trans, of_pseudoMetrizableSpace and isCompact_isClosed (Regular.lean:280/674/684)
- exists_open_between_and_isCompact_closure (Separation/Regular.lean:364)
- withDensity_apply and withDensity_absolutelyContinuous (WithDensity.lean:44/146)
- integral_withDensity_eq_integral_smul (Bochner/ContinuousLinearMap.lean:251)
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- isBoundedBilinearMap_apply (BoundedLinearMaps.lean:391)
- ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739)
- isFiniteMeasure_restrict (Typeclasses/Finite.lean:40)
- le_of_forall_lt (Order/Basic.lean:352)
- opNorm_le_bound and opNorm_smul_le (Operator/Basic.lean:196/329)

Lean checks in the replayed contract scope:
- All five children compile from the Lean-route blocks of their natural proofs, with axioms propext, Classical.choice and Quot.sound only.
- The exact parent type compiles from the children plus the two uncle stubs. With the uncles as axioms, the parent depends only on those two and the standard axioms.
- All challenge files from the verifier's child_modules elaborate.

Names: none of the five lean_names occurs in dag.json (298 nodes), GMT/, .humanize (apart from this node's rejected v1) or any git ref.
