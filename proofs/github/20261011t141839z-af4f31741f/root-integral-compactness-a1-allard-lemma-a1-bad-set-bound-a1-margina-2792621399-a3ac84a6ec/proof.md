# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1.marginal_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof. In Simon 8.5.10 (p. 221, the Besicovitch deduction from (4)), the tilt integrals ∫_{B_{ρ_y}(y)×G}‖p_S − p‖dW over disjoint balls are summed to at most ∫_{B_3(0)×G}‖p_S − p‖dW. There the functional T(A) := ∫⁻_{A ×ˢ univ} ofReal t_P(z.2) dW.measure(z) is used only through two properties: monotonicity, and countable additivity on pairwise disjoint Borel sets. This child packages both properties by showing that T agrees on Borel sets with a measure. It is stated for an arbitrary measure m on ℝ^N × G(N,n) (G(N,n) := Grassmannian N n, product σ-algebra) and an arbitrary g : ℝ^N × G(N,n) → [0,∞]. The parent applies it with m := W.measure and g(z) := ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 − Grassmannian.projectionLinearMap P)‖.

1. Let m_g := m.withDensity g. This is a measure on ℝ^N × G(N,n) with m_g(S) = ∫⁻_S g dm for every measurable S (MeasureTheory.withDensity_apply). Mathlib's withDensity_apply needs only S to be measurable, not g.

2. Let τ := m_g.map Prod.fst, the image of m_g under the first projection Prod.fst : ℝ^N × G(N,n) → ℝ^N. This projection is measurable (measurable_fst).

3. Let A ⊆ ℝ^N be measurable.
 – By Measure.map_apply (with measurable_fst and A measurable), τ(A) = m_g(Prod.fst ⁻¹' A).
 – Prod.fst ⁻¹' A is measurable (measurable_fst hA), so step 1 gives m_g(Prod.fst ⁻¹' A) = ∫⁻_{Prod.fst ⁻¹' A} g dm.
 – Finally Prod.fst ⁻¹' A = A ×ˢ univ (Set.prod_univ).
 Hence τ(A) = ∫⁻_{A ×ˢ univ} g dm, which is the claim. ∎

Consequently T = τ on Borel sets, so T is monotone and countably additive on pairwise disjoint Borel sets, which is what step 2 of the parent proof uses. The parent evaluates τ only on closed balls B_ρ(y) and on the open ball B°_3(0). These sets are measurable, so the values of τ on non-measurable sets play no role.

## Key steps

1. m_g := m.withDensity g satisfies m_g(S) = ∫⁻_S g dm for measurable S (no measurability of g needed)
2. τ := m_g.map Prod.fst (Prod.fst is measurable)
3. For measurable A: τ(A) = m_g(Prod.fst⁻¹'A) = m_g(A ×ˢ univ) = ∫⁻_{A ×ˢ univ} g dm (Measure.map_apply, Set.prod_univ, withDensity_apply)

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem exist_disjoint_covering_families|no_satelliteConfig' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean (lines 156, 455)`
- `rg -n 'instance.*HasBesicovitchCovering' mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean (line 499)`
- `rg -n 'theorem withDensity_apply' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean (line 44: only MeasurableSet s required)`
- `rg -n 'theorem map_apply' mathlib/Mathlib/MeasureTheory/Measure/Map.lean (line 170); rg -n 'theorem prod_univ' mathlib/Mathlib/Data/Set/Prod.lean (line 97)`
- `rg -n 'countable_of_nonempty_interior' mathlib/Mathlib/Topology (Bases.lean:493); rg -n 'theorem measure_biUnion_le|theorem measure_iUnion_fintype_le' mathlib/Mathlib/MeasureTheory (OuterMeasure/Basic.lean:74,84); rg -n 'theorem measure_biUnion' mathlib/Mathlib/MeasureTheory (Measure/Basic.lean:132)`
- `rg -n 'theorem tsum_mul_left|theorem tsum_le_tsum' mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean (116, 180); rg -n 'theorem add_apply|theorem smul_apply' mathlib/Mathlib/MeasureTheory/Measure/Module.lean (91, 120); rg -n 'ball_subset_interior_closedBall|mem_ball_self|ball_subset_closedBall' mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean (1216, 379, 477)`
- `grep -n 'abbrev Grassmannian|structure Varifold|def weight' simongmt Chapter08/Varifold.lean (60, 335, 557: weight = measure.map Prod.fst)`
- `python3 scan of dag.json: Besicovitch nodes (besicovitch_ratio_cover_estimate accepted in root.density_semicontinuity-a1; intcpt_vdb_besicovitch_cover_estimate decomposing, identical thickening type) and duplicate lean_names (none; no cross-branch reuse in the run)`
- `git show b70dd9d5 (accepted proof of besicovitch_ratio_cover_estimate); git show da0a42e7:GMT/Ch08/Submission.lean and 3beae5a3:GMT/Ch08/Submission.lean (leaf bases = contract + tracked dependency declarations only)`
- `grep -n Besicovitch book/chapter-08.txt; sed -n 776,850p (Simon 8.5.10 printed (1)-(5) and the Besicovitch deduction, p. 221)`
- `lake env lean /tmp/bsb-decomp-v1/Check0.lean (#check of the cited lemmas after import GMT.Ch08.Submission)`
- `lake env lean /tmp/bsb-decomp-v1/Assembly.lean (both children proved; frozen parent proved from them + stubbed accepted sibling; comparator wrappers; #print axioms)`
- `python3 gmt-compare.child_modules -> /tmp/bsb-decomp-v1/gen/Both.lean; lake env lean (exact challenge modules elaborate)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on both lean_statements`
- `grep intcpt_allard_bsb_ in dag.json and the run directory; git grep -l intcpt_allard_bsb_ over all 523 refs (0 hits)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-bad-set-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-good-point-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-besicovitch-ratio-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-variation-density-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/bsb-decomp-v1/Check0.lean`
- `/tmp/bsb-decomp-v1/Assembly.lean`
- `/tmp/bsb-decomp-v1/gen/Both.lean`

The snapshot is project 63436ae6 + Mathlib 25730c7c; its Contract is byte-identical to the workspace Contract and Submission. Every lemma cited in the two child proofs exists in the snapshot with suitable hypotheses: withDensity_apply needs only a measurable set; exist_disjoint_covering_families needs 1 < τ, no satellite configurations and a bounded-radius BallPackage; Euclidean N has a HasBesicovitchCovering instance. Each lemma was #checked from import GMT.Ch08.Submission. The accepted thickening-form lemma besicovitch_ratio_cover_estimate is in another branch and not in this node's base. Leaf bases contain only the contract plus tracked dependencies, and the run never reuses a declaration across branches (variation_density_bound re-proves it as intcpt_vdb_besicovitch_cover_estimate). So the more general containing-set form is proposed under a fresh name; its proof is the accepted one with the thickening containment replaced by the hypothesis B ⊆ O. In the comparator's replayed scope both child statements elaborate, pass validate_lean_statement, and are fully proved with axioms propext, Classical.choice and Quot.sound only. The frozen parent type (byte-identical) is proved from them plus the accepted sibling good_point_monotonicity, with no sorry of its own. An independent reviewer re-ran all checks and accepted. Neither lean_name occurs in dag.json, the run directory or any git ref.
