# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1.bilip_integral_sandwich-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: V := μ₂(E).toReal ≥ 0 and κ̂ := ENNReal.ofReal κ.
1. Preliminaries.
   - Since κ ≥ 1, we have κ ≥ 0, κ̂ ≠ ∞ and κ̂.toReal = κ (ENNReal.toReal_ofReal).
   - μ₁ is finite: μ₁(E) ≤ (κ̂ · μ₂)(E) = κ̂ · μ₂(E) < ∞ (Measure.le_iff', Measure.smul_apply, μ₂ finite).
   - M ≥ |φ(0)| ≥ 0.
2. Nonnegative case. Let g : E → ℝ be continuous with 0 ≤ g ≤ M everywhere.
   g is a.e.-strongly measurable for every measure and ‖g‖ ≤ M. So g is integrable for the finite measures μ₁ and μ₂ (Integrable.of_bound). It is also integrable for κ̂ · μ₁ and κ̂ · μ₂ (Integrable.smul_measure, κ̂ ≠ ∞).
   Put a := ∫ g dμ₂ and b := ∫ g dμ₁.
   (a) a ≥ 0 and b ≥ 0 (integral_nonneg).
   (b) a ≤ M V: by norm_integral_le_of_norm_le_const, |a| ≤ M · μ₂.real(E) = M V.
   (c) b ≤ κ a: since μ₁ ≤ κ̂ · μ₂ and g ≥ 0, integral_mono_measure gives b ≤ ∫ g d(κ̂ · μ₂). By integral_smul_measure, ∫ g d(κ̂ · μ₂) = κ̂.toReal · a = κ a.
   (d) a ≤ κ b: the same argument with μ₂ ≤ κ̂ · μ₁.
   Using κ − 1 ≥ 0:
   - b − a ≤ (κ − 1)a ≤ (κ − 1)κ a ≤ (κ − 1)κ M V. The steps use (c); then a ≥ 0 and κ ≥ 1; then (b) and (κ − 1)κ ≥ 0.
   - a − b ≤ (κ − 1)b ≤ (κ − 1)κ a ≤ (κ − 1)κ M V. The steps use (d); then (c); then (b).
   Hence |b − a| ≤ (κ − 1)κ M V.
3. Splitting φ. Let φ⁺ := max(φ, 0) and φ⁻ := max(−φ, 0).
   - Both are continuous with values in [0, M], because |φ| ≤ M and M ≥ 0.
   - φ = φ⁺ − φ⁻ (max_zero_sub_max_neg_zero_eq_self).
   - Both are integrable for the finite measures μ₁ and μ₂, so ∫ φ dμᵢ = ∫ φ⁺ dμᵢ − ∫ φ⁻ dμᵢ for i = 1, 2 (integral_sub).
4. Conclusion. By step 3, the difference regroups as (∫φ⁺dμ₁ − ∫φ⁺dμ₂) − (∫φ⁻dμ₁ − ∫φ⁻dμ₂). By the triangle inequality,
   |∫ φ dμ₁ − ∫ φ dμ₂| ≤ |∫ φ⁺ dμ₁ − ∫ φ⁺ dμ₂| + |∫ φ⁻ dμ₁ − ∫ φ⁻ dμ₂|.
   Step 2 applied to g = φ⁺ and to g = φ⁻ bounds each term by (κ − 1)κ M V. So the total is at most 2((κ − 1)κ(M V)), the claim.

## Key steps

1. κ̂ = ENNReal.ofReal κ is finite with real value κ; μ₁(E) ≤ κ̂μ₂(E) < ∞; M ≥ |φ 0| ≥ 0
2. for continuous 0 ≤ g ≤ M: 0 ≤ ∫g dμ₂ ≤ MV, and integral_mono_measure with integral_smul_measure gives ∫g dμ₁ ≤ κ∫g dμ₂ and ∫g dμ₂ ≤ κ∫g dμ₁
3. algebra: |∫g dμ₁ − ∫g dμ₂| ≤ (κ − 1)κMV
4. φ = max(φ,0) − max(−φ,0), with both parts continuous and valued in [0, M]; apply the sandwich to each part and add

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project ea5607598f31, mathlib 25730c7c759d)`
- `diff GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean (identical frozen contract)`
- `rg -n 'theorem hausdorffMeasure_image_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_eq_volume|notation.*μHE' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem map_apply_of_aemeasurable|theorem le_iff' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/*.lean`
- `rg -n 'integral_mono_measure|theorem integral_smul_measure|^theorem integral_map|theorem norm_integral_le_of_norm_le_const|theorem integral_sub ' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/`
- `rg -n 'theorem ContinuousOn.aemeasurable|theorem ContinuousOn.aestronglyMeasurable' <snapshot>/mathlib/Mathlib`
- `rg -n 'image_preimage_inter|leftInvOn_invFunOn|max_zero_sub_max_neg_zero_eq_self|Integrable.smul_measure|restrict_apply. |isFiniteMeasure_map|theorem ofReal_pow|theorem uniformContinuous_iff ' <snapshot>/mathlib/Mathlib`
- `rg -l 'euclideanHausdorffMeasure_image_le_of_lipschitzOn' <snapshot> (no match; found in .lake/packages/simongmt Poincare/SimonGMT/Chapter02/Lipschitz.lean:216)`
- `rg -l 'dohr_tp_gat_bilip_measure_comparison|dohr_tp_gat_bilip_integral_sandwich' <run>/nodes <run>/dag.json <snapshot>/project (no match); python3 name scan of dag.json lean_names`
- `read accepted Submission.aetp_c1_piece_approxTangent (worktree 4be3fb780add150d6ac3, candidate 94f10688) for the bi-Lipschitz/sandwich Lean pattern`
- `read parent decomposition-v1.json and parent-child-handoff.json of this node`
- `grep -n '1.8 Theorem' book/chapter-02.txt`
- `lean -o build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (isolated scratch, LEAN_PATH to prebuilt package oleans)`
- `lean scratch/ChildA.lean; lean scratch/ChildB.lean; lean scratch/Assembly.lean with #print axioms`
- `python3 -I tools/gen.py: lean_contract.validate_lean_statement + gmt-compare.child_modules (contract mode); lean on 3 NodeChallenge (bare Submission) and 3 NodeSolution (extended Submission) modules`
- `lean scratch/Inst.lean with pp.explicit/pp.fullNames (instance check)`
- `WebSearch 'Hausdorff measure Lipschitz image H^s(f(A)) ≤ Lip(f)^s H^s(A) bi-Lipschitz map comparison Evans Gariepy'`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/4be3fb780add150d6ac3/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-e0ca221366/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-5428b2422d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/bilip-decomp-p7qvLW/scratch/ChildA.lean`
- `/tmp/bilip-decomp-p7qvLW/scratch/ChildB.lean`
- `/tmp/bilip-decomp-p7qvLW/scratch/Assembly.lean`
- `/tmp/bilip-decomp-p7qvLW/full/GMT/Ch05/Submission.lean`
- `/tmp/bilip-decomp-p7qvLW/gen/parent/NodeChallenge.lean`
- `/tmp/bilip-decomp-p7qvLW/gen/bilip_measure_comparison/NodeChallenge.lean`
- `/tmp/bilip-decomp-p7qvLW/gen/bilip_integral_sandwich/NodeSolution.lean`

Pinned revisions match the workspace (project ea56075, Mathlib 25730c7c, simongmt 2b366308). The frozen Submission is byte-identical to the Contract.
The snapshot's Mathlib supplies every tool the two children and the assembly need:
- LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733); μHE notation and euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:72/187)
- Measure.map_apply_of_aemeasurable (Map.lean:166); Measure.le_iff/le_iff' (CompleteLattice.lean:41/46); restrict_apply' (Restrict.lean:111); Measure.isFiniteMeasure_map (Typeclasses/Finite.lean:124)
- integral_mono_measure (Bochner/Basic.lean:623), integral_smul_measure (:1052), integral_map (:1081), norm_integral_le_of_norm_le_const (:1004), integral_sub (:263)
- ContinuousOn.aemeasurable (IntegrableOn.lean:754); Integrable.smul_measure (L1Space/Integrable.lean:317)
- image_preimage_inter (Data/Set/Image.lean:457); InjOn.leftInvOn_invFunOn (Data/Set/Function.lean:987); max_zero_sub_max_neg_zero_eq_self (MinMax.lean)
The μHE Lipschitz image bound euclideanHausdorffMeasure_image_le_of_lipschitzOn has no match in the snapshot. It is available under the frozen imports at simongmt Chapter02/Lipschitz.lean:216, and it formalizes Simon Ch. 2 Thm 1.8(i) (book/chapter-02.txt l.270).
The accepted aetp_c1_piece_approxTangent (candidate 94f10688) contains the same bi-Lipschitz comparison and sandwich pattern for a globally continuous Φ. It informed the child proofs but is not reusable as a declaration.
The proposed names have no match in dag.json, node records or the snapshot.
Lean checks against an isolated compile of the frozen Submission:
- Both children have complete proofs.
- The parent's exact frozen type is assembled from them.
- Axioms are {propext, Classical.choice, Quot.sound}.
- All statements pass validate_lean_statement.
- The verifier-generated NodeChallenge and NodeSolution modules elaborate.
- Instances are Measure.instSMul with an ENNReal scalar, Measure.instPartialOrder and Set.univ.
