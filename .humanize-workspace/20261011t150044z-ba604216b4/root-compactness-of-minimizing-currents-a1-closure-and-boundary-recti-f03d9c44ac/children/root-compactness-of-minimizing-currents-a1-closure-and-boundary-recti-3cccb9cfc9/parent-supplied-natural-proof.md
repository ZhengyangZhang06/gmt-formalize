# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.lipschitz_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8 (“p_j is injective on D and h : p_j(D) → π_j, h(p_j x) := p_{π_j}x, is 4-Lipschitz. Extend h ... (McShane extension of each coordinate ...) ... D ⊆ F_{j,x₀}(ℝⁿ)”); Simon Ch. 3, proof of 1.6, chapter-03.txt lines 249–262 (Ej ∩ B_{δ/4}(x₀) ⊆ Q^T(graph f) via the extension theorem 1.2 of Ch. 2). We parametrize D directly over ℝⁿ ≅ T, which is the composition of Simon's graph map with the orthogonal transformation.

1. Let C' := max(C, 0) ≥ 0. Since |p_T(·)| ≥ 0, |y − x| ≤ C'|p_T(y − x)| for x, y ∈ D.
2. A linear chart of T. As dim T = n, an orthonormal basis of T indexed by {1,…,n} gives a linear isometry ι : T → ℝⁿ. Let L := ι ∘ (orthogonal projection of ℝ^P onto T) : ℝ^P → ℝⁿ. L is linear and |Lv − Lw| = |p_T(v − w)| for all v, w.
3. Inverse on L(D). For x, y ∈ D, |y − x| ≤ C'|Ly − Lx|; in particular L is injective on D. Define g : L(D) → ℝ^P by g(Lx) := x. Then |g(u) − g(v)| ≤ C'|u − v| for u, v ∈ L(D), i.e. g is C'-Lipschitz on L(D).
4. McShane extension coordinatewise. Identify ℝ^P with (Fin P → ℝ) carrying the sup norm; the identification is 1-Lipschitz (|v|_∞ ≤ |v|), so the coordinate map of g is C'-Lipschitz on L(D). By McShane's extension theorem applied to each coordinate (Mathlib `LipschitzOnWith.extend_pi`, built on `LipschitzOnWith.extend_real`) there is a C'-Lipschitz G : ℝⁿ → (Fin P → ℝ) that agrees with the coordinates of g on L(D).
5. Back to the Euclidean norm. The map (Fin P → ℝ) → ℝ^P, v ↦ v, is √P-Lipschitz from the sup norm to the Euclidean norm (|v| ≤ √P|v|_∞; Mathlib `PiLp.antilipschitzWith_ofLp`). Hence F := (this map) ∘ G : ℝⁿ → ℝ^P is Lipschitz with constant √P·C'.
6. Covering. For x ∈ D, F(Lx) = g(Lx) = x, so D ⊆ F(ℝⁿ). ∎

## Key steps

1. Replace C by C' = max(C, 0).
2. L = (isometry T ≅ ℝⁿ) ∘ p_T satisfies |Lv − Lw| = |p_T(v − w)|, so L is injective on D with C'-Lipschitz inverse g on L(D).
3. Extend g coordinatewise by McShane to a Lipschitz G : ℝⁿ → ℝ^P (constant √P·C').
4. G ∘ L = id on D, hence D ⊆ G(ℝⁿ).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical) and Contract.lean against Submission.lean (identical); grep -n 'unitBallVolume' Contract.lean (line 143: volume (ball (0 : Euclid n) 1))`
- `grep -rn 'μHE' <snapshot>/mathlib/Mathlib --include=*.lean (Geometry/Euclidean/Volume/Measure.lean: euclideanHausdorffMeasure_zero, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_homothety_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -rln 'Lusin' <snapshot>/mathlib/Mathlib (only Function/Jacobian.lean, Constructions/Polish/Basic.lean, Topology/MetricSpace/Polish.lean: no Lusin continuity theorem); grep for ContinuousOn theorems with exists/closed/compact in Mathlib/MeasureTheory (no Lusin match)`
- `grep -rn 'starProjection_norm_le|norm_starProjection_apply_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; grep -rn 'theorem LipschitzOnWith.extend_pi|theorem LipschitzOnWith.extend_real|theorem finite_approx_of_totallyBounded|theorem antilipschitzWith_ofLp|theorem tendsto_measure_iUnion_atTop|theorem lintegral_liminf_le|theorem exists_measurable_superset_of_null|theorem Infinite.exists_subset_card_eq|lemma sum_measure_singleton|DenseRange.exists_dist_lt' <snapshot>/mathlib/Mathlib`
- `sed -n 1,400p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap, countablyRectifiable_of_measure_zero/_range/_iUnion/_sUnion, CountablyRectifiable.mono, regular_euclideanHausdorffMeasure_restrict_submodule); grep -n 'theorem exists_isClosed_continuousOn_of_measurable' SimonGMT/Chapter01/Lusin.lean (exists, but outside the contract import closure: unknown identifier after import GMT.Ch07.Submission)`
- `python3 scan of dag.json lean_statement values for HasApproximateTangentSpaceAt, CountablyRectifiable, starProjection, blowUpMap, Lipschitz, unitBallVolume; status and candidate_commit of doragm_approxTangent_lower_density (accepted, a0c1e365), rsd_cmr_ir_blowUp_image_measure (accepted, 6d5fb477), dor_ims_lusin_measurable_continuousOn (accepted, e4172a7b), types byte-identical; no lean_name starts with 'cbrr'`
- `git show a0c1e365af06 (accepted proof of doragm_approxTangent_lower_density); git show 6d5fb477cd67 (accepted rsd_cmr_ir_blowUp_image_measure); git show 77fcc7d4ea07 (accepted precedent adding a SimonGMT Chapter01 import to Submission.lean)`
- `sed -n 77,274p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt (Definition 1.4, Remark 1.5(3), Theorem 1.6, proof of '⇐' with (1)–(10) and the printed ε = 1/16ⁿ)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on all 11 types (pass); contract_scope in verifier/gmt-compare.py (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end); grep -n 'def _existing_lean_name_problem' -A 40 and the accepted-reuse branch in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `lake env lean /tmp/crt-decomp-x91/lean/Types2.lean (all 10 child types and the parent elaborate), Assembly.lean (parent from dim_zero, uniform_density and uniform_to_rectifiable; uniform_to_rectifiable from plane_net, cone_claim and lipschitz_cover), NetZero.lean, ConeClaim.lean, LipCover.lean, ConeDensity.lean, LusinImport.lean, and the reviewer file /tmp/crt-review-r7/lean/UD.lean (#print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f03d9c44ac/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/crt-decomp-x91/lean/Types2.lean`
- `/tmp/crt-decomp-x91/lean/Assembly.lean`
- `/tmp/crt-decomp-x91/lean/NetZero.lean`
- `/tmp/crt-decomp-x91/lean/ConeClaim.lean`
- `/tmp/crt-decomp-x91/lean/LipCover.lean`
- `/tmp/crt-decomp-x91/lean/ConeDensity.lean`
- `/tmp/crt-review-r7/lean/UD.lean`

The snapshot contract equals the workspace Contract.lean and Submission.lean, and unitBallVolume (Contract.lean:143) supplies ωₙ. The pinned Mathlib has every lemma the child proofs cite but no Lusin continuity theorem. SimonGMT's Chapter01 Lusin lemma lies outside the contract's import closure, so uniform_density reuses the accepted DAG theorem dor_ims_lusin_measurable_continuousOn instead. SimonGMT Chapter03 provides the definitions and the union/range/mono lemmas for CountablyRectifiable but no rectifiability criterion (Simon 3.1.6), which justifies the split. Three children reuse accepted DAG declarations with byte-identical types (doragm_approxTangent_lower_density, rsd_cmr_ir_blowUp_image_measure, dor_ims_lusin_measurable_continuousOn), and the seven new cbrr_* names collide with no DAG name. All 11 types pass the verifier's lexical check and elaborate in the replayed contract scope. Hypothesis-only Lean assemblies prove the frozen parent type and uniform_to_rectifiable from their children. Scratch Lean proofs of every new child, each taking its siblings' exact types as hypotheses, compile with axioms propext, Classical.choice and Quot.sound only.
