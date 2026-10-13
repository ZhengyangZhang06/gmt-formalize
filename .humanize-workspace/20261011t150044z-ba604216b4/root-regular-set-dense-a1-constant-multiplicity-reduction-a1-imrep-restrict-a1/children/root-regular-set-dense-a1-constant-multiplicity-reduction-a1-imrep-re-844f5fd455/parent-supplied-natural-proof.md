# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1.blowup_image_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Lemma A, step A4 (“η_λ is the translation y ↦ y − x (an isometry, Isometry.euclideanHausdorffMeasure_image) followed by the dilation by λ⁻¹, so Hⁿ(η_λ(S)) = λ^{−n}Hⁿ(S) for every S”). This is the scaling used in Simon Ch. 3, proof of Theorem 1.6 “⇒”, where the integral over η_{x,λ}(M ∖ N_j) is bounded by sup|f|·λ^{−n}·Hⁿ(B_{λR}(x) ∩ M ∖ N_j).

Notation:
- Hⁿ = μHE[n] is an outer measure, so every set below has a measure and no measurability of S is needed.
- η_{x,r}(y) = r⁻¹ • (y − x) is blowUpMap x r.
- For c ∈ ℝ and T ⊆ ℝ^P, c • T := {c • z : z ∈ T}.

1. Factorization. For every y ∈ ℝ^P, η_{x,r}(y) = r⁻¹ • (y − x) = r⁻¹ • (y + (−x)). Let τ(y) := y + (−x) (translation by −x) and m(z) := r⁻¹ • z. Then η_{x,r} = m ∘ τ, so η_{x,r}(S) = m(τ(S)) (Set.image_image). Also m(T) = r⁻¹ • T for every T (Set.image_smul). Hence η_{x,r}(S) = r⁻¹ • τ(S).

2. Dilation law. Since r > 0, r⁻¹ ≠ 0. For every nonzero scalar c and every T ⊆ ℝ^P, Hⁿ(c • T) = ‖c‖₊ⁿ • Hⁿ(T) (Mathlib Measure.euclideanHausdorffMeasure_smul₀). Geometrically: z ↦ c • z is a bijection of ℝ^P that multiplies the diameter of every set by |c|. So it carries ε-covers of T to |c|ε-covers of c • T and multiplies every sum Σ diam(Cᵢ)ⁿ by |c|ⁿ. Letting ε ↓ 0 gives the law for the Hausdorff measure, and μHE[n] is a fixed constant multiple of it. With c = r⁻¹ and T = τ(S): Hⁿ(r⁻¹ • τ(S)) = ‖r⁻¹‖₊ⁿ • Hⁿ(τ(S)).

3. Translation invariance. τ is an isometry of ℝ^P, because |τ(y) − τ(y')| = |y − y'| (Mathlib isometry_add_right (−x)). The Hausdorff measure of the image of an arbitrary set under an isometry equals that of the set (Isometry.euclideanHausdorffMeasure_image): isometries preserve diameters, so covers correspond with equal sums. Hence Hⁿ(τ(S)) = Hⁿ(S).

4. Constant.
- By steps 1–3, Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ • Hⁿ(S), where an ℝ≥0-scalar acts on ℝ≥0∞ as multiplication by its coercion (ENNReal.smul_def).
- Because r > 0, ‖r⁻¹‖ = |r⁻¹| = r⁻¹ (abs_of_pos). So ‖r⁻¹‖₊ⁿ is the nonnegative real number (r⁻¹)ⁿ, and its coercion to ℝ≥0∞ equals ENNReal.ofReal (r⁻¹ ^ n) (ENNReal.ofReal_coe_nnreal).
- Therefore Hⁿ(η_{x,r}(S)) = ENNReal.ofReal (r⁻¹ ^ n) · Hⁿ(S). ∎

## Key steps

1. Factor the blow-up as translation then dilation: η_{x,r}(S) = r⁻¹ • (S + (−x)) (Set.image_image, Set.image_smul).
2. Dilation law: Hⁿ(c • T) = ‖c‖₊ⁿ Hⁿ(T) for c = r⁻¹ ≠ 0 (Measure.euclideanHausdorffMeasure_smul₀).
3. Translation invariance: Hⁿ(S + (−x)) = Hⁿ(S) (isometry_add_right, Isometry.euclideanHausdorffMeasure_image).
4. For r > 0 the factor ‖r⁻¹‖₊ⁿ coerced to ℝ≥0∞ equals ENNReal.ofReal (r⁻¹ ^ n).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 over dag.json: id/lean_name/status/depth of all 212 nodes; lean_statement of dtc_approxTangent_of_null_diff, hasApproximateTangentSpaceAt_iff_of_null_sdiff, dtc_approxTangent_sdiff_singleton, dtc_hausdorff_dilation, regcomp_atl_blowUp_measure_scaling, rsdic_ae_tangent_iff_of_subset, rsdic_imrep_ae_tangent_orient_of_subset, regcomp_approx_tangent_locality, rsd_cmr_imrep_restrict`
- `rg -o --no-filename 'rsd_cmr_[A-Za-z0-9_']+' dag.json nodes/ GMT/ (collision check for rsd_cmr_ir_*)`
- `rg -n 'HasApproximateTangentSpaceAt|blowUpMap' -t lean local-references/123e8435b4a2469b`
- `rg -n '^(theorem|lemma) [A-Za-z_.']*([Aa]pproximateTangent|approxTangent|blowUp)' lake-packages-25730c7c/simongmt/Poincare`
- `sed -n 1,160p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable.mono, blowUpMap, HasApproximateTangentSpaceAt); sed -n 1,80p Chapter04/TangentDensity.lean (hausdorff_blowUp_image)`
- `grep in local-references/123e8435b4a2469b/mathlib: euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image, Measure.euclideanHausdorffMeasure_smul₀, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, isometry_mul_right/isometry_add_right`
- `git show <accepted branches>:GMT/Ch07/Submission.lean for Submission.dtc_approxTangent_sdiff_singleton and Submission.dtc_hausdorff_dilation; import survey over 196 humanize-recursive branches`
- `python3 contract_scope (verifier/gmt-compare.py) on Contract.lean; validate_lean_statement (verifier/lean_contract.py) on both child types and the parent type`
- `lake env lean /tmp/rsd-cmr-ir-decomp/{Children,NodeChallenge1,NodeChallenge2,SolutionSim,ImportCheck}.lean (#print axioms)`
- `book/chapter-03.txt lines 75-145 (Definition 1.4, proof of Theorem 1.6 =>)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-restrict-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-restrict-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rsd-cmr-ir-decomp/Children.lean`
- `/tmp/rsd-cmr-ir-decomp/NodeChallenge1.lean`
- `/tmp/rsd-cmr-ir-decomp/NodeChallenge2.lean`
- `/tmp/rsd-cmr-ir-decomp/SolutionSim.lean`
- `/tmp/rsd-cmr-ir-decomp/ImportCheck.lean`

Contract and imports:
- The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.
- The comparator child scope is: namespace GMT.Ch07 with the contract's opens. Only CountablyRectifiable and HasApproximateTangentSpaceAt are opened from Chapter03, so blowUpMap is written fully qualified.

No reachable library proof of either child:
- In the snapshot and in SimonGMT Chapter03, HasApproximateTangentSpaceAt has only finrank_eq, the plane model, and uniqueness. There is no null-set or locality lemma.
- SimonGMT Chapter04/TangentDensity.lean proves hausdorff_blowUp_image, which is the A4 scaling. It is not imported by GMT.Ch07.Submission (ImportCheck: unknown identifier), and 195 of 196 branches keep the contract imports. So child 1 must be proved locally.

Other DAG nodes:
- The other-branch node dtc_approxTangent_of_null_diff is a Lemma A variant with a different type (open V, no measurability). It is still decomposing, so it cannot be reused.
- The accepted dtc_approxTangent_sdiff_singleton and dtc_hausdorff_dilation have different types. Their proofs (about 45 and 12 lines) served only as templates.
- No rsd_cmr_ir_* name exists in dag.json, the node directories, or GMT/.

Mathlib tools used in the compiled proofs: Measure.euclideanHausdorffMeasure_smul₀, isometry_add_right, Isometry.euclideanHausdorffMeasure_image, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, Bornology.IsBounded.subset_closedBall_lt, Ioo_mem_nhdsGT, Tendsto.congr', measure_eq_zero_iff_ae_notMem, CountablyRectifiable.mono, AEStronglyMeasurable.mono_measure, ae_restrict_of_ae_restrict_of_subset, Set.sdiff_self_inter.

Book: Simon Ch. 3, Definition 1.4 and the proof of Theorem 1.6 "=>" (chapter-03.txt lines 77-143) confirm the cited splitting and the scaling Hⁿ(η_{x,λ}(Z)) = λ^{-n}Hⁿ(Z).

Lean checks:
- Both child types elaborate in exact NodeChallenge form.
- Both children are fully proved, and the frozen parent type is proved from child 2, which uses child 1.
- All `exact Submission.X` targets depend only on propext, Classical.choice and Quot.sound.
