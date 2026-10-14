# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.borel_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) (Lean Eucl k) with its Borel σ-algebra; ℝⁿ is a Polish space and ℝ^P is Hausdorff. Hypotheses: D ⊆ ℝⁿ Borel; Φ : ℝⁿ → ℝ^P continuous on D and injective on D; γ : ℝⁿ → ℝ^Q Borel measurable. The set D carries the subspace σ-algebra (Lean: the subtype ↥D); ι : D → ℝ^P, ι(w) := Φ(w), is the restriction of Φ to D (Lean D.domRestrict Φ), and γ_D : D → ℝ^Q, γ_D(w) := γ(w), is the restriction of γ (Lean D.domRestrict γ). This is Step 6 of the parent proof, in the equivalent form it states there (g = Function.extend (Φ restricted to D) (γ restricted to D) 0, Borel by ContinuousOn.measurableEmbedding and MeasurableEmbedding.measurable_extend), for an arbitrary Borel set D and Borel field γ.

1. (ι is a measurable embedding: Lusin–Souslin.) D is a Borel subset of the Polish space ℝⁿ, Φ is continuous and injective on D, and ℝ^P is a Hausdorff space with its Borel σ-algebra. By the Lusin–Souslin theorem (a continuous injective image of a Borel subset of a Polish space is Borel; Kechris, Classical Descriptive Set Theory, Thm. 15.1), ι is injective, measurable, and maps every measurable subset of D onto a Borel subset of ℝ^P; i.e. ι is a measurable embedding (Mathlib ContinuousOn.measurableEmbedding, which also uses MeasurableSet.image_of_continuousOn_injOn). In particular ι(D) = Φ(D) is Borel.

2. (γ_D is measurable.) γ_D = γ ∘ (inclusion D ↪ ℝⁿ), and the inclusion is measurable for the subspace σ-algebra (Mathlib measurable_subtype_coe), so γ_D is measurable.

3. (Definition of g.) Let g := Function.extend ι γ_D 0 : ℝ^P → ℝ^Q. Explicitly, g(y) = γ_D(w) if y = ι(w) for some w ∈ D (this w is unique because ι is injective), and g(y) = 0 if y ∉ ι(D) = Φ(D).

4. (g is Borel.) For a Borel set S ⊆ ℝ^Q, g⁻¹(S) = ι(γ_D⁻¹(S)) ∪ (ℝ^P ∖ ι(D)) if 0 ∈ S, and g⁻¹(S) = ι(γ_D⁻¹(S)) if 0 ∉ S. Here γ_D⁻¹(S) is measurable in D (step 2), so ι(γ_D⁻¹(S)) is Borel (step 1), and ι(D) is Borel (step 1). Hence g is Borel measurable; this is Mathlib MeasurableEmbedding.measurable_extend applied to the measurable embedding ι, the measurable map γ_D and the constant (measurable) map 0.

5. (Values on Φ(D).) Let w ∈ D. Then Φ(w) = ι(w), and since ι is injective, g(ι(w)) = γ_D(w) (Mathlib Function.Injective.extend_apply). Hence g(Φ(w)) = γ(w).

6. (Values off Φ(D).) Let y ∈ ℝ^P with y ∉ Φ(D). Then there is no w ∈ D with ι(w) = Φ(w) = y, so g(y) = 0 (Mathlib Function.extend_apply').

Steps 4, 5 and 6 prove the three claims. ∎

Lean remark. The following tactic proof was verified in the exact comparator scope (import GMT.Ch06.Submission, then the prefix replayed by verifier gmt-compare.contract_scope: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06 with the contract's three opens; noncomputable section followed by end) as `theorem Submission.slicing_im_tg_cg_borel_transfer : (<frozen statement>) := by`, with toolchain Lean v4.35.0-rc3 and Mathlib 25730c7c. Axioms: propext, Classical.choice, Quot.sound.
  intro n P Q Φ D γ hD hc hi hγ
  have hE := hc.measurableEmbedding hD hi
  refine ⟨Function.extend (D.domRestrict Φ) (D.domRestrict γ) 0,
    hE.measurable_extend (hγ.comp measurable_subtype_coe) measurable_const, ?_, ?_⟩
  · intro w hw
    exact hE.injective.extend_apply (D.domRestrict γ) 0 ⟨w, hw⟩
  · intro y hy
    rw [Function.extend_apply']
    · rfl
    rintro ⟨⟨w, hw⟩, hwy⟩
    exact hy ⟨w, hw, hwy⟩

## Key steps

1. Lusin–Souslin: the restriction ι = Φ|_D : D → ℝ^P is a measurable embedding (D Borel in the Polish space ℝⁿ, Φ continuous and injective on D).
2. The restriction γ_D = γ|_D is measurable.
3. g := Function.extend ι γ_D 0 is Borel (MeasurableEmbedding.measurable_extend).
4. g(Φ(w)) = γ(w) for w ∈ D by injectivity of ι, and g(y) = 0 for y ∉ ι(D) = Φ(D).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (all identical; git rev-parse HEAD = d8d46c9587747dee0751a1f780fcafdba16a3886)`
- `grep -rn 'slicing_im_tg_cg' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem measurable_fderiv\b|theorem measurable_fderiv_apply_const\b|theorem measurableSet_of_differentiableAt\b|theorem MeasurableSet.image_of_continuousOn_injOn|theorem ContinuousOn.measurableEmbedding|theorem MeasurableEmbedding.measurable_extend|theorem NormedRing.inverse_continuousAt|theorem ContinuousOn.measurable_piecewise|theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem|le_of_lip|theorem HasDerivAt.le_of_lipschitz' local-references/197bdd4b88278494/mathlib/Mathlib`
- `sed -n 330,400p Mathlib/Analysis/Calculus/FDeriv/Measurable.lean; sed -n 815,880p Mathlib/MeasureTheory/Constructions/Polish/Basic.lean; sed -n 515,535p Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean; sed -n 420,460p and grep 'def HasLineDerivAt' Mathlib/Analysis/Calculus/LineDeriv/Basic.lean (snapshot mathlib)`
- `lake env lean /tmp/cg_split_q7/Avail.lean: #check NormedRing.inverse_continuousAt, Continuous.measurable2, MeasurableEmbedding.measurable_extend, Function.Injective.extend_apply, Function.extend_apply', LipschitzWith.locallyLipschitz, LocallyLipschitz.locallyLipschitzOn, ContinuousLinearEquiv.funUnique, EuclideanSpace.equiv, ContinuousLinearMap.adjoint, adjoint_inner_left/right, InnerProductSpace.toDual, toDual_symm_apply, ContDiff.continuous_fderiv, measurable_fderiv, ContinuousOn.measurable_piecewise, HasLineDerivAt.le_of_lipschitz, LipschitzOnWith.ae_differentiableWithinAt_of_mem, injective_iff_map_eq_zero, ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective, isBoundedBilinearMap_apply, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ContinuousLinearEquiv.comp_differentiableAt_iff (all present; Measurable.clm_apply and ContinuousLinearMap.continuous_comp absent)`
- `python3 scans of dag.json: the tangential_gradient subtree (statuses and types of chart_cover, chart_gradient, chart_tangent, line_deriv); the lpf twins tangential_differential_exists, chart_chain_rule and weighted_tangent_on_c1_chart; lean_statements containing InjOn, Function.extend, inner ℝ, MeasurableEmbedding, adjoint or Ring.inverse; multi-parent and cross-branch child edges (53 multi-parent, 102 cross-branch); exact-type duplicates of the four child types; occurrences of the new names`
- `read nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json plus its scope, audit and receipt files, and nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json (reuse-child mechanism; rule that a solution PR proves only its tracked theorem)`
- `read the parent-child-handoff.json of nodes …-char-837491fcd9 (fderiv_lower_bound), …-tangential-differential-exists-a1-ch-34870e43f7 (chart_nondiff_image_null), …-tangential-gradient-a1-5d0f3ce1cd (line_deriv) and …-tangential-gradient-a1-661abdfbe7 (selected node)`
- `git show 8cfbc487a3d10545b0ea005ad58122242bbcc072 / 019ad40a7219b394f7e3a76a9361c778b6a98739 / 32fbf107157ca3b51c06f62670856410738101f5 -- GMT/Ch06/Submission.lean (accepted Lean proofs)`
- `python3: verifier/lean_contract.validate_lean_statement on the four child types; verifier/gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem')`
- `lake env lean /tmp/cg_split_q7/Stmts.lean, Assembly.lean, Final.lean, FinalFull.lean`
- `grep -c slicing_im_tg_cg_gram_field|slicing_im_tg_cg_borel_transfer in dag.json, DAG.md, dag.mmd, issue-workers.json, problem.json, nodes/, GMT/, lake-packages-25730c7c/simongmt/Poincare; git for-each-ref (1882 refs, no chart_gradient refs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-34870e43f7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-5d0f3ce1cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cg_split_q7/Stmts.lean`
- `/tmp/cg_split_q7/Avail.lean`
- `/tmp/cg_split_q7/Assembly.lean`
- `/tmp/cg_split_q7/Final.lean`
- `/tmp/cg_split_q7/FinalFull.lean`
- `/tmp/cg_split_q7/proposal.json`

Snapshot and scope:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) holds the frozen Ch06 contract. It is byte-identical to the workspace Contract.lean and Submission.lean.
- The child comparator scope is import GMT.Ch06.Submission plus the replayed prefix: opens, namespace GMT.Ch06, its three opens, then noncomputable section … end.
- No `slicing_im_tg_cg*` declaration exists in the snapshot project, the GMT sources, SimonGMT, dag.json (508 nodes) or any git ref.

Mathlib supplies every tool used by the new children and the assembly:
- measurable_fderiv and measurableSet_of_differentiableAt (FDeriv/Measurable.lean);
- MeasurableSet.image_of_continuousOn_injOn and ContinuousOn.measurableEmbedding, the latter producing s.domRestrict f (Polish/Basic.lean);
- ContinuousOn.measurable_piecewise and Continuous.measurable2 (BorelSpace/Basic.lean);
- MeasurableEmbedding.measurable_extend;
- NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint with adjoint_inner_left, and InnerProductSpace.toDual_symm_apply;
- ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective and isBoundedBilinearMap_apply;
- HasLineDerivAt.le_of_lipschitz (LineDeriv/Basic.lean), which reduces the parent's Step 8 to a single line;
- ContinuousLinearEquiv.comp_differentiableAt_iff and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.

DAG and reuse:
- Steps 1 and 2–3 are already comparator-accepted as lpf_wtc_cat_fderiv_lower_bound (candidate 8cfbc487) and lpf_tde_chart_nondiff_image_null (candidate 019ad40a). Both are reused with byte-identical types; cross-branch reuse is established in this DAG (102 edges).
- No accepted or active node has the type of gram_field or borel_transfer. lpf_tde_mcd_single_chart differs: it gives an operator-valued field with no range condition.

Kernel checks:
- All four child types pass validate_lean_statement and elaborate in the exact scope.
- Both new children are fully proved with standard axioms.
- The frozen parent type is proved from the four children and line_deriv. With the accepted proofs substituted, every declaration depends only on propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced these checks with its own assembly and returned ACCEPT.
