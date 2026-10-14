# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.mass_measure_rectifiable-a1`
- Child DAG node: `root.rectifiability-a1.mass_measure_rectifiable-a1.rn_positive_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, proof of Theorem 8.1, display (8) (p. 174), in the form of steps 5-7 of the selected parent's proof. ν stands in for Hⁿ and B for the Borel carrier B₀. The integrability of step 7 is recorded for every measurable K of finite μ-measure. The Radon-Nikodym theorem is used in its abstract σ-finite form (the form recalled before Simon Ch. 1, 3.24).

Notation. For a measurable E ⊆ X, ν⌞E := ν.restrict E. It satisfies ν⌞E(A) = ν(A ∩ E) for every A ⊆ X (Measure.restrict_apply'). For a measure λ on X and any f : X → [0, ∞], λ.withDensity(f)(A) = ∫_A f dλ for every measurable A (withDensity_apply). For r ∈ ℝ with r ≥ 0, ‖r‖ₑ = ofReal(r) (Real.enorm_of_nonneg). 'λ-a.e.' means outside a λ-null set.

1. μ ≪ λ, where λ := ν⌞B. By Measure.AbsolutelyContinuous.mk it suffices to treat measurable s with λ(s) = 0, i.e. ν(s ∩ B) = 0. Then μ(s ∩ B) = 0 because μ ≪ ν. Also μ(s ∖ B) ≤ μ(X ∖ B) = 0. Since s ⊆ (s ∩ B) ∪ (s ∖ B), we get μ(s) ≤ μ(s ∩ B) + μ(s ∖ B) = 0.

2. Radon-Nikodym. λ is σ-finite and μ is σ-finite, so the pair (μ, λ) has a Lebesgue decomposition (Mathlib instance Measure.haveLebesgueDecomposition_of_sigmaFinite). Let h := μ.rnDeriv λ : X → [0, ∞]; it is measurable (Measure.measurable_rnDeriv). The decomposition reads μ = μ.singularPart(λ) + λ.withDensity(h) (Measure.haveLebesgueDecomposition_add). Since μ ≪ λ, the singular part is 0 (Measure.singularPart_eq_zero_of_ac), so μ = λ.withDensity(h). This is Measure.withDensity_rnDeriv_eq. That lemma lives in Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean, which may be imported; the two lemmas above are already available after the frozen imports. Since μ is σ-finite, h(x) < ∞ for λ-a.e. x (Measure.rnDeriv_lt_top).

3. M and θ. Put M := B ∩ {x : 0 < h(x)} ∩ {x : h(x) < ∞} and θ(x) := (h(x)).toReal for x ∈ X. M is measurable because B and h are measurable (measurableSet_lt). Clearly M ⊆ B. θ is measurable (Measurable.ennreal_toReal) and θ ≥ 0 everywhere. For x ∈ M we have 0 < h(x) < ∞, so θ(x) > 0 (ENNReal.toReal_pos).

4. h = 1_M·g λ-a.e., where g(x) := ofReal(θ(x)) and 1_M·g is the indicator of M applied to g. λ-a.e. x satisfies both x ∈ B (ae_restrict_mem, since B is measurable) and h(x) < ∞ (step 2). Fix such an x. If h(x) > 0, then x ∈ M and g(x) = ofReal(h(x).toReal) = h(x), because h(x) ≠ ∞ (ENNReal.ofReal_toReal). If h(x) = 0, then x ∉ M and both sides are 0.

5. The representation. By steps 2 and 4 and withDensity_congr_ae, μ = λ.withDensity(h) = λ.withDensity(1_M·g). Since M is measurable, λ.withDensity(1_M·g) = (λ⌞M).withDensity(g) (withDensity_indicator). Finally λ⌞M = (ν⌞B)⌞M = ν⌞(M ∩ B) (Measure.restrict_restrict), and M ∩ B = M because M ⊆ B. Hence μ = (ν⌞M).withDensity(x ↦ ofReal θ(x)).

6. Integrability. Let K ⊆ X be measurable with μ(K) < ∞. θ is measurable, hence a.e.-strongly measurable for ν⌞(M ∩ K). Since θ ≥ 0, ‖θ(x)‖ₑ = g(x) for all x. Using (ν⌞M)⌞K = ν⌞(K ∩ M) = ν⌞(M ∩ K) (Measure.restrict_restrict), the formula of step 5 and withDensity_apply for the measurable K:
∫_{M∩K} ‖θ‖ₑ dν = ∫_K g d(ν⌞M) = (ν⌞M).withDensity(g)(K) = μ(K) < ∞.
So θ has a finite integral on M ∩ K. Together with measurability this is IntegrableOn θ (M ∩ K) ν. ∎

## Key steps

1. μ ≪ ν⌞B, from μ ≪ ν and μ(X ∖ B) = 0.
2. Lebesgue decomposition for the σ-finite pair (μ, ν⌞B) with zero singular part: μ = (ν⌞B).withDensity(h), h := μ.rnDeriv(ν⌞B) measurable, and h < ∞ (ν⌞B)-a.e. because μ is σ-finite.
3. M := B ∩ {0 < h < ∞} and θ := h.toReal: M and θ measurable, M ⊆ B, θ ≥ 0, θ > 0 on M.
4. h = 1_M·ofReal(θ) (ν⌞B)-a.e.; withDensity_indicator and restrict_restrict give μ = (ν⌞M).withDensity(ofReal ∘ θ).
5. For measurable K with μ(K) < ∞: ∫_{M∩K} |θ| dν = μ(K) < ∞, so θ is ν-integrable on M ∩ K.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean <git show d8d46c95:GMT/Ch06/Submission.lean> (identical; sha256 ea3ee0ddd08be5db60dced2b002e9f60fd87091910069abcfcbd7e34db89853d), then private lean -o build of that frozen Submission`
- `grep -rn 'measurable_rectifiable_purelyUnrectifiable_decomposition|sigmaFinite_restrict_of_hausdorff_finite_cover|def PurelyUnrectifiable|def CountablyRectifiable|notation.*μHE|def dimensionalUpperDensity' simongmt/Poincare/SimonGMT and mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn 'theorem withDensity_rnDeriv_eq|theorem sigmaFinite_of_countable|theorem rnDeriv_lt_top' local-references/197bdd4b88278494/mathlib/Mathlib`
- `grep -n 'singularPart_eq_zero_of_ac|haveLebesgueDecomposition_add|haveLebesgueDecomposition_of_sigmaFinite' local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `grep -n 'OuterRegular|WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure' local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `lean probe/Names.lean and probe/Names2.lean (#check of every cited Mathlib/SimonGMT name after import GMT.Ch06.Submission, plus instance checks OuterRegular / HaveLebesgueDecomposition / BorelSpace on Eucl P)`
- `python3 scan of dag.json for reusable accepted declarations (exhaustion, density comparison, statements mentioning withDensity/rnDeriv/SigmaFinite)`
- `python3 scan of lean_names in dag.json and nodes/*/decomposition-v*.json (456 distinct names, 266 nodes) and git log --all -S for the two new names (no match)`
- `sed -n 2130,2305p book/chapter-06.txt (Simon Ch. 6, 8.1 and its printed proof, displays (1)-(8))`
- `git show cb89cc7f436bbfa9b474f73003fa9aa79ebad102:GMT/Ch06/Submission.lean and git show c5336e1a14131119b486a9306a19dac19728d9fb:GMT/Ch06/Submission.lean (accepted proofs of the reused declarations)`
- `python3 -I gen_challenges.py (verifier gmt-compare.py contract_scope/child_modules) and lean on the four generated NodeChallenge files`
- `lean assembly/Assembly.lean; lean combined/Combined.lean (#print axioms); lean children/ChildB.lean, children/ChildC.lean, children/ChildC_noimport.lean`
- `grep -n 'existing_by_name|_existing_lean_name_problem|_install_parent_supplied_child_handoff|_accepted_checkpoint' /runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py (reuse semantics); python3 recomputation of parent_contract_digest via decomposition_scope.scope`
- `WebSearch: Mattila Geometry of Sets and Measures in Euclidean Spaces, Ch. 6 density theorems (citation check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-exhaustion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-projection-null-ae-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/decomposition_scope.py`
- `/tmp/mmr_decomp_scratch/challenge/exhaustion_Challenge.lean`
- `/tmp/mmr_decomp_scratch/challenge/density_comparison_Challenge.lean`
- `/tmp/mmr_decomp_scratch/challenge/positive_density_cover_null_Challenge.lean`
- `/tmp/mmr_decomp_scratch/challenge/rn_positive_density_Challenge.lean`
- `/tmp/mmr_decomp_scratch/assembly/Assembly.lean`
- `/tmp/mmr_decomp_scratch/children/ChildB.lean`
- `/tmp/mmr_decomp_scratch/children/ChildC.lean`
- `/tmp/mmr_decomp_scratch/children/ChildC_noimport.lean`
- `/tmp/mmr_decomp_scratch/combined/Combined.lean`
- `/tmp/mmr_decomp_scratch/probe/Names.lean`
- `/tmp/mmr_decomp_scratch/probe/Names2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the frozen Submission used for all checks. Library facts. SimonGMT provides measurable_rectifiable_purelyUnrectifiable_decomposition, sigmaFinite_restrict_of_hausdorff_finite_cover, countablyRectifiable_iUnion/of_measure_zero/mono (Chapter03/Rectifiable.lean) and dimensionalUpperDensity (Chapter01/Densities.lean). Mathlib provides, under the frozen imports: Measure.rnDeriv_lt_top, measurable_rnDeriv, haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac and the instance haveLebesgueDecomposition_of_sigmaFinite (Lebesgue.lean); Measure.sigmaFinite_of_countable (SFinite.lean); Set.exists_isOpen_lt_of_lt with the OuterRegular instance for finite measures (Regular.lean); and withDensity_indicator, withDensity_congr_ae and withDensity_apply. Measure.withDensity_rnDeriv_eq (RadonNikodym.lean) is not in the frozen import closure; the rn child's proof names the import-free route, which compiles. Reuse. No existing DAG declaration covers the positive-density lemma or the positive-real-density Radon-Nikodym statement. Two accepted declarations are reused with byte-identical types, titles and statements: cmb_exists_compactly_contained_exhaustion (cb89cc7f) and rectifiability_density_comparison (c5336e1a). The controller resolves accepted checkpoints by name and skips their handoffs; the bf_projection_null_ae decomposition is a precedent for cross-branch reuse. The new names collide with nothing. Lean checks. All four child types elaborate in the comparator's exact child scope. One file compiled the accepted proofs of the reused declarations, Lean proofs of both new children and the parent assembly. All four children depend only on [propext, Classical.choice, Quot.sound]; the parent's only sorryAx comes from stubs for its three not-yet-accepted dependencies (projection_null, mass_measure_abs_continuous, structure_projection). Simon's printed proof of 8.1 (book chapter-06.txt) matches the supplied steps: (1) and (6) go to positive_density_cover_null, (8) to rn_positive_density.
