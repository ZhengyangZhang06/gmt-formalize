# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (the area formula on the chart, extended from nonnegative to signed integrands). Here F is any Banach-valued integrable function, which covers the real integrands of steps 8–9 and the vector field Y of step 8. The parent splits a real F into positive and negative parts; for Banach-valued F the same step is done once for the measures (step 4 below). Notation as in the statement; JΦ ≥ 0 because it is a square root.
1. (The nonnegative formula.) Apply the sibling chart_change_of_variables (lpf_raf_chart_change_of_variables) to the same Φ, Ω, A. For every g : ℝ^P → [0, ∞] that is Hⁿ⌞A-a.e. measurable: D is Lⁿ-null-measurable, g∘Φ is Lⁿ⌞D-a.e. measurable, and ∫⁻_A g dHⁿ = ∫⁻_D g(Φ(w))·ofReal(JΦ(w)) dw. With g = 0 this already gives the first conclusion: D is Lⁿ-null-measurable.
2. (JΦ is Borel.) w ↦ DΦ(w) is Borel measurable for every map Φ (Mathlib `measurable_fderiv`). The map Λ ↦ √det(⟨Λe_i, Λe_j⟩)_{i,j} is continuous on the space of linear maps ℝⁿ → ℝ^P: the entries are continuous, det is a polynomial and √ is continuous (`fun_prop` proves it). So JΦ is Borel, and so is w ↦ JΦ(w).toNNReal.
3. (A measure on the parameter side.) Let ρ := Lⁿ⌞D with density ofReal∘JΦ (Mathlib `withDensity` with density w ↦ ↑(JΦ(w).toNNReal), which is ofReal(JΦ(w)) by definition). Φ is continuous on Ω (it is Lipschitz there) and Ω is open, so Φ is Lⁿ⌞Ω-a.e. measurable (`ContinuousOn.aemeasurable`). Since D ⊆ Ω (`Measure.restrict_mono`), Φ is Lⁿ⌞D-a.e. measurable. Since ρ ≪ Lⁿ⌞D (`withDensity_absolutelyContinuous`), Φ is ρ-a.e. measurable.
4. (Φ pushes ρ forward to Hⁿ⌞A.) Let S ⊆ ℝ^P be Borel. Then:
(Φ_#ρ)(S) = ρ(Φ⁻¹(S)) (`Measure.map_apply_of_aemeasurable`)
= ∫⁻_{Φ⁻¹(S)} ofReal(JΦ) d(Lⁿ⌞D) (`withDensity_apply'`; Lⁿ⌞D is s-finite)
= ∫⁻_D 1_S(Φ(w))·ofReal(JΦ(w)) dw (`lintegral_indicator₀`; Φ⁻¹(S) is Lⁿ⌞D-null-measurable by step 3, and 1_{Φ⁻¹(S)}·ofReal(JΦ) = (1_S∘Φ)·ofReal(JΦ) pointwise)
= ∫⁻_A 1_S dHⁿ (step 1 with the Borel function g = 1_S)
= Hⁿ(S ∩ A) = (Hⁿ⌞A)(S).
Two measures that agree on all Borel sets are equal, so Φ_#ρ = Hⁿ⌞A.
5. (Transfer of integrability and integral.) F is Hⁿ⌞A-integrable, i.e. Φ_#ρ-integrable. Φ is ρ-a.e. measurable and F is Φ_#ρ-a.e. strongly measurable. Hence F∘Φ is ρ-integrable (`integrable_map_measure`), and ∫_A F dHⁿ = ∫ F d(Φ_#ρ) = ∫ F(Φ(w)) dρ(w) (`integral_map`).
6. (Removing the density.) Let f := JΦ.toNNReal : ℝⁿ → [0, ∞), which is Borel. For any G : ℝⁿ → E: G is ρ-integrable iff w ↦ f(w)·G(w) is Lⁿ⌞D-integrable (`integrable_withDensity_iff_integrable_smul`), and ∫ G dρ = ∫_D f(w)·G(w) dw (`integral_withDensity_eq_integral_smul`). Because JΦ ≥ 0, f(w) = JΦ(w) as real numbers (`Real.coe_toNNReal`), so f(w)·G(w) = JΦ(w)·G(w) (`NNReal.smul_def`). Take G := F∘Φ. With step 5, w ↦ JΦ(w)·F(Φ(w)) is Lⁿ-integrable on D and ∫_A F dHⁿ = ∫_D JΦ(w)·F(Φ(w)) dw. ∎

## Key steps

1. chart_change_of_variables: D is null-measurable, and ∫⁻_A g dHⁿ = ∫⁻_D (g∘Φ)·JΦ dLⁿ for every measurable g ≥ 0.
2. JΦ is Borel (measurable fderiv composed with the continuous Gram-determinant map) and nonnegative.
3. With ρ := JΦ·Lⁿ⌞D, Φ is ρ-a.e. measurable and Φ_#ρ = Hⁿ⌞A (test on Borel sets with g = 1_S).
4. integral_map and integrable_map_measure transfer F to F∘Φ under ρ.
5. integral_withDensity_eq_integral_smul and integrable_withDensity_iff_integrable_smul turn ρ back into JΦ·Lⁿ⌞D.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read GMT/Ch06/Contract.lean (IsRectifiableTriple fields subset, nullMeasurableSet, countablyRectifiable, pos, integrableOn, orients) and verifier/gmt-compare.py contract_scope/child_modules (child challenge = import GMT.Ch06.Submission + replayed namespace GMT.Ch06 scope, solution = exact Submission.X)`
- `python3 scan of dag.json (554 nodes; rechecked at 572 nodes before submission): status/candidate_commit/lean_statement of lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart, lpf_raf_chart_change_of_variables, lpf_ccr_ae_pullback, lpf_tde_continuous_left_inverse, lpf_wtc_cat_fderiv_lower_bound (all accepted), lpf_chart_chain_rule, lpf_ccr_hasDerivAt_line_of_comp, lpf_tde_chart_directional_deriv, lpf_raf_chart_preimage_null, lpf_wtc_chart_image_measurable_locally_finite, lpf_wtc_cat_gram_jacobian_continuous (accepted, not needed), slicing_im_ll_gradient_weak_star (decomposing, parent-level dependency)`
- `read the six reused nodes' parent-child-handoff.json (subproblem key/natural_proof/proof_key_steps) and compare title/statement/lean_statement with dag.json (byte-identical)`
- `collision check: python3 over dag.json lean_name/lean_statement and rg 'slicing_im_ll_twl' in the snapshot and lake-packages-25730c7c/simongmt (no match)`
- `git show d38f8d26:GMT/Ch06/Submission.lean (proof base = bare contract, no lpf declarations); git show <candidate>:GMT/Ch06/Submission.lean for the six reused candidates (declarations, imports); git merge-base --is-ancestor checks`
- `union-merge simulation of the six reused candidate commits on d38f8d26 in a git clone --shared temp copy (git merge + git merge-file --union, as in the controller's _union_lean_conflicts)`
- `grep snapshot Mathlib: LipschitzOnWith.ae_differentiableWithinAt_of_mem (Analysis/Calculus/Rademacher.lean), tendsto_tsum_of_dominated_convergence (Analysis/Normed/Group/Tannery.lean, not in import closure), hasSum_integral_iUnion, measurable_fderiv, integral_withDensity_eq_integral_smul, integrable_withDensity_iff_integrable_smul, withDensity_apply', Measure.map_apply_of_aemeasurable, integral_map, integrable_map_measure, MeasurableSet.image_of_continuousOn_injOn, disjointed/iUnion_disjointed/disjoint_disjointed, integrable_indicator_iff₀, ContinuousLinearMap.aestronglyMeasurable_comp₂, AEStronglyMeasurable.inner (StronglyMeasurable/Inner.lean, not imported; continuous_inner.comp_aestronglyMeasurable₂ used instead)`
- `read SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt.unique)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/twl_split/check/Stmts.lean (13 types: 5 new, 6 reused, gradient_weak_star, parent; no errors)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/twl_split/check/AssemblyParent.lean (parent type from partition_tendsto, chart_representation, R1, R2, gradient_weak_star types; axioms propext, Classical.choice, Quot.sound)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/twl_split/check/AssemblyT.lean, AssemblyCV.lean, AssemblyCF.lean, AssemblyDI.lean, AssemblyCR.lean (each new child from its declared dependencies' exact types; same axioms)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/twl_split/check/Integrated.lean (union of the six reused candidates + five new children + parent, gradient_weak_star stubbed; EXIT 0; new children axioms propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/twl_split/check/Stmts.lean`
- `/tmp/twl_split/check/AssemblyParent.lean`
- `/tmp/twl_split/check/AssemblyT.lean`
- `/tmp/twl_split/check/AssemblyCV.lean`
- `/tmp/twl_split/check/AssemblyCF.lean`
- `/tmp/twl_split/check/AssemblyDI.lean`
- `/tmp/twl_split/check/AssemblyCR.lean`
- `/tmp/twl_split/check/Integrated.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract, so child types use only contract, SimonGMT and Mathlib names. All 13 relevant types elaborate in the exact comparator scope. The proof base d38f8d26 is the bare contract, so accepted lpf declarations can only be used as reused children. Six accepted declarations have exactly the types this proof needs: lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (both speculative when the handoff was written, accepted now), lpf_raf_chart_change_of_variables, lpf_ccr_ae_pullback, lpf_tde_continuous_left_inverse and lpf_wtc_cat_fderiv_lower_bound. They are reused byte-for-byte. No library has the Bochner chart area formula, the coefficient-field lift, the a.e. chart differential of a Lipschitz function with tangential gradient, or the partition/Tannery convergence lemma; these are the five new children. Mathlib supplies Rademacher on sets, countable additivity of the integral, withDensity/map integral transfer, measurable fderiv and Lusin–Souslin images. Tannery's file is outside the import closure, so its proof is inlined. Scratch Lean proves the parent type from the child types plus gradient_weak_star, and each new child from exactly its declared dependencies. A union-merge of the six reused candidates, together with all new children and the parent, compiles. Axioms are propext, Classical.choice, Quot.sound (sorryAx only from the gradient_weak_star stub). No new name occurs in the DAG, the snapshot or SimonGMT.
