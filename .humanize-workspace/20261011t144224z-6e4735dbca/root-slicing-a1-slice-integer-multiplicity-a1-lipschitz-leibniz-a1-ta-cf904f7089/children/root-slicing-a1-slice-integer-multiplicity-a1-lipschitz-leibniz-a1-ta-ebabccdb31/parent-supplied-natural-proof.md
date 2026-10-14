# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the parent proof, items (9a) and (9b): rewrite ∫_{M_j} F_k and ∫_{M_j} F_∞ as parameter integrals against the coefficient field. Steps 5, 7 and 8 of the parent are supplied by the three siblings. Notation: D := Ω ∩ Φ⁻¹(A), A_w := DΦ(w), JΦ(w) := √det(⟨A_w e_i, A_w e_j⟩)_{i,j<n}. Φ is C¹, hence differentiable everywhere.
1. (Coefficient field.) Apply the sibling coefficient_field with the first half of the a.e. hypothesis (Y(x) ∈ range A_w). It gives c : ℝⁿ → ℝⁿ, Lⁿ-integrable on Ω, with c(w) = 0 for w ∉ D and A_w c(w) = JΦ(w)·Y(Φ(w)) for Lⁿ-a.e. w ∈ D. This c is the field in the conclusion.
2. (Differential of h∘Φ.) Apply the sibling chart_has_fderiv_at with the second half of the a.e. hypothesis. It gives: for Lⁿ-a.e. w ∈ D, h∘Φ has Fréchet derivative v ↦ ⟨G(Φ(w)), A_w v⟩ at w. In particular D(h∘Φ)(w)v = ⟨G(Φ(w)), A_w v⟩ (`HasFDerivAt.fderiv`).
3. (Integrals over Ω reduce to D.) For any u : ℝⁿ → ℝ and w ∈ Ω ∖ D we have c(w) = 0, so Du(w)(c(w)) = 0. Since Ω is measurable and D ⊆ Ω, ∫_Ω Du(w)(c(w)) dw = ∫_D Du(w)(c(w)) dw (`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`; no integrability is needed).
4. (Identity (i).) Let f be differentiable and K-Lipschitz, and put F(x) := Df(x)(Y(x)). F is Hⁿ⌞A-integrable:
- x ↦ Df(x) is Borel (`measurable_fderiv`), Y is Hⁿ⌞A-a.e. strongly measurable, and evaluation is continuous bilinear, so F is a.e. strongly measurable;
- |F(x)| ≤ ‖Df(x)‖·|Y(x)| ≤ K|Y(x)| (`norm_fderiv_le_of_lipschitz`), and K|Y| is integrable on A.
The sibling chart_integral_eq with E := ℝ gives ∫_A F dHⁿ = ∫_D JΦ(w)·F(Φ(w)) dw. For Lⁿ-a.e. w ∈ D (step 1), the chain rule (`fderiv_comp`; f is differentiable at Φ(w) and Φ at w) gives
D(f∘Φ)(w)(c(w)) = Df(Φ(w))(A_w c(w)) = Df(Φ(w))(JΦ(w)·Y(Φ(w))) = JΦ(w)·F(Φ(w)).
Hence ∫_D D(f∘Φ)(c) dLⁿ = ∫_D JΦ·(F∘Φ) dLⁿ (`integral_congr_ae`). With step 3, ∫_Ω D(f∘Φ)(w)(c(w)) dw = ∫_A F dHⁿ.
5. (Identity (ii).) Put F(x) := ⟨G(x), Y(x)⟩. F is Hⁿ⌞A-integrable: G is Borel, Y is a.e. strongly measurable and the inner product is continuous (`continuous_inner.comp_aestronglyMeasurable₂`); and |F| ≤ |G|·|Y| ≤ L|Y|. chart_integral_eq gives ∫_A F dHⁿ = ∫_D JΦ(w)·F(Φ(w)) dw. For Lⁿ-a.e. w ∈ D (steps 1 and 2),
D(h∘Φ)(w)(c(w)) = ⟨G(Φ(w)), A_w c(w)⟩ = ⟨G(Φ(w)), JΦ(w)·Y(Φ(w))⟩ = JΦ(w)·F(Φ(w)).
With step 3, ∫_Ω D(h∘Φ)(w)(c(w)) dw = ∫_D JΦ·(F∘Φ) dLⁿ = ∫_A ⟨G, Y⟩ dHⁿ. ∎

## Key steps

1. coefficient_field gives c integrable on Ω, c = 0 off D = Ω ∩ Φ⁻¹(A), and DΦ(w)c(w) = JΦ(w)Y(Φ(w)) a.e. on D.
2. chart_has_fderiv_at gives D(h∘Φ)(w) = ⟨G(Φ(w)), DΦ(w)·⟩ a.e. on D.
3. ∫_Ω Du(c) = ∫_D Du(c) because c = 0 on Ω ∖ D.
4. Chain rule: a.e. on D, D(f∘Φ)(w)(c(w)) = JΦ(w)·Df(Φ(w))(Y(Φ(w))) and D(h∘Φ)(w)(c(w)) = JΦ(w)·⟨G, Y⟩(Φ(w)).
5. chart_integral_eq (E = ℝ) turns ∫_D JΦ·(F∘Φ) back into ∫_A F dHⁿ for F = Df(Y) and F = ⟨G, Y⟩; both are dominated by a constant times |Y|.

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
