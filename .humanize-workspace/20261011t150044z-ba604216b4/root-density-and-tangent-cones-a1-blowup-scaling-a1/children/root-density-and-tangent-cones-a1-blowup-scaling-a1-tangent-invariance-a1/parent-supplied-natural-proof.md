# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1.tangent_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, Definition 1.4 (chapter-03.txt lines 77–86), formalized by SimonGMT HasApproximateTangentSpaceAt n M y Q := finrank Q = n ∧ ∀ f ∈ C_c(ℝ^P;ℝ), lim_{r→0+} ∫_{blowUpMap y r '' M} f dHⁿ = ∫_Q f dHⁿ, with blowUpMap y r w = r⁻¹•(w − y); parent proof step 2, orientation bullet (η_{z,r}(η(M)) = η_{y,λr}(M)). Here η = η_{x,λ} = dilation x λ, Hⁿ = μHE[n].
1. The condition finrank Q = n involves neither M nor the base point, so it holds for η(M) at η(y).
2. Set identity. For w ∈ ℝ^P, η(w) − η(y) = (−λ⁻¹x + λ⁻¹w) − (−λ⁻¹x + λ⁻¹y) = λ⁻¹(w − y). Hence for every r ∈ ℝ, blowUpMap(η(y), r)(η(w)) = r⁻¹λ⁻¹(w − y) = (λr)⁻¹(w − y) = blowUpMap(y, λr)(w), using (λr)⁻¹ = λ⁻¹r⁻¹ (valid in ℝ with the convention 0⁻¹ = 0). Taking images of M: blowUpMap(η(y), r)(η(M)) = blowUpMap(y, λr)(M) for all r.
3. Fix f ∈ C_c(ℝ^P;ℝ) and put g(s) := ∫_{blowUpMap(y,s)(M)} f dHⁿ. By step 2, for every r the integral ∫_{blowUpMap(η(y),r)(η(M))} f dHⁿ is literally g(λr) (same domain of integration, same integrand and same measure, so no integrability is needed for this identity).
4. The map r ↦ λr sends the filter r → 0+ into the filter s → 0+: it is continuous with value 0 at 0, and λr > 0 whenever r > 0 because λ > 0. By hypothesis g(s) → ∫_Q f dHⁿ as s → 0+. Composing the two limits, ∫_{blowUpMap(η(y),r)(η(M))} f dHⁿ = g(λr) → ∫_Q f dHⁿ as r → 0+.
5. Steps 1 and 4 are exactly HasApproximateTangentSpaceAt n (η(M)) (η(y)) Q. ∎
Formalization notes (this exact statement was proved in a scratch build): obtain ⟨hdim, hconv⟩; prove the set identity with image_image, congr, funext and the rewrite chain ← smul_sub, smul_smul, mul_inv, mul_comm, sub_sub_sub_cancel_right (after writing dilation x λ y = λ⁻¹ • (y − x)); simp_rw it; the filter limit by tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within with mul_pos; conclude with (hconv f).comp.

## Key steps

1. η(w) − η(y) = λ⁻¹(w − y), hence η_{η(y),r}(η(M)) = η_{y,λr}(M) for every r.
2. The rescaled integrals for η(M) at η(y) at scale r equal those for M at y at scale λr.
3. r ↦ λr maps r → 0+ to s → 0+, so the limit transfers; dim Q = n is unchanged.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (both identical; manifest project b4d606d, mathlib 25730c7c)`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|theorem Isometry.euclideanHausdorffMeasure_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem restrict_map \(μ|theorem ae_map_iff \{p' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'MeasurableEmbedding.lintegral_map|MeasurableEmbedding.integral_map |MeasurableEmbedding.aestronglyMeasurable_map_iff' mathlib/Mathlib`
- `rg -n 'theorem map_smul_univ' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean; rg -n 'comp_homeomorph' mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n 'theorem preimage_closure|theorem image_closure' mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `grep -n '^def\|^theorem' simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Mass,CurrentLocalEquality,Currents,Forms}.lean simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (affinePullbackForm, affinePushforward_apply, boundary_affinePushforward, exteriorDerivative_affinePullbackForm, massOn, massAdmissibleOn, restrictDomain_apply, zeroRegion, support, CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap)`
- `grep -rl -F <each proposed lean_name> runs/20261011T150044Z-ba604216b4 (no match) and lean_name inventory of dag.json and all node JSON files (no collision)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all eight child types`
- `lake build GMT.Ch07.Submission; lake env lean Check/FinalExact.lean, Check/FinalAssembly.lean, Check/FinalLeaves.lean with #print axioms (scratch /tmp/bscale-decomp-6cU90O/proj)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalExact.lean`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalAssembly.lean`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalLeaves.lean`

The snapshot contract and submission (project b4d606d, mathlib 25730c7c) are byte-identical to the workspace files. SimonGMT supplies the objects the children reason about: blowUp is an affinePushforward of a restrictDomain; affinePullbackForm comes with affinePushforward_apply, boundary_affinePushforward and exteriorDerivative_affinePullbackForm (used for blowup_structure (iv)); massOn/massAdmissibleOn (mass_scaling); zeroRegion/support/VanishesOn (blowup_structure (iii)); CountablyRectifiable and HasApproximateTangentSpaceAt via blowUpMap (rep_pushforward, tangent_invariance). It contains no dilation or blow-up lemmas, so the children supply them. The pinned Mathlib supplies the measure-theoretic and multilinear ingredients: euclideanHausdorffMeasure_smul₀ and Isometry.euclideanHausdorffMeasure_image (hausdorff_scaling); MeasurableEmbedding.restrict_map, lintegral_map, integral_map, ae_map_iff and aestronglyMeasurable_map_iff (rep_pushforward); ContinuousAlternatingMap.map_smul_univ and HasCompactSupport.comp_homeomorph (testform_correspondence); Homeomorph.preimage_closure and image_closure (blowup_structure, minimality). All eight child types elaborate in the comparator scope. Scratch Lean proofs of every child, and of the parent from the children, compile using only propext, Classical.choice and Quot.sound. No proposed name occurs elsewhere in the run.
