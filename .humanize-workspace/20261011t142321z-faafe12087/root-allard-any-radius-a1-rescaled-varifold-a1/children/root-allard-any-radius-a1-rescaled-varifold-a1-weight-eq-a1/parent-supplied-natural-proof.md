# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.rescaled_varifold-a1`
- Child DAG node: `root.allard_any_radius-a1.rescaled_varifold-a1.weight_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: ℝ^{n+ℓ} = Amb n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)); H^n = μHE[n] is Mathlib's Euclidean Hausdorff measure on ℝ^{n+ℓ}; for c ∈ ℝ^{n+ℓ} and R > 0, ψ(x) := c + R x and φ(y) := R⁻¹(y − c); κ := (ENNReal.ofReal (R^n))⁻¹, i.e. R^{-n} as an element of [0, ∞]. This is step 3 of the parent proof.
1. Maps. ψ is a homeomorphism (x ↦ R x via Homeomorph.smulOfNeZero R, then z ↦ c + z via Homeomorph.addLeft c), hence a measurable embedding. φ is continuous, hence measurable. For every x, φ(ψ(x)) = R⁻¹ (c + R x − c) = R⁻¹ R x = x.
2. Change of variables. For every set S ⊆ ℝ^{n+ℓ} and every g : ℝ^{n+ℓ} → [0, ∞]: ∫⁻_{ψ⁻¹(S)} g(ψ(x)) dH^n(x) = κ · ∫⁻_S g dH^n. Proof: by MeasurableEmbedding.restrict_map, (Measure.map ψ H^n)⌞S = Measure.map ψ (H^n⌞ψ⁻¹(S)), and by MeasurableEmbedding.lintegral_map, ∫⁻ g d(Measure.map ψ (H^n⌞ψ⁻¹(S))) = ∫⁻_{ψ⁻¹(S)} g ∘ ψ dH^n. On the other hand the sibling lemma map_hausdorff gives Measure.map ψ H^n = κ • H^n, so (Measure.map ψ H^n)⌞S = κ • (H^n⌞S) (Measure.restrict_smul) and ∫⁻ g d(κ • (H^n⌞S)) = κ · ∫⁻_S g dH^n (lintegral_smul_measure).
3. Left side on a measurable set. Fix a measurable set A. By withDensity_apply (A measurable) and Measure.restrict_restrict (A measurable): W.weight(A) = ∫⁻_{A ∩ W.carrier} ofReal(W.mult(x)) dH^n(x).
4. Right side on A. φ⁻¹(A) is measurable. By Measure.smul_apply and Measure.map_apply (φ measurable, A measurable): (κ • Measure.map φ V.weight)(A) = κ · V.weight(φ⁻¹(A)) = κ · ∫⁻_{φ⁻¹(A) ∩ M} ofReal(θ(y)) dH^n(y) (withDensity_apply and Measure.restrict_restrict for the measurable set φ⁻¹(A)).
5. Set identity. A ∩ W.carrier = ψ⁻¹(φ⁻¹(A) ∩ M): indeed W.carrier = ψ⁻¹(M), ψ⁻¹(φ⁻¹(A)) = (φ ∘ ψ)⁻¹(A) = A by step 1, and preimages commute with intersections (preimage_inter). Also ofReal(W.mult(x)) = ofReal(θ(ψ(x))) for every x.
6. Conclusion on A. W.weight(A) = ∫⁻_{ψ⁻¹(φ⁻¹(A) ∩ M)} ofReal(θ(ψ(x))) dH^n(x) = κ · ∫⁻_{φ⁻¹(A) ∩ M} ofReal(θ(y)) dH^n(y) (step 2 with S := φ⁻¹(A) ∩ M and g := ofReal ∘ θ) = (κ • Measure.map φ V.weight)(A) (step 4).
7. Two measures that agree on every measurable set are equal (Measure.ext). Hence W.weight = (ENNReal.ofReal (R^n))⁻¹ • Measure.map φ V.weight.

## Key steps

1. ψ measurable embedding, φ measurable, φ ∘ ψ = id
2. change of variables ∫⁻_{ψ⁻¹S} g∘ψ dH^n = κ ∫⁻_S g dH^n from restrict_map, lintegral_map and the sibling map_hausdorff
3. both sides on measurable A via withDensity_apply, restrict_restrict, map_apply
4. A ∩ ψ⁻¹M = ψ⁻¹(φ⁻¹A ∩ M) and W.mult = θ ∘ ψ
5. Measure.ext

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|theorem Isometry.euclideanHausdorffMeasure_preimage' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `sed -n 55,175p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 750,762p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'support_map|support_smul' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean (no match); rg -n 'lemma mem_support_iff_forall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'nonrec theorem map_apply \(hf : MeasurableEmbedding|theorem restrict_map \(μ : Measure α\) \(s : Set β\)' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Map.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem integral_smul_measure|theorem lintegral_smul_measure' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `rg -n 'theorem preimage_closure' <snapshot>/mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `rg -n 'any_radius_rv' <snapshot>/project (no match)`
- `rg -n '^def HasWeightedApproximateTangentSpaceAt|^noncomputable def blowUpMap|^def CountablyRectifiable' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I scan of every lean_name field in dag.json and nodes/*/*.json of this run (reservation check, 409 names)`
- `git show 363c12f633c5 / e9dece5c26fe (accepted rsod_tv_exists_structure and rsod_tv_tangentProj_eq proofs); python3 read of nodes/root-regular-set-open-dense-a1-translated-varifold-a1/decomposition-v1.json`
- `lake env lean Checks/Api.lean (#check of the cited Mathlib API names)`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/rv-decomp-xMtC66/proj (packages symlinked to lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean, Checks/C1.lean, Checks/C45.lean, Checks/C23.lean, Checks/C6.lean, Checks/All.lean (complete child proofs, parent assembly, #print axioms)`
- `lake env lean Checks/ChalAll.lean and Checks/SolAll.lean (comparator-shaped challenge/solution targets, scope replayed by verifier/gmt-compare.py contract_scope)`
- `verifier/lean_contract.validate_lean_statement on all seven types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-rescaled-varifold-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-translated-varifold-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rv-decomp-xMtC66/proj/Checks/All.lean`
- `/tmp/rv-decomp-xMtC66/proj/Checks/ChalAll.lean`
- `/tmp/rv-decomp-xMtC66/proj/Checks/SolAll.lean`
- `/tmp/rv-decomp-xMtC66/proj/Checks/Api.lean`

Snapshot and reservations
- The snapshot is pinned at project ea5607598f31 and Mathlib 25730c7c759d. Its Contract.lean and Submission.lean are byte-identical to the workspace copies.
- No-match results: 'any_radius_rv' occurs nowhere in the snapshot project. None of the 409 lean_names reserved in the run starts with any_radius_rv_, so the six proposed names are free.

Mathlib facts the children cite
- MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ (Geometry/Euclidean/Volume/Measure.lean:152): μHE[d](r • s) = ‖r‖₊^d • μHE[d] s. With Isometry.euclideanHausdorffMeasure_preimage (:136) this proves map_hausdorff.
- MeasurableEmbedding.map_apply (Measure/Map.lean:271) and MeasurableEmbedding.restrict_map (Measure/Restrict.lean:890) hold for arbitrary sets. MeasurableEmbedding.lintegral_map, MeasurableEmbedding.integral_map and MeasurableEmbedding.integrableOn_map_iff exist (#check).
- integral_smul_measure (Bochner/Basic.lean:1052) and lintegral_smul_measure (Lebesgue/Basic.lean:418) are unconditional.
- mem_support_iff_forall is at Measure/Support.lean:75. No-match: Support.lean has no support_map or support_smul, so support_eq proves the pushforward-support identity directly.
- Homeomorph.preimage_closure is at Topology/Homeomorph/Defs.lean:300.
- Not present in this Mathlib (#check fails), with the workaround used:
  - MeasurableEmbedding.setLIntegral_map → restrict_map + lintegral_map;
  - IntegrableOn.smul_measure → Measure.restrict_smul + Integrable.smul_measure;
  - LipschitzWith.const_smul → lipschitzWith_smul + LipschitzWith.comp.

SimonGMT (pinned package)
- CountablyRectifiable (Rectifiable.lean:34), blowUpMap (:96) and HasWeightedApproximateTangentSpaceAt (:330, a Bochner integral over blowUpMap x r '' M against θ(x + r • y), filter 𝓝[>] 0) are the definitions the structure and tangent children transport.

Template
- The accepted rsod_tv_exists_structure and rsod_tv_tangentProj_eq proofs (commits 363c12f, e9dece5) and the rsod translated-varifold decomposition-v1.json give the translation-only template. This split extends it with the dilation: the Hausdorff factor R^{-n}, radius R r in blow-ups, and the test field R·X'∘φ.

Lean verification in the scratch copy
- All six child types elaborate in the comparator scope.
- Complete proofs of all six children and of the frozen parent type from them compile.
- Axioms are only propext, Classical.choice and Quot.sound.
- The comparator-shaped challenge and solution modules compile, and validate_lean_statement accepts all seven types.
