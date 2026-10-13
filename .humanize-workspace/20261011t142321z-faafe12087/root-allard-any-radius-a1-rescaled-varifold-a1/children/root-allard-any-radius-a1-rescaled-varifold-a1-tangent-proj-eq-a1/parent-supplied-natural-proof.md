# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.rescaled_varifold-a1`
- Child DAG node: `root.allard_any_radius-a1.rescaled_varifold-a1.tangent_proj_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: ℝ^{n+ℓ} = Amb n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)); H^n = μHE[n]; ψ(x) := c + R x for the given c and R > 0. This is step 5 of the parent proof. Fix x ∈ ℝ^{n+ℓ} and write p := ψ(x) = c + R x; note R ≠ 0.
1. Blow-up identity: for every r ∈ ℝ, η_{x,r}(ψ⁻¹(M)) = η_{p,R r}(M), where η_{a,s}(y) = s⁻¹(y − a). (We use (R r)⁻¹ = R⁻¹ r⁻¹ (mul_inv), which also holds when r = 0 under the convention 0⁻¹ = 0, so no case split is needed.)
(⊆) Let z ∈ ψ⁻¹(M) and w = r⁻¹(z − x). Put m := ψ(z) ∈ M. Then m − p = (c + R z) − (c + R x) = R(z − x), so η_{p,R r}(m) = (R r)⁻¹ R (z − x) = R⁻¹ r⁻¹ R (z − x) = r⁻¹ (z − x) = w.
(⊇) Let m ∈ M and w = (R r)⁻¹(m − p). Put z := R⁻¹(m − c). Then ψ(z) = c + R R⁻¹ (m − c) = m ∈ M, so z ∈ ψ⁻¹(M); and z − x = R⁻¹(m − c) − R⁻¹ R x = R⁻¹(m − p), so η_{x,r}(z) = r⁻¹ R⁻¹ (m − p) = (R r)⁻¹ (m − p) = w.
2. Multiplicity identities: for all r ∈ ℝ and y, W.mult(x + r y) = θ(c + R(x + r y)) = θ(p + (R r) y) (smul_add, mul_smul, add_assoc), and W.mult(x) = θ(p).
3. The integral functions. Fix a subspace P and f ∈ C_c(ℝ^{n+ℓ}, ℝ), and let F(s) := ∫_{η_{p,s}(M)} f(y) θ(p + s y) dH^n(y). By steps 1–2, the function r ↦ ∫_{η_{x,r}(W.carrier)} f(y) W.mult(x + r y) dH^n(y) is exactly r ↦ F(R r), and the target value W.mult(x) · ∫_P f dH^n equals L := θ(p) · ∫_P f dH^n.
4. Filter lemma: for every a > 0, the map r ↦ a r tends from 𝓝[>] 0 to 𝓝[>] 0. Indeed it is continuous with value a · 0 = 0 at 0, so it tends to 𝓝 0 along 𝓝 0 ⊇ 𝓝[>] 0, and r > 0 implies a r > 0 eventually along 𝓝[>] 0 (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within).
5. Equivalence of limits: (r ↦ F(R r)) → L along 𝓝[>] 0 ⟺ F → L along 𝓝[>] 0. (⇐) Compose F → L with step 4 for a = R. (⇒) Compose (r ↦ F(R r)) → L with step 4 for a = R⁻¹ > 0; this gives s ↦ F(R (R⁻¹ s)) = F(s) tending to L.
6. Equality of the predicates: for every subspace P, HasWeightedApproximateTangentSpaceAt n W.carrier W.mult x P ⟺ HasWeightedApproximateTangentSpaceAt n M θ p P. The dimension clauses finrank P = n are identical, and for each f the convergence clauses are equivalent by steps 3 and 5.
7. The chosen planes. Unfold tangentProj. Case 1: some P satisfies the W-predicate at x. Then by step 6 some P satisfies the V-predicate at p, and both dependent ifs take their positive branches (dite_eq_left). The two predicates are equal as functions of P (funext and propext from step 6). For equal predicates q₁ = q₂ and any proofs h₁ : ∃P, q₁ P and h₂ : ∃P, q₂ P, Classical.choose h₁ = Classical.choose h₂ (substitute q₂ := q₁; the proofs of the same proposition are equal by proof irrelevance). Hence the chosen subspaces coincide, and so do their orthogonal projections (the HasOrthogonalProjection instance is a proposition, so congruence reduces to equality of subspaces). Case 2: no P satisfies the W-predicate. Then by step 6 no P satisfies the V-predicate at p, and both sides equal 0 (dite_eq_right). In both cases W.tangentProj(x) = V.tangentProj(c + R x).

## Key steps

1. blow-up identity η_{x,r}(ψ⁻¹M) = η_{ψx,Rr}(M) for every r
2. multiplicity identities W.mult(x + r y) = θ(ψx + (Rr) y) and W.mult(x) = θ(ψx)
3. r ↦ a r maps 𝓝[>]0 to 𝓝[>]0 for a > 0, so limits along r and R r coincide
4. the weighted approximate tangent predicates of W at x and V at ψx are equivalent for every P
5. dependent-if case split; equal predicates give equal Classical.choose and equal starProjections

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
