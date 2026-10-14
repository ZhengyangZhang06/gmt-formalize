# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.tangent_space_dilation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 3, orientation bullet ("For r > 0, blowUpMap z r '' M' = {r^{-1}(λ^{-1}m − z) : m ∈ M} = {(λr)^{-1}(m − λz) : m ∈ M} = blowUpMap y (λr) '' M, and λr → 0⁺ as r → 0⁺; hence HasApproximateTangentSpaceAt n M' z Q"), with λ = c, y = cz and M' = λ^{-1}M = T^{-1}(M), T(x) := cx. Book: Simon Ch. 3, Definition 1.4 (chapter-03.txt line 77), approximate tangent spaces defined by blow-ups η_{x,λ}.

Recall the definition (SimonGMT Chapter03, Simon Ch. 3, 1.4): HasApproximateTangentSpaceAt n E x Q means finrank Q = n and, for every f ∈ C_c(ℝ^P, ℝ), the function r ↦ ∫_{η_{x,r}(E)} f dH^n (integral over the image set η_{x,r}(E) with respect to H^n = μHE[n]) tends to ∫_Q f dH^n as r → 0 within (0, ∞), where η_{x,r}(y) := r^{-1}(y − x) (SimonGMT blowUpMap x r y). Write M' := T^{-1}(M) = {x : cx ∈ M}.

1. Dimension. finrank Q = n is the first component of the hypothesis HasApproximateTangentSpaceAt n M (cz) Q.

2. Set identity: for every r ∈ ℝ, η_{z,r}(M') = η_{cz,cr}(M).
 First, for every m ∈ ℝ^P: (cr)^{-1}(m − cz) = (r^{-1}c^{-1})(m − cz) = r^{-1}(c^{-1}m − c^{-1}(cz)) = r^{-1}(c^{-1}m − z), using (cr)^{-1} = r^{-1}c^{-1} (mul_inv_rev; this holds for all real r and c with the convention 0^{-1} = 0 of the real inverse used in the definition of η, and only r > 0 matters for the limit in step 4), (ab)•v = a•(b•v), linearity of v ↦ c^{-1}v, and c^{-1}(cz) = z (c ≠ 0).
 (⊆) Let y = η_{z,r}(m') with m' ∈ M', i.e. cm' ∈ M. Put m := cm' ∈ M. By the identity, η_{cz,cr}(m) = r^{-1}(c^{-1}(cm') − z) = r^{-1}(m' − z) = y.
 (⊇) Let y = η_{cz,cr}(m) with m ∈ M. Put m' := c^{-1}m. Then cm' = c(c^{-1}m) = m ∈ M, so m' ∈ M', and by the identity η_{z,r}(m') = r^{-1}(c^{-1}m − z) = η_{cz,cr}(m) = y.

3. The map φ(r) := cr tends to 0 within (0, ∞) as r → 0 within (0, ∞): φ is continuous with φ(0) = c·0 = 0, so φ(r) → 0 as r → 0 (in particular along r → 0⁺), and φ(r) = cr > 0 whenever r > 0 because c > 0; a function converging to 0 that eventually takes values in (0, ∞) converges within (0, ∞) (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within).

4. Fix f ∈ C_c(ℝ^P, ℝ) and put F(s) := ∫_{η_{cz,s}(M)} f dH^n. By the hypothesis HasApproximateTangentSpaceAt n M (cz) Q, F(s) → ∫_Q f dH^n as s → 0⁺. By step 2, ∫_{η_{z,r}(M')} f dH^n = F(cr) = (F ∘ φ)(r) for every r. By step 3 and the composition of limits, F(φ(r)) → ∫_Q f dH^n as r → 0⁺. Hence r ↦ ∫_{η_{z,r}(M')} f dH^n tends to ∫_Q f dH^n as r → 0⁺.

5. Steps 1 and 4 are the two components of HasApproximateTangentSpaceAt n M' z Q, i.e. HasApproximateTangentSpaceAt n ((x ↦ cx)^{-1}(M)) z Q.

## Key steps

1. finrank Q = n is inherited from the hypothesis.
2. Set identity η_{z,r}(c^{-1}M) = η_{cz,cr}(M) for every r, from (cr)^{-1}(m − cz) = r^{-1}(c^{-1}m − z).
3. r ↦ cr tends to 0 within (0,∞) as r → 0⁺ because c > 0.
4. Compose the hypothesis limit at cz with r ↦ cr.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp ... GMT/Ch07/Submission.lean (both identical); git -C .lake/packages/{simongmt,mathlib} log -1 (2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cat -n GMT/Ch07/Contract.lean (IMRep, IMRep.action/Represents/measure, currentEval, dilationCLM, dilation, blowUp, IsConeCurrent)`
- `cat -n simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean (affinePullbackForm, affinePullbackTestOn_coe, GeometricCurrentOn.affinePushforward_apply)`
- `grep -rn restrictDomain simongmt/Poincare/SimonGMT; cat -n Chapter06/CurrentLocalEquality.lean (restrictDomain_apply, testFormOnInclusion_coe)`
- `sed -n 1,200p Chapter06/Currents.lean; sed -n 1,80p Chapter06/Forms.lean (TestFormOn, GeometricCurrentOn, Covector, DifferentialForm, IsTestForm)`
- `sed -n 1,200p Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt)`
- `rg -n HasApproximateTangentSpaceAt simongmt | grep -iE 'smul|dilat|scale|homothet|preimage|image'; rg -n 'theorem .*(smul|dilat|homothet|rescale)' Chapter03 Chapter04 Chapter06; grep '^theorem' Chapter08/TangentRescaling.lean`
- `grep -rn 'hausdorffMeasure_smul\|euclideanHausdorffMeasure_smul\|euclideanHausdorffMeasure_homothety\|map_euclideanHausdorffMeasure\|euclideanHausdorffMeasure_image' mathlib/Mathlib; sed -n 100,180p Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 745,770p Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'theorem map_smul_univ' mathlib/Mathlib; sed -n 510,525p Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `grep -n lipschitzWith_smul Mathlib/Analysis/Normed/MulAction.lean; grep -n 'protected theorem comp' Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `grep -rhoE '"lean_name": *"[^"]+"' nodes dag.json | sort -u; grep -rlE 'euclid_hausdorff_dilation_change_of_variables|approx_tangent_space_smul_preimage|imrep_univ_smul_rescale_exists|cone_current_apply_dilation_pullback|imrep_smul_rescale_action_measure' nodes dag.json problem.json GMT (no match)`
- `sed -n 694,700p book/chapter-07.txt; sed -n 404,410p book/chapter-06.txt; grep -n '1.4 Definition' book/chapter-03.txt`
- `lake env lean /tmp/cmh-decomp/{Stmts,ChildA,ChildB,ChildE,ChildF,ChildD,Final,Inst}.lean (#print axioms; pp.explicit instance check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cmh-decomp/Final.lean`
- `/tmp/cmh-decomp/Inst.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean, and the installed simongmt (2b366308) and mathlib (25730c7c) match the pins. SimonGMT supplies the pieces the children need: affinePullbackForm, affinePullbackTestOn_coe and affinePushforward_apply (AffineCurrentPushforward.lean); restrictDomain_apply and testFormOnInclusion_coe (CurrentLocalEquality.lean); CountablyRectifiable, blowUpMap and HasApproximateTangentSpaceAt (Rectifiable.lean, Simon 3.1.1 and 3.1.4). It has no dilation-invariance lemma for HasApproximateTangentSpaceAt or for triples: Chapter08/TangentRescaling.lean treats Chapter 8 general varifolds only. Snapshot Mathlib supplies Measure.euclideanHausdorffMeasure_smul₀ (Geometry/Euclidean/Volume/Measure.lean:152), ContinuousAlternatingMap.map_smul_univ (Topology/Algebra/Module/Alternating/Basic.lean:518), lipschitzWith_smul (Analysis/Normed/MulAction.lean:51) and the measurable-embedding API (restrict_map, lintegral_map, integral_map, ae_map_iff, measurableSet_image). All five child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract's opens. Each is proved in scratch using only propext, Classical.choice and Quot.sound. The parent's exact frozen type follows from them plus the sibling imrep_measure_eq_of_represents_same_current; the only sorryAx is that sibling stub. None of the five proposed names occurs in the DAG. Book lines cited by the proofs were checked: chapter-07.txt 697–698, chapter-06.txt 408, chapter-03.txt 77. No network sources were needed.
