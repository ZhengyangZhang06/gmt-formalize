# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.rescaled_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 3 ("The rescaled triple R_λ := (M', θ', ξ') with M' := S(M) = λ^{-1}M, θ'(z) := θ(λz), ξ'(z) := ξ(λz) is an IMRep univ n", with its six bullets), with λ = c; note λ^{-1}M = S(M) = T^{-1}(M) for T(x) := cx. Uses the sibling children dilation_change_of_variables, cited as (CV)(i) and (CV)(ii), and tangent_space_dilation, cited as (TS). Book: Simon Ch. 6, Definition 3.1 of integer multiplicity currents (chapter-06.txt §3) and the push-forward under the homothety (Ch. 6, 2.23, chapter-06.txt line 408).

Notation: M := R.carrier, θ := R.mult, ξ := R.orient, T(x) := cx, M' := T^{-1}(M) = {x : cx ∈ M}, θ' := θ ∘ T, ξ' := ξ ∘ T, H^n := μHE[n], ν := H^n⌞M and ν' := H^n⌞M' (⌞ = restriction). T is a homeomorphism of ℝ^P (inverse x ↦ c^{-1}x, c ≠ 0), so it is continuous, measurable, injective and a measurable embedding (Homeomorph.smulOfNeZero c hc). By (CV)(i) applied to the set M:
 (∗) T_#ν' = ENNReal.ofReal(c^{-n}) · ν.
We define R' := (M', θ', ξ') and verify the fields of IMRep univ n one by one (steps 1–8); the three identities R'.carrier = T^{-1}(M), R'.mult x = θ(cx) and R'.orient x = ξ(cx) (all x) then hold by construction (step 9).

1. measurableSet_carrier. M' = T^{-1}(M) is Borel, being the preimage of the Borel set M (R.measurableSet_carrier) under the measurable map T.

2. carrier_subset. M' ⊆ ℝ^P = univ trivially.

3. rectifiable (SimonGMT CountablyRectifiable n M'). By R.rectifiable there are M₀ ⊆ ℝ^P with H^n(M₀) = 0 and maps F_j : ℝ^n → ℝ^P (j ∈ ℕ), each F_j Lipschitz with some constant K_j ≥ 0, such that M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n). Put M₀' := T^{-1}(M₀) and F_j'(w) := c^{-1}F_j(w).
 (a) H^n(M₀') = 0: by (CV)(i) applied to the set M₀, T_#(H^n⌞T^{-1}(M₀)) = ENNReal.ofReal(c^{-n}) · (H^n⌞M₀). Evaluate both measures on the Borel set ℝ^P: the left side gives (H^n⌞T^{-1}(M₀))(T^{-1}(ℝ^P)) = H^n(T^{-1}(M₀)), the right side ENNReal.ofReal(c^{-n}) · H^n(M₀) = 0. Hence H^n(M₀') = 0.
 (b) F_j' is Lipschitz with constant ‖c^{-1}‖₊ · K_j: it is the composition of F_j with the ‖c^{-1}‖₊-Lipschitz map x ↦ c^{-1}x (lipschitzWith_smul, LipschitzWith.comp).
 (c) Covering. Let z ∈ M'. Then cz ∈ M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n). If cz ∈ M₀ then z ∈ T^{-1}(M₀) = M₀'. Otherwise cz = F_j(w) for some j ∈ ℕ and w ∈ ℝ^n, and then z = c^{-1}(cz) = c^{-1}F_j(w) = F_j'(w) ∈ F_j'(ℝ^n). Hence M' ⊆ M₀' ∪ ⋃_j F_j'(ℝ^n).
 By (a)–(c), M' is countably n-rectifiable.

4. measurable_mult. θ' = θ ∘ T is measurable as the composition of the measurable θ (R.measurable_mult) with the measurable T.

5. mult_pos. If z ∈ M' then cz ∈ M, hence θ'(z) = θ(cz) > 0 by R.mult_pos.

6. locallyIntegrable_mult. Let K ⊆ ℝ^P be compact (K ⊆ univ). Then T(K) = cK is compact (continuous image of a compact set) and T(K) ⊆ univ. Since T is injective, z ∈ K ⇔ cz ∈ T(K), so
 M' ∩ K = T^{-1}(M) ∩ T^{-1}(T(K)) = T^{-1}(M ∩ T(K)).
 By (CV)(ii) applied to the set M ∩ T(K) and the function g(y) := θ(y) ∈ [0,∞]:
 ∫⁻_{M'∩K} θ'(z) dH^n(z) = ∫⁻_{T^{-1}(M∩T(K))} θ(cz) dH^n(z) = ENNReal.ofReal(c^{-n}) · ∫⁻_{M∩T(K)} θ dH^n.
 The last lower integral is finite by R.locallyIntegrable_mult applied to the compact set T(K) ⊆ univ, and ENNReal.ofReal(c^{-n}) < ∞; the product of two finite elements of [0,∞] is finite (ENNReal.mul_ne_top). So ∫⁻_{M'∩K} θ' dH^n ≠ ∞.

7. aestronglyMeasurable_orient. ξ is a.e.-strongly measurable for ν (R.aestronglyMeasurable_orient), hence also for the scalar multiple ENNReal.ofReal(c^{-n}) · ν (every null set of ν is null for a scalar multiple of ν; AEStronglyMeasurable.smul_measure), i.e., by (∗), for T_#ν'. Since T is measurable, hence a.e.-measurable for ν', the composition ξ' = ξ ∘ T is a.e.-strongly measurable for ν' (AEStronglyMeasurable.comp_aemeasurable: if g is a.e.-strongly measurable for f_#μ and f is a.e.-measurable for μ, then g ∘ f is a.e.-strongly measurable for μ).

8. orients. For y ∈ ℝ^P let p(y) be the statement: there is a linear subspace Q of ℝ^P with HasApproximateTangentSpaceAt n M y Q and IsUnitOrientationOf (ξ(y)) Q. By R.orients, p(y) holds for ν-a.e. y. A property holding ν-a.e. holds (ENNReal.ofReal(c^{-n}) · ν)-a.e. (Measure.ae_smul_measure), i.e., by (∗), T_#ν'-a.e. Because T is a measurable embedding, a property holds T_#ν'-a.e. if and only if its composition with T holds ν'-a.e. (MeasurableEmbedding.ae_map_iff; no measurability of the property is required). Hence p(cz) holds for ν'-a.e. z. Fix such a z and Q with HasApproximateTangentSpaceAt n M (cz) Q and IsUnitOrientationOf (ξ(cz)) Q. By (TS) (applied to the set M, c > 0, the point z and Q), HasApproximateTangentSpaceAt n M' z Q; and ξ'(z) = ξ(cz), so IsUnitOrientationOf (ξ'(z)) Q. Thus, for ν'-a.e. z, there is Q with HasApproximateTangentSpaceAt n M' z Q and IsUnitOrientationOf (ξ'(z)) Q, which is the field orients of R'.

9. Steps 1–8 supply every field of the structure IMRep univ n for the data (M', θ', ξ'); call the resulting triple R'. By construction R'.carrier = M' = (x ↦ cx)^{-1}(R.carrier), R'.mult x = θ(cx) = R.mult (c • x) and R'.orient x = ξ(cx) = R.orient (c • x) for every x, which proves the claim.

## Key steps

1. T(x) = cx is a measurable embedding with T_#(H^n⌞T^{-1}M) = c^{-n}H^n⌞M (sibling dilation_change_of_variables).
2. Borel carrier, positivity and measurability of θ∘T transfer directly; rectifiability via the null set T^{-1}M₀ (change of variables at univ) and the Lipschitz maps c^{-1}F_j.
3. Local integrability: M' ∩ K = T^{-1}(M ∩ cK) and the lower-integral change of variables reduce to the compact set cK.
4. a.e.-strong measurability of ξ∘T: ξ is a.e.-strongly measurable for c^{-n}H^n⌞M = T_#(H^n⌞M'), then compose with T.
5. Orientation: transfer the a.e. statement through the measurable embedding T and apply dilation invariance of approximate tangent planes (sibling tangent_space_dilation).

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
