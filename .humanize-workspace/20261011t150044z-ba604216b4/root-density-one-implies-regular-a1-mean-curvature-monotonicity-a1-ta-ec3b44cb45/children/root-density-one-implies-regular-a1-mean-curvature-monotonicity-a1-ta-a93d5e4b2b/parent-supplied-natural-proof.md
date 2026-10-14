# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_measurable-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_measurable-a1.blowup_integral_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6, parts (a)–(d), of the parent proof. Here it is stated for an arbitrary set M with s-finite Hⁿ⌞M, a continuous f ≥ 0 and a fixed r > 0. In the parent, s-finiteness comes from step 2 and f is the test function f_u of step 4.

Notation.
- Hⁿ := μHE[n]. It is defined on every subset of ℝ^P (outer measure).
- ν := Hⁿ⌞M, s-finite by hypothesis.
- η_x(y) := r⁻¹(y − x) = blowUpMap x r y.
- c := r^{−n} = |r⁻¹|ⁿ.
- No measurability of M is assumed or needed.

1. Regularity of η.
- For fixed x, η_x is the translation y ↦ y − x followed by multiplication by r⁻¹. It is continuous, hence Borel measurable.
- The map (x, y) ↦ η_x(y) = r⁻¹(y − x) is continuous on ℝ^P × ℝ^P.

2. Scaling. For every x and every set s ⊆ ℝ^P, measurable or not, Hⁿ(η_x(s)) = c·Hⁿ(s).
- η_x(s) = r⁻¹·(s − x).
- The translation y ↦ y − x is an isometry, so Hⁿ(s − x) = Hⁿ(s) (Isometry.euclideanHausdorffMeasure_image).
- Since r⁻¹ ≠ 0, Hⁿ(r⁻¹·A) = |r⁻¹|ⁿHⁿ(A) for every set A (Measure.euclideanHausdorffMeasure_smul₀).

3. The restricted measure. For every x, Hⁿ⌞η_x(M) = c·(η_x)_#ν.
- Let B be Borel. Then η_x⁻¹(B) is Borel by step 1.
- η_x(M) ∩ B = η_x(M ∩ η_x⁻¹(B)); this holds for any map (image_inter_preimage).
- Using the restriction formula (Hⁿ⌞S)(T) = Hⁿ(T ∩ S) for Borel T, and step 2:
  (Hⁿ⌞η_x(M))(B) = Hⁿ(B ∩ η_x(M)) = Hⁿ(η_x(M ∩ η_x⁻¹(B))) = c·Hⁿ(η_x⁻¹(B) ∩ M) = c·ν(η_x⁻¹(B)) = c·((η_x)_#ν)(B).
- Measures that agree on all Borel sets are equal.

4. From the Bochner integral to a lower integral. Fix x.
- f ≥ 0 everywhere, and f is continuous, hence a.e. strongly measurable for every measure.
- So ∫_{η_x(M)} f dHⁿ = (∫⁻_{η_x(M)} ofReal(f) dHⁿ).toReal (integral_eq_lintegral_of_nonneg_ae).
- This holds whether or not f is integrable on η_x(M). If it is not, the lower integral is ∞ and ∞.toReal = 0, which is also the value of the Bochner integral.

5. Change of variables.
- By step 3, ∫⁻_{η_x(M)} ofReal(f) dHⁿ = c·∫⁻ ofReal(f) d((η_x)_#ν) (lintegral_smul_measure).
- This equals c·∫⁻ ofReal(f(η_x(y))) dν(y) (lintegral_map; ofReal∘f and η_x are measurable).

6. Tonelli.
- G(x, y) := ofReal(f(r⁻¹(y − x))) is a continuous map ℝ^P × ℝ^P → [0, ∞], by step 1 and the continuity of f and ofReal. So it is Borel measurable.
- ℝ^P is second countable, so the Borel σ-algebra of ℝ^P × ℝ^P is the product σ-algebra, and G is measurable for the product σ-algebra.
- Since ν is s-finite, x ↦ ∫⁻ G(x, y) dν(y) is measurable (Measurable.lintegral_prod_right').

7. Conclusion.
- By steps 4 and 5, ∫_{η_x(M)} f dHⁿ = (c·∫⁻ G(x, y) dν(y)).toReal for every x.
- Multiplication by the constant c and ENNReal.toReal preserve measurability.
- So x ↦ ∫_{η_x(M)} f dHⁿ is Borel measurable. ∎

## Key steps

1. Hⁿ(η_x(s)) = r^{−n}Hⁿ(s) for every set s: a translation isometry followed by the dilation r⁻¹.
2. Hence Hⁿ⌞η_x(M) = r^{−n}(η_x)_#(Hⁿ⌞M), checked on Borel sets via η_x(M) ∩ B = η_x(M ∩ η_x⁻¹B).
3. For f ≥ 0 continuous, ∫_{η_x(M)} f dHⁿ = (r^{−n}∫⁻ ofReal(f(r⁻¹(y−x))) dν(y)).toReal, even when f is not integrable there.
4. (x, y) ↦ ofReal(f(r⁻¹(y−x))) is continuous, hence product-measurable. Since ν is s-finite, Tonelli (Measurable.lintegral_prod_right') makes the x-integral measurable, and so is its toReal.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project; project_commit b4d606d; mathlib_commit 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I over dag.json: tangent/measurability nodes, every accepted node's lean_name and lean_statement, duplicate lean_name check, lookup of the two reused names and the two new names`
- `git show 36b2d37 / 2b2d626 / 3c953dc (accepted proofs of imrep_approxTangent_starProjection_aesm, exists_plane_cutoff_quadratic_moment_eq, aemeasurable_starProjection_of_aemeasurable_norm_sq); git show --stat ed3a6a2 (this node's proof base = contract only)`
- `grep -n 'def \|theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 1,130p;150,330p;395,500p (blowUpMap, HasApproximateTangentSpaceAt, unique, sigmaFinite_restrict_of_hausdorff_finite_cover)`
- `rg -n 'SigmaFinite|SFinite' project/GMT simongmt/Chapter03/Rectifiable.lean (only Ch01 IsOpenSigmaFinite and the SimonGMT lemma)`
- `rg -n blowUpMap simongmt | grep -i 'measurab|continu' (only local fun_prop uses; no measurability-of-blow-up-integral lemma)`
- `rg -n approxTangentPlane project/GMT (only the Ch07 contract definition and Ch03's different definition)`
- `rg -n "theorem Measurable.lintegral_prod_right'|IsOpen.locallyCompactSpace|setLIntegral_mono'|lintegral_smul_measure|Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero|EuclideanSpace.euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib`
- `grep -n theorem mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image, Isometry.map_euclideanHausdorffMeasure, Measure.euclideanHausdorffMeasure_smul₀)`
- `grep -rn 'isSigmaCompact_iff_sigmaCompactSpace|sigmaCompactSpace_of_locallyCompact_secondCountable|aemeasurable_of_tendsto_metrizable_ae|integral_eq_lintegral_of_nonneg_ae|withDensity_absolutelyContinuous|mono_ac|tendsto_one_div_add_atTop_nhds_zero_nat|Submodule.finrank_eq_zero' mathlib/Mathlib`
- `grep -rl -w 'dsmc_imrep_carrier_sigmaFinite|dsmc_measurable_blowUp_image_setIntegral' dag.json nodes .humanize/math-wiki GMT simongmt/Poincare project (no match)`
- `lake env lean /tmp/dsmc-tpm-decomp/Probe.lean, Stmts.lean, New.lean, Full.lean, Assembly.lean (#check, #synth, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ta-ec3b44cb45/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasura-b7386b9a1e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasura-3808e84e38/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-34fbedec8b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki/submission-imrep-approxtangent-starprojection-aesm.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/tmp/dsmc-tpm-decomp/Stmts.lean`
- `/tmp/dsmc-tpm-decomp/New.lean`
- `/tmp/dsmc-tpm-decomp/Full.lean`
- `/tmp/dsmc-tpm-decomp/Assembly.lean`

Snapshot: project b4d606d, mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. This node's proof base ed3a6a2 adds no Lean declarations.

The local project has no proof of the target or of the two new lemmas. rg finds only the contract's approxTangentPlane definition, and no SigmaFinite/SFinite or blow-up-measurability lemma for IMRep.

SimonGMT Chapter03/Rectifiable.lean provides, through the contract's imports:
- blowUpMap x r y = r⁻¹(y−x);
- HasApproximateTangentSpaceAt (finrank = n, plus convergence of ∫_{blowUpMap x r '' M} f dHⁿ for every C_c test function as r → 0⁺);
- sigmaFinite_restrict_of_hausdorff_finite_cover, used for the σ-finite child.

Mathlib supplies every cited lemma: Measurable.lintegral_prod_right', integral_eq_lintegral_of_nonneg_ae, lintegral_map, lintegral_smul_measure, Isometry.euclideanHausdorffMeasure_image, Measure.euclideanHausdorffMeasure_smul₀, image_inter_preimage, IsOpen.locallyCompactSpace, isSigmaCompact_iff_sigmaCompactSpace, aemeasurable_of_tendsto_metrizable_ae', withDensity_absolutelyContinuous, AEMeasurable.mono_ac, tendsto_one_div_add_atTop_nhds_zero_nat and Submodule.finrank_eq_zero.

Two DAG theorems with the exact frozen types needed by steps 5 and 8–9 are comparator-accepted and are reused: exists_plane_cutoff_quadratic_moment_eq (candidate 2b2d626) and aemeasurable_starProjection_of_aemeasurable_norm_sq (candidate 3c953dc).

Lean checks: all child types and the parent type elaborate. The parent compiles from sorry stubs of the four children. Full.lean, which contains the accepted proofs verbatim, complete proofs of the two new children and the parent assembly, uses only propext, Classical.choice and Quot.sound.

The new names have no matches anywhere.
