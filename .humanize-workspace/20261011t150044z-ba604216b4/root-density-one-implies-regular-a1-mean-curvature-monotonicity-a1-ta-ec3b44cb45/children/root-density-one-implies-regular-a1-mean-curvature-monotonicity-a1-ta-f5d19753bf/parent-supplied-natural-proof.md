# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_measurable-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_measurable-a1.carrier_sigma_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2, parts (a)–(d), of the parent proof. The parent needs this σ-finiteness for Tonelli's theorem in step 6. The proof uses only four fields of R: M ⊆ U (R.carrier_subset), M Borel (R.measurableSet_carrier), θ > 0 on M (R.mult_pos) and the local integrability of θ (R.locallyIntegrable_mult). Notation: Hⁿ := μHE[n] and ν := Hⁿ⌞M.

1. Compact exhaustion of U. There are compact sets K_0, K_1, K_2, … ⊆ U with ⋃_j K_j = U.
- If U = ℝ^P, take K_j := closedBall(0, j).
- Otherwise F := ℝ^P ∖ U is closed and nonempty, and d(y) := dist(y, F) = inf_{z∈F}|y − z| is 1-Lipschitz, hence continuous.
  - If y ∈ F, then d(y) = 0.
  - If y ∈ U, then, since U is open, some ball B(y, ε) ⊆ U misses F, so d(y) ≥ ε > 0.
  - Put K_j := {y : |y| ≤ j and d(y) ≥ 1/(j+1)}.
  - K_j is closed, as an intersection of preimages of closed sets under continuous maps, and bounded, hence compact (Heine–Borel).
  - K_j ⊆ {d > 0} = U.
  - For y ∈ U, choose j ≥ |y| with 1/(j+1) ≤ d(y), which is possible since d(y) > 0. Then y ∈ K_j. So ⋃_j K_j = U.
- Equivalent route used in Lean: U is an open subset of the locally compact, second-countable space ℝ^P. So U with the subspace topology is locally compact and second countable, hence σ-compact (IsOpen.locallyCompactSpace, sigmaCompactSpace_of_locallyCompact_secondCountable, isSigmaCompact_iff_sigmaCompactSpace).

2. Pieces of finite measure.
- Put B_j := M ∩ K_j. It is Borel: M is Borel, and K_j is compact, hence closed.
- For x ∈ B_j we have x ∈ M, so θ(x) ≥ 1, because θ is ℕ-valued and positive on M.
- Therefore Hⁿ(B_j) = ∫⁻_{B_j} 1 dHⁿ ≤ ∫⁻_{B_j} θ dHⁿ = ∫⁻_{M∩K_j} θ dHⁿ < ∞.
- The last bound is R.locallyIntegrable_mult, which applies because K_j is compact and K_j ⊆ U.

3. Covering.
- By R.carrier_subset and step 1, M ⊆ U = ⋃_j K_j, so M = ⋃_j B_j.
- Since B_j ⊆ M, ν(B_j) = Hⁿ(B_j ∩ M) = Hⁿ(B_j) < ∞.
- The Borel set C := ℝ^P ∖ M satisfies ν(C) = Hⁿ(C ∩ M) = Hⁿ(∅) = 0.

4. Conclusion.
- The Borel sets S_j := B_j ∪ C (j ∈ ℕ) satisfy ν(S_j) ≤ ν(B_j) + ν(C) < ∞.
- ⋃_j S_j = M ∪ C = ℝ^P.
- So ℝ^P is a countable union of Borel sets of finite ν-measure, and ν is σ-finite.
- In Lean one may instead apply SimonGMT's Poincare.SimonGMT.Chapter03.sigmaFinite_restrict_of_hausdorff_finite_cover to the cover M ⊆ ⋃_j B_j with Hⁿ(B_j) < ∞. ∎

## Key steps

1. The open set U is a countable union of compact sets K_j ⊆ U.
2. θ ≥ 1 on M and R.locallyIntegrable_mult give Hⁿ(M ∩ K_j) ≤ ∫⁻_{M∩K_j} θ dHⁿ < ∞.
3. M ⊆ U = ⋃K_j, so the Borel sets (M ∩ K_j) ∪ (ℝ^P ∖ M) have finite ν-measure and cover ℝ^P. Hence ν = Hⁿ⌞M is σ-finite.

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
