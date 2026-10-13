# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1`
- Child DAG node: `root.density_semicontinuity-a1.variation_lsc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 8, Remark 3.8(1) (“a trivial consequence of the definitions”). This is exactly Step 1 of the parent proof. It uses only the kernel-checked SimonGMT lemmas of Chapter08/FirstVariationRiesz.lean and Chapter08/VarifoldConvergence.lean, so no sibling is needed.

1. Notation. IsRelCompactOpenIn W U unfolds to IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U. These are exactly the hypotheses `IsOpen W` and `IsCompact (closure W) ∧ closure W ⊆ U` used in SimonGMT's HasLocallyBoundedFirstVariation and its lemmas. For a varifold X with locally bounded first variation hX, variationMeasure X = X.firstVariationRieszMeasure hX by definition: the `dite` in variationMeasure takes its positive branch (rewrite with `variationMeasure` and `dif_pos hX`/`dite_eq_left`).

2. Identification for the V_i. Fix i and W with IsRelCompactOpenIn W U. By step 1 and Varifold.firstVariationRieszMeasure_eq_norm (Simon 2.5 for the Riesz measure built from local boundedness): variationMeasure (V_i) W = (V_i).firstVariationRieszMeasure (hi i) W = (V_i).firstVariationNormOn W.

3. Transport of the bound. For every open W with IsCompact (closure W) ∧ closure W ⊆ U, step 2 rewrites the hypothesis as liminf_i (V_i).firstVariationNormOn W = liminf_i variationMeasure (V_i) W ≠ ∞.

4. Local boundedness of V. Since V_i → V on G_n(U), δV_i(X) → δV(X) for every X ∈ K(U;ℝ^N), because div_S X is a continuous compactly supported test function on G_n(U). Hence the supremum firstVariationNormOn is lower semicontinuous: V.firstVariationNormOn W ≤ liminf_i (V_i).firstVariationNormOn W for every W (Varifold.RadonConverges.firstVariationNormOn_le_liminf). With step 3 this gives V.firstVariationNormOn W ≠ ∞ for every open W ⊂⊂ U, i.e. V has locally bounded first variation. This is exactly Varifold.RadonConverges.hasLocallyBoundedFirstVariation applied to the bound of step 3. Call this proof hV. This is the first conclusion.

5. The inequality. For W with IsRelCompactOpenIn W U: variationMeasure V W = V.firstVariationRieszMeasure hV W (step 1) = V.firstVariationNormOn W (firstVariationRieszMeasure_eq_norm) ≤ liminf_i (V_i).firstVariationNormOn W (firstVariationNormOn_le_liminf) = liminf_i variationMeasure (V_i) W (step 2, rewritten under the liminf). This is the second conclusion. ∎

## Key steps

1. variationMeasure X = X.firstVariationRieszMeasure hX whenever X has locally bounded first variation (dif_pos).
2. firstVariationRieszMeasure_eq_norm: on W ⊂⊂ U, variationMeasure (V_i) W = (V_i).firstVariationNormOn W, so the liminf hypothesis becomes a liminf bound on firstVariationNormOn.
3. RadonConverges.hasLocallyBoundedFirstVariation gives local boundedness of V.
4. variationMeasure V W = V.firstVariationNormOn W ≤ liminf (V_i).firstVariationNormOn W = liminf variationMeasure (V_i) W by firstVariationNormOn_le_liminf.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `cat simongmt Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean; grep -n '^theorem\|^def' Chapter08/{Varifold,FirstVariationRiesz,BallVariationBound,StationaryMonotonicity,FirstVariationDensity,FirstVariationBounds}.lean`
- `grep -rn -i 'portmanteau\|le_liminf\|limsup_le\|liminf_le' simongmt/Poincare --include=*.lean; grep -rln RadonConverges simongmt/Poincare`
- `grep -n 'theorem exist_disjoint_covering_families' -A 12 and 'structure BallPackage' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -rn 'countable_of_nonempty_interior\|countable_of_isOpen' mathlib/Mathlib/Topology/`
- `grep -n 'theorem exists_continuous_one_zero_of_isCompact\|theorem exists_compact_between' mathlib/Mathlib/Topology/UrysohnsLemma.lean mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `lake env lean Scratch/Api.lean Api2.lean Api3.lean (#check: HasBesicovitchCovering (Euclidean N), CompactSpace (Grassmannian N n), IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, IsOpen.exists_iUnion_isClosed, TopologicalSpace.isOpen_iUnion_countable, closure_thickening_subset_cthickening, ball_subset_thickening, cthickening_closure, ENNReal.liminf_add_of_right_tendsto_zero, Monotone.map_liminf_of_continuousAt, ofReal_integral_eq_lintegral_ofReal, Filter.limsup_comp, limsup_le_limsup_of_le, ENNReal.inv_mul_cancel_left, measure_biUnion_null_iff; ENNReal.liminf_const_mul and ENNReal.mul_liminf: unknown constants)`
- `python3 -I gen.py: gmt-compare.contract_scope replay + lean_contract.validate_lean_statement on the 6 lean_statements; lake env lean Cmp/Challenge0..5.lean`
- `lake env lean Scratch/Small.lean, Scratch/C2.lean, Scratch/C3.lean, Scratch/C5.lean, Scratch/C6.lean, Scratch/All.lean (exact frozen statements with complete proofs + parent assembly + #print axioms)`
- `python3 dag.json lean_name collision check (15 nodes); grep -l -i portmanteau nodes/*/parent-supplied-natural-proof.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

Snapshot: project 63436ae6 + Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. SimonGMT Chapter08/VarifoldConvergence.lean already proves RadonConverges.firstVariation_tendsto, firstVariationNormOn_le_liminf, hasLocallyBoundedFirstVariation and firstVariationRieszMeasure_le_liminf. FirstVariationRiesz.lean:218 firstVariationRieszMeasure_eq_norm identifies variationMeasure with firstVariationNormOn on W ⊂⊂ U. Remark 3.8(1) (child variation_lsc) therefore needs no sibling. The VarifoldConvergence module states that it does not prove the lower-density part. SimonGMT has no portmanteau for varifold weights: the only *_le_liminf lemmas are for first variation, BV and currents (Chapter06/Mass.lean WeaklyConvergesOn.massOn_le_liminf), hence the child weight_portmanteau. Mathlib supplies the needed tools: Besicovitch covering families (Covering/Besicovitch.lean:455 exist_disjoint_covering_families, whose BallPackage needs only bounded radii; HasBesicovitchCovering is inferred for Euclidean N); countability of disjoint balls (Topology/Bases.lean:493); Urysohn (UrysohnsLemma.lean:404, LocallyCompact.lean:172); and the thickening and ℝ≥0∞ liminf lemmas. ENNReal.liminf_const_mul does not exist, so the proofs use Monotone.map_liminf_of_continuousAt. All 6 child lean_statements pass validate_lean_statement and elaborate in the replayed contract scope. In a scratch copy, complete proofs of all 6 exact statements compile with axioms propext, Classical.choice and Quot.sound only, and the parent assembly via Submission.monotonicity_and_density_theorems checks against DensitySemicontinuity. dag.json has no lean_name collisions.
