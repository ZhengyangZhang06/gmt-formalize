# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.mickle_rado-a1`
- Child DAG node: `root.rectifiability-a1.mickle_rado-a1.limsup_eq_iinf-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent-supplied proof (P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Thm 18.5, Mickle–Radó), which uses ϑ(c) = inf_q g_q(c) "by the definition of limsup". This child proves that identity for an arbitrary [0,∞]-valued function, with q = n + 1.

Notation. f : ℝ → [0,∞] is arbitrary. 𝓝[>]0 is the filter of right neighbourhoods of 0 (sets containing an interval (0,ε) with ε > 0). For ε ∈ ℝ put G(ε) := sup_{t∈(0,ε)} f(t) ∈ [0,∞] (so G(ε) = 0 when ε ≤ 0).

1. Basis formula. The intervals (0,ε), ε > 0, form a basis of 𝓝[>]0 (Mathlib `nhdsGT_basis 0`; ℝ has no largest element). For a filter with a basis (s_i)_{p i} and a function u into a complete lattice, limsup u = inf_{i, p i} sup_{a∈s_i} u(a) (Mathlib `Filter.HasBasis.limsup_eq_iInf_iSup`). Hence limsup_{𝓝[>]0} f = inf_{ε>0} G(ε).
2. Monotonicity of G. If ε ≤ ε′ then (0,ε) ⊆ (0,ε′), so every value f(t) occurring in the supremum G(ε) also occurs in G(ε′). Hence G(ε) ≤ G(ε′) (Mathlib `biSup_mono`).
3. First inequality. For each n ∈ ℕ we have 1/(n+1) > 0, so ε = 1/(n+1) is admissible in step 1 and inf_{ε>0} G(ε) ≤ G(1/(n+1)). Taking the infimum over n gives inf_{ε>0} G(ε) ≤ inf_{n∈ℕ} G(1/(n+1)).
4. Second inequality. Let ε > 0. By the Archimedean property of ℝ there is n ∈ ℕ with 1/(n+1) < ε (Mathlib `exists_nat_one_div_lt`). By step 2, inf_{m∈ℕ} G(1/(m+1)) ≤ G(1/(n+1)) ≤ G(ε). Since ε > 0 was arbitrary, inf_{n∈ℕ} G(1/(n+1)) ≤ inf_{ε>0} G(ε).
5. Conclusion. By steps 1, 3 and 4 and antisymmetry, limsup_{𝓝[>]0} f = inf_{n∈ℕ} sup_{t∈(0,1/(n+1))} f(t). In Lean notation this is `limsup f (𝓝[>] 0) = ⨅ n : ℕ, ⨆ t ∈ Ioo 0 (1 / ((n : ℝ) + 1)), f t`. ∎

Lean reference proof (appendix; compile-checked as a single declaration inside `namespace GMT.Ch06` of a scratch copy of the frozen project, commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c; `#print axioms` = [propext, Classical.choice, Quot.sound]; it introduces no auxiliary declarations):
```lean
theorem Submission.rectifiability_mickle_rado_limsup_eq_iInf : ∀ f : ℝ → ℝ≥0∞, limsup f (𝓝[>] (0 : ℝ)) = ⨅ n : ℕ, ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), f t := by
  intro f
  rw [(nhdsGT_basis (0 : ℝ)).limsup_eq_iInf_iSup]
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact iInf₂_le (1 / ((n : ℝ) + 1)) (by positivity)
  · refine le_iInf₂ fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine (iInf_le _ n).trans ?_
    exact biSup_mono fun t ht => ⟨ht.1, ht.2.trans hn⟩
```

## Key steps

1. The intervals (0,ε), ε>0, form a basis of 𝓝[>]0, so limsup f = inf_{ε>0} G(ε) with G(ε) := sup_{t∈(0,ε)} f(t) (HasBasis.limsup_eq_iInf_iSup).
2. G is monotone in ε, since (0,ε) ⊆ (0,ε′) for ε ≤ ε′.
3. inf_{ε>0} G ≤ inf_n G(1/(n+1)), because each 1/(n+1) > 0.
4. inf_n G(1/(n+1)) ≤ G(ε) for every ε > 0: pick n with 1/(n+1) < ε (Archimedean) and use monotonicity. Antisymmetry gives the identity.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean /tmp/mickle-rado-decomp-VkNUMK/GMT/Ch06/Contract.lean (all identical)`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement|theorem ae_tendsto_measure_inter_div|theorem exists_mem_of_measure_ne_zero_of_ae|theorem countable_of_isOpen|theorem measure_biUnion_le|theorem addHaar_ball|theorem addHaar_closedBall|theorem exists_infDist_eq_dist|exists_isCompact_lt_add|exists_lt_isCompact|theorem LowerSemicontinuous.measurable|lowerSemicontinuous_iSup|theorem HasBasis.limsup_eq_iInf_iSup|theorem nhdsGT_basis' local-references/197bdd4b88278494/mathlib/Mathlib`
- `sed -n 50,80p and 150,215p mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean; sed -n 1080,1115p mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; sed -n 420,432p mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n -i 'mickle|radó|rado\b' local-references/197bdd4b88278494/mathlib/Mathlib; rg -n -i 'mickle' local-references/197bdd4b88278494/project; rg -n -i 'mickle|radó' lake-packages-25730c7c/simongmt/Poincare (no Mickle–Radó result; only author-name false positives 'Herradón')`
- `rg -n 'LowerSemicontinuous|lowerSemicontinuous' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; sed -n 1,420p SimonGMT/Chapter01/Densities.lean`
- `grep -n '^theorem\|^lemma\|^def\|^noncomputable def' SimonGMT/Chapter01/{InfiniteDensitySet,HausdorffDensityBounds,RadonDensity,DensityComparison,DensityCovering,LowerDensityComparison,GeneralDensity,SymmetricVitali}.lean; sed -n 15,75p and 290,420p DensityComparison.lean; sed -n 1,80p DensityCovering.lean; sed -n 15,100p HausdorffDensityBounds.lean`
- `cmp -s snapshot mathlib/Mathlib/{MeasureTheory/Covering/Vitali,MeasureTheory/Covering/Besicovitch,MeasureTheory/Measure/Restrict,MeasureTheory/Measure/Regular,MeasureTheory/Measure/Lebesgue/EqHaar,Order/LiminfLimsup,Topology/Semicontinuity/Basic}.lean against lake-packages-25730c7c/mathlib (all identical; git rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d)`
- `lake env lean Scratch/Names.lean (#synth volume.InnerRegular, IsLocallyFiniteMeasure, ProperSpace, SeparableSpace, IsAddHaarMeasure on Eucl 3; #check of every cited Mathlib lemma)`
- `lake env lean Scratch/Parent.lean; Scratch/Assembly.lean (parent from four sorry'd children); Scratch/Easy.lean; Scratch/Vitali.lean; Scratch/Full.lean with #print axioms of all five declarations`
- `lake env lean GMT/Ch06/Submission.lean -o .lake/build/lib/lean/GMT/Ch06/Submission.olean -i ...ilean (scratch Submission with the five declarations inserted before main_theorem)`
- `python3 -I /tmp/mickle-rado-gen/gen.py: verifier/lean_contract.validate_lean_statement + gmt-compare.child_modules(mode=contract) for the 5 statements; lake env lean on the 10 generated NodeChallenge/NodeSolution modules (all rc=0)`
- `python3 lean_name collision scan of dag.json (257 nodes) and nodes/*/decomposition-v*.json (422 proposed names)`
- `python3 survey of nodes/*/decomposition-audit-v*.json (rejection reasons); sed -n 340,378p problem.md (helper-declaration rule at line 378)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/LowerDensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/GeneralDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SymmetricVitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/decomposition-v1.json`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Parent.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Names.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Assembly.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Easy.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Vitali.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Full.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/GMT/Ch06/Submission.lean`
- `/tmp/mickle-rado-decomp-VkNUMK/Scratch/Cmp`
- `/tmp/mickle-rado-gen/gen.py`
- `/tmp/mickle-rado-gen/children.json`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. It is byte-identical to the workspace Contract.lean and Submission.lean and to the scratch copy.

No existing Mickle–Radó result: neither the snapshot Mathlib, the project, nor the pinned SimonGMT contains one (rg -i 'mickle|radó' finds only author-name false positives).

SimonGMT's density results do not apply to the bare outer measure ψ, which has only inner continuity on balls:
- Chapter01/Densities.lean: lowerSemicontinuous_measure_ball needs a Measure; lowerSemicontinuous_outerMeasure_inter_ball and measurable_dimensionalUpperDensity need borel ≤ caratheodory and finite closed balls; nhdsGT_zero_basis_rat is also there.
- DensityComparison.lean: simon_theorem_3_3 and simon_theorem_3_6 need IsBorelRegularOuterMeasure.
So the four child obligations are genuine.

The snapshot Mathlib supplies every ingredient the children and the assembly use:
- limsup_eq_iinf: nhdsGT_basis (LeftRightNhds.lean:80), Filter.HasBasis.limsup_eq_iInf_iSup (LiminfLimsup.lean:308), exists_nat_one_div_lt.
- sup_lsc: lt_biSup_iff, ENNReal.continuous_div_const, Continuous.comp_lowerSemicontinuous, lowerSemicontinuous_biSup.
- vitali_bound: Vitali.exists_disjoint_subfamily_covering_enlargement_ball (Vitali.lean:195), Set.PairwiseDisjoint.countable_of_isOpen, IsClosed.exists_infDist_eq_dist, IsClosed.notMem_iff_infDist_pos, Metric.disjoint_ball_infDist, measure_biUnion_le (OuterMeasure/Basic.lean:74), measure_biUnion, Measure.addHaar_ball (EqHaar.lean:456), finrank_euclideanSpace_fin.
- density_zero: Besicovitch.ae_tendsto_measure_inter_div (Besicovitch.lean:1105), Measure.addHaar_closedBall (EqHaar.lean:500), measure_sdiff_add_inter, ENNReal.Tendsto.sub and ENNReal.Tendsto.const_mul, tendsto_of_tendsto_of_tendsto_of_le_of_le'.
- parent assembly: LowerSemicontinuous.measurable (BorelSpace/Order.lean:686), Measurable.iInf, MeasurableSet.exists_lt_isCompact (Regular.lean:732, with the InnerRegular instance on volume), Measure.exists_mem_of_measure_ne_zero_of_ae (Restrict.lean:426), ENNReal.exists_nat_gt, ENNReal.exists_inv_nat_lt.
The snapshot files are byte-identical to the pinned package Mathlib used for compilation.

Compile checks in a scratch copy of the frozen project:
- All four children and the parent assembly compile; #print axioms gives [propext, Classical.choice, Quot.sound] for all five declarations.
- All 10 comparator-generated NodeChallenge/NodeSolution modules compile in the exact child scope.
- All five statements pass validate_lean_statement.

No proposed lean_name collides with the 257 DAG names or the 422 names proposed in decompositions.
