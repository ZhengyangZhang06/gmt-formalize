# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.line_deriv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) with Euclidean norm |·|. DΦ(w) := fderiv ℝ Φ w and D(f∘Φ)(w) := fderiv ℝ (f ∘ Φ) w; by hypothesis these are Fréchet derivatives. This lemma is Step 4 of the parent proof (Simon Ch. 2, 4.10: the argument of 4.7 comparing the two curves s ↦ Φ(w + su) and s ↦ Φ(w) + s DΦ(w)u), stated with an explicit o(s) estimate.

1. (Notation.) Fix u ∈ ℝⁿ. Put A := DΦ(w), ℓ := D(f∘Φ)(w), x := Φ(w), and for s ∈ ℝ let γ(s) := f(x + sAu) and γ₁(s) := (f∘Φ)(w + su). Then γ(0) = γ₁(0) = f(x). We must show γ(s) − γ(0) − sℓ(u) = o(s) as s → 0, which is the statement HasDerivAt γ (ℓ(u)) 0.

2. (The chart curve.) s ↦ w + su has derivative u at s = 0 and value w there, and f∘Φ has Fréchet derivative ℓ at w. By the chain rule, γ₁ has derivative ℓ(u) at 0, i.e. γ₁(s) − γ₁(0) − sℓ(u) = o(s).

3. (The two curves are tangent at s = 0.) Since Φ has Fréchet derivative A at w, Φ(w + h) − Φ(w) − Ah = o(|h|) as h → 0. Composing with h = su, which tends to 0 as s → 0, and using |su| = |s||u|, we get Φ(w + su) − x − sAu = o(s).

4. (Lipschitz transfer.) For every s ∈ ℝ, |γ(s) − γ₁(s)| = |f(x + sAu) − f(Φ(w + su))| ≤ L|x + sAu − Φ(w + su)| = L|Φ(w + su) − x − sAu|, since f is L-Lipschitz. By step 3, γ − γ₁ = o(s).

5. (Conclusion.) Using γ(0) = γ₁(0),
 γ(s) − γ(0) − sℓ(u) = [γ₁(s) − γ₁(0) − sℓ(u)] + [γ(s) − γ₁(s)],
 a sum of two o(s) terms (steps 2 and 4). Hence γ(s) = γ(0) + sℓ(u) + o(s) as s → 0, i.e. HasDerivAt (fun s ↦ f(Φ w + s • fderiv ℝ Φ w u)) (fderiv ℝ (f ∘ Φ) w u) 0. ∎

(Lean check: this exact argument — `hasDerivAt_iff_isLittleO`, `HasFDerivAt.comp_hasDerivAt`, `HasFDerivAt.isLittleO` composed with `s ↦ w + s • u` via `IsLittleO.comp_tendsto`, `LipschitzWith.dist_le_mul`, `IsBigO.trans_isLittleO` and `IsLittleO.add` — was compiled for the frozen type in the exact comparator scope, with axioms propext, Classical.choice, Quot.sound only.)

## Key steps

1. Compare γ(s) = f(Φ(w) + sDΦ(w)u) with γ₁(s) = (f∘Φ)(w + su); γ(0) = γ₁(0).
2. Chain rule: γ₁ has derivative D(f∘Φ)(w)u at 0.
3. Differentiability of Φ at w: Φ(w + su) − Φ(w) − sDΦ(w)u = o(s).
4. Lipschitz f: |γ(s) − γ₁(s)| ≤ L|Φ(w + su) − Φ(w) − sDΦ(w)u| = o(s).
5. Adding the two o(s) estimates gives HasDerivAt γ (D(f∘Φ)(w)u) 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (both identical; workspace HEAD d8d46c95)`
- `python3 importlib verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') -> scope prefix: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n '^theorem|^def' simongmt Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,AreaDomain,WhitneyExtension,WhitneyJet}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/{SubmanifoldCover,Differential,DisjointCover}.lean`
- `grep -n '^theorem' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_smul0)`
- `grep -rn 'theorem Measurable.find|theorem measurable_find|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem DifferentiableWithinAt.differentiableAt|theorem ae_restrict_iff|theorem tendstoUniformlyOn_of_ae_tendsto|IsSigmaCompact.image|theorem normDet_sq_eq_det_gram|theorem normDet_nonneg|theorem hausdorffMeasure_image_le' mathlib/Mathlib`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 and Chapter01 (WhitneyExtension.olean absent; AreaCritical, AreaLipschitz, AreaDomain, WhitneyJet, Lusin, DensityComparison present)`
- `python3 scan of dag.json (360 nodes): uniqueness of slicing_im_tg_* names; byte-identity of child types with lpf_countably_rectifiable_c1_cover / lpf_weighted_tangent_on_c1_chart (speculative-ready); live statuses and statements of lpf_c1r_*, lpf_c1_local_antilipschitz, lpf_lipschitz_c1_immersion_pieces, lpf_wtc_*, lpf_tde_chart_directional_deriv, lpf_ccr_hasDerivAt_line_of_comp, rectifiability_weighted_tangent_ae, br_weightedTangent_congr, iwl_weighted_tangent_locality`
- `read nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (twin proofs; reuse-child mechanism)`
- `git show <workspace_result_commit>:GMT/Ch06/Submission.lean for 138 accepted nodes (extra SimonGMT imports such as Chapter02.AreaDomain, Chapter01.DensityComparison, Chapter02.AreaBranches are allowed)`
- `lake env lean /tmp/tg_split/Stmts.lean (four child types in exact comparator scope; 0 errors)`
- `lake env lean /tmp/tg_split/Assembly.lean (frozen parent type proved from chart_cover, chart_tangent, chart_gradient stubs; #print axioms: propext, sorryAx [stubs only], Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/CProof.lean (complete proof of the line_deriv frozen type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/Avail.lean (#check of cited Mathlib and SimonGMT lemmas in the Submission import closure)`
- `python3 verifier/lean_contract.py validate_lean_statement on the four child types (all OK)`
- `rg 'slicing_im_tg' local-references/197bdd4b88278494/project and lake-packages-25730c7c/simongmt (no match)`
- `sed book/chapter-03.txt (1.1-1.9, 2.1-2.2), chapter-02.txt (1.4-1.8, 4.1-4.11), chapter-01.txt (3.6-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/tmp/tg_split/Stmts.lean`
- `/tmp/tg_split/Assembly.lean`
- `/tmp/tg_split/CProof.lean`
- `/tmp/tg_split/Avail.lean`

Snapshot and imports:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract.lean and Submission.lean. Child types may therefore use only contract, SimonGMT and Mathlib names. The comparator scope is namespace GMT.Ch06 with the contract's opens.
- SimonGMT supplies the following:
  - CountablyRectifiable as countably many Lipschitz images plus an Hⁿ-null set, and HasWeightedApproximateTangentSpaceAt with uniqueness at θ(x) ≠ 0.
  - Lipschitz image bounds for μHE[n].
  - Area-formula critical-image and injective results (AreaCritical, AreaLipschitz, AreaDomain), Lusin (Chapter01.Lusin) and the upper density theorem 3.6 (Chapter01.DensityComparison). These modules are not imported by the contract but are prebuilt and may be added to the imports, as accepted nodes do.
  - Its Chapter02.WhitneyExtension module is not prebuilt, so it cannot be imported.
- SimonGMT lacks the chart-cover direction of Simon Lemma 1.2 (SubmanifoldCover proves only the easy direction), a tangential gradient for Lipschitz functions, and tangent identification on C¹ charts.
- Mathlib supplies Rademacher on sets (LipschitzOnWith.ae_differentiableWithinAt_of_mem), μHE[n] = volume on ℝⁿ, measurable_fderiv, measurableSet_of_differentiableAt, Lusin–Souslin images and measurable embeddings, Measurable.find, Egorov, and normDet_sq_eq_det_gram.

DAG and reuse:
- The chart-cover and chart-tangent lemmas exist in the DAG only as the speculative-ready lpf twins. Their types are byte-identical to the children chart_cover and chart_tangent, but they are not yet comparator-accepted, so fresh names are used.
- Many of the twins' leaves are comparator-accepted and are listed in the child proofs for reuse in those children's own decompositions.
- No accepted declaration has a type identical to any child. slicing_im_tg_* matches nowhere: not in the snapshot project, not in SimonGMT, not among the 360 DAG nodes.

Kernel checks:
- All four child types elaborate in the exact scope and pass the verifier's statement validator.
- The frozen parent type is proved from chart_cover, chart_tangent and chart_gradient; sorryAx comes only from the stubs.
- line_deriv is fully proved with standard axioms.

These checks do not certify the analytic proofs of chart_cover, chart_tangent and chart_gradient.
