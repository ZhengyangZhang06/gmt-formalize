# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.dilation-a1`
- Child DAG node: `root.deformation-a1.dilation-a1.mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 3 and 4 (Simon 2.23 with |η_ρ^#ω| = ρ^k|ω∘η_ρ|).
Sibling used: deformation_dilation_calculus, first conjunct. For σ > 0, every test k-form ω has a test k-form η with η(x) = σ^k • ω(σ • x) for all x.

Conventions and definitions.
- ℝ^N := Eucl N; test forms are elements of TestFormOn univ k.
- SimonGMT Chapter06.Mass: T.mass = T.massOn univ = sSup {ENNReal.ofReal(T ω) : ω ∈ massAdmissibleOn univ k univ}.
- ω ∈ massAdmissibleOn univ k univ iff tsupport ω ⊆ univ and covectorEuclideanNorm(ω(x)) ≤ 1 for every x.
- GeometricCurrentOn.le_massOn: ENNReal.ofReal(T ω) ≤ T.massOn W for every ω ∈ massAdmissibleOn univ k W.
- σ-pair: for σ > 0 and A, B ∈ GeometricCurrentOn univ k, (A, B) is a σ-pair if B(ω) = A(η) for all test forms ω, η with η(x) = σ^k • ω(σ • x) for all x.
- By hypothesis, (X, Y) is a ρ-pair.

1. General inequality. If σ > 0 and (A, B) is a σ-pair, then B.mass ≤ ENNReal.ofReal(σ^k)·A.mass. By sSup_le it suffices to prove ENNReal.ofReal(B ω) ≤ ENNReal.ofReal(σ^k)·A.mass for every admissible ω. Fix one.
(a) By deformation_dilation_calculus N σ hσ k (first conjunct), there is a test form η with η(x) = σ^k • ω(σ • x) for all x.
(b) Put η′ := (σ^k)⁻¹ • η. It is a test form, since TestFormOn univ k is a submodule. Since σ^k ≠ 0, η′(x) = (σ^k)⁻¹ • σ^k • ω(σ • x) = ω(σ • x) for every x (smul_smul, inv_mul_cancel₀, one_smul).
(c) η′ is admissible. tsupport η′ ⊆ univ, and covectorEuclideanNorm(η′(x)) = covectorEuclideanNorm(ω(σ • x)) ≤ 1 for every x, by admissibility of ω at σ • x. Hence ENNReal.ofReal(A η′) ≤ A.mass.
(d) As test forms, η = σ^k • η′ (smul_smul, mul_inv_cancel₀, one_smul). By the σ-pair property and linearity of A (map_smul), B ω = A η = σ^k·A η′.
(e) Since σ^k ≥ 0, ENNReal.ofReal(σ^k·A η′) = ENNReal.ofReal(σ^k)·ENNReal.ofReal(A η′) (ENNReal.ofReal_mul, valid whatever the sign of A η′). By (c) and monotonicity of multiplication in [0, ∞], this is ≤ ENNReal.ofReal(σ^k)·A.mass.
[Lean: after rintro _ ⟨ω, hω, rfl⟩, start with `show ENNReal.ofReal (B ω) ≤ _`.]

2. Inverse pair. (Y, X) is a ρ⁻¹-pair: X(ω′) = Y(η′) for all test forms ω′, η′ with η′(x) = (ρ⁻¹)^k • ω′(ρ⁻¹ • x) for all x.
- For every x, ρ^k • η′(ρ • x) = ρ^k • (ρ⁻¹)^k • ω′(ρ⁻¹ • ρ • x) = (ρ·ρ⁻¹)^k • ω′(x) = ω′(x) (smul_smul, mul_pow, mul_inv_cancel₀, one_pow, one_smul, inv_smul_smul₀).
- So the pair (ω, η) := (η′, ω′) satisfies η(x) = ρ^k • ω(ρ • x) for all x, and the ρ-pair hypothesis gives Y(η′) = X(ω′).
- No existence statement is used here.

3. Two inequalities.
- Step 1 with (σ, A, B) := (ρ, X, Y) gives Y.mass ≤ ENNReal.ofReal(ρ^k)·X.mass.
- Step 1 with (σ, A, B) := (ρ⁻¹, Y, X) is legitimate by step 2 and ρ⁻¹ > 0; it uses deformation_dilation_calculus N ρ⁻¹ (inv_pos.2 hρ) k. It gives X.mass ≤ ENNReal.ofReal((ρ⁻¹)^k)·Y.mass.

4. Multiply the second inequality by ENNReal.ofReal(ρ^k); multiplication is monotone in [0, ∞]:
ENNReal.ofReal(ρ^k)·X.mass ≤ ENNReal.ofReal(ρ^k)·(ENNReal.ofReal((ρ⁻¹)^k)·Y.mass)
= ENNReal.ofReal(ρ^k·(ρ⁻¹)^k)·Y.mass
= ENNReal.ofReal(1)·Y.mass = Y.mass
(mul_assoc, ENNReal.ofReal_mul with ρ^k ≥ 0, mul_pow, mul_inv_cancel₀, one_pow, ENNReal.ofReal_one, one_mul).

5. By steps 3 and 4 and antisymmetry (le_antisymm), Y.mass = ENNReal.ofReal(ρ^k)·X.mass. All quantities live in [0, ∞], so this also covers X.mass = ∞ or Y.mass = ∞. ∎

Template (optional). Step 1 is the argument of Submission.ind_rs_massOn_dilation_le for the map y ↦ r⁻¹(y − x), on branch proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-mass-bound-a1-2746022a44. That declaration has a different frozen type, so do not cite it. Auxiliary lemmas need globally unique names.

## Key steps

1. General half: for a σ-pair (A, B), each admissible ω for B yields the admissible form η′ = σ^{−k}·(σ-pull-back of ω) = ω(σ·) for A (sibling calculus). Since B ω = σ^k·A η′, M(B) ≤ σ^kM(A).
2. (X, Y) a ρ-pair implies (Y, X) is a ρ⁻¹-pair, by pure algebra: ω′(x) = ρ^kη′(ρx).
3. Apply the half with (ρ, X, Y) and with (ρ⁻¹, Y, X), multiply by ofReal(ρ^k), use ρ^kρ^{−k} = 1, and conclude with le_antisymm in [0, ∞].

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in lake-packages-25730c7c/simongmt and .lake/packages/simongmt (2b3663083f3fe399b6296fb8eaee52169170e197 = lakefile.toml rev)`
- `cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (byte-identical)`
- `python3 -I over dag.json: lean_statement of root.deformation-a1.dilation-a1 == selected frozen type == handoff lean_statement (True); six proposed names vs all 554 lean_names (no collision)`
- `rg -n 'deformation_dilation_(calculus|hausdorff|mass|support|integer_multiplicity|lattice_chain)' local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt (no match, exit 1); git grep -l 'deformation_dilation_' -- '*.lean' over all 2352 refs (no match)`
- `grep -n '^theorem|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean (affinePullbackForm:35, affinePullbackTestOn:65, iteratedFDeriv_affinePullbackForm:109, TestFormOnConverges.affinePullback:127, exteriorDerivative_affinePullbackForm:147, GeometricCurrentOn.affinePushforward:172, boundary_affinePushforward:188)`
- `cat simongmt Chapter06/Currents.lean, Mass.lean, CurrentLocalEquality.lean, FormsDuality.lean, Forms.lean; grep -n 'def blowUpMap|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable' Chapter03/Rectifiable.lean (lines 96, 330, 34)`
- `rg -n 'euclideanHausdorffMeasure_smul₀|def MeasureTheory.Measure.euclideanHausdorffMeasure' mathlib/Mathlib (Geometry/Euclidean/Volume/Measure.lean:152, :67)`
- `rg -n 'theorem (MeasurePreserving\.)?(setIntegral_image_emb|integrableOn_image|restrict_image_emb)|aestronglyMeasurable_map_iff|theorem ae_map_iff|theorem extDeriv_pullback|theorem map_smul_univ|theorem image_compl_eq|theorem ae_smul_measure|theorem integral_smul_measure' mathlib/Mathlib (Integral/Bochner/Set.lean:576, Integral/IntegrableOn.lean:324, Dynamics/Ergodic/MeasurePreserving.lean:86, StronglyMeasurable/AEStronglyMeasurable.lean:668, Measure/Restrict.lean:887, Calculus/DifferentialForm/Basic.lean:259, Topology/Algebra/Module/Alternating/Basic.lean:518, Data/Set/Image.lean:372, Measure/Module.lean:191, Integral/Bochner/Basic.lean:1052)`
- `python3 over dag.json for integrality_weak_limits-a1.integer_density-a1.rescale-a1 children (ind_rs_dilation_measurePreserving, ind_rs_massOn_dilation_le, ind_rs_tauAction_dilation, ind_rs_weightedTangent_dilation accepted; ind_rs_rectifiableTriple_dilation comparing; all for y ↦ r⁻¹(y − x), different frozen types); git show <triple-image and tau-action branches>:GMT/Ch06/Submission.lean (proof templates)`
- `header imports of GMT/Ch06/Submission.lean on all theorems/solutions/* branches (accepted solutions add imports, e.g. Poincare.SimonGMT.Chapter02.AreaDomain x7); sed -n 334,372p verifier/gmt-compare.py (candidate_inputs byte-checks only frozen files other than Submission.lean)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the six child statements and the parent (all valid, returned unchanged)`
- `lake env lean /tmp/dil-decomp-6e47/Scratch/NC_<key>.lean for the six keys in the exact comparator scope (all exit 0, only the expected sorry warning); Assembly.lean (dilation_assembly: [propext, Classical.choice, Quot.sound]); Proto_calculus, Proto_hmass, Proto_support, Proto_im, Proto_lattice and EndToEnd.lean (sha256 3f159720…; exit 0, 0 errors; all seven Submission declarations [propext, Classical.choice, Quot.sound])`
- `sed -n '385,440p;1450,1475p' book/chapter-06.txt (2.23 f_#T(ω) = T(ζ f^#ω), 2.24(1) ∂f_#T = f_#∂T, ‘scaled version … changing scale … then changing scale back by x → ρx’)`
- `web search: scaling of Hausdorff measure H^s(λA) = λ^s H^s(A) (Wikipedia ‘Hausdorff measure’; Imperial College M345PA46 notes ch. 2, similarity scaling via δ-covers); Evans–Gariepy theorem number could not be verified, so not cited`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dil-decomp-6e47/stmts.json`
- `/tmp/dil-decomp-6e47/Scratch/Assembly.lean`
- `/tmp/dil-decomp-6e47/Scratch/EndToEnd.lean`
- `/tmp/dil-decomp-6e47/logs/EndToEnd.log`
- `/tmp/dil-decomp-6e47/logs/Assembly.log`
- `/tmp/dil-decomp-6e47/logs/NC_calculus.log`
- `/tmp/dil-decomp-6e47/logs/NC_hausdorff.log`
- `/tmp/dil-decomp-6e47/logs/NC_mass.log`
- `/tmp/dil-decomp-6e47/logs/NC_support.log`
- `/tmp/dil-decomp-6e47/logs/NC_integer_multiplicity.log`
- `/tmp/dil-decomp-6e47/logs/NC_lattice_chain.log`

The pinned revisions are confirmed, and Contract = Submission = the snapshot Contract byte for byte. No project, SimonGMT or Mathlib declaration already proves the selected statement. The pinned simongmt module Poincare.SimonGMT.Chapter06.AffineCurrentPushforward supplies all of the push-forward calculus for proper affine maps: the pull-back test-form map, its sequential continuity, the push-forward current, and commutation with d. It is not in the frozen import closure, but Submission.lean may add the import, since only the other frozen files are byte-checked and accepted solutions already add imports. Mathlib supplies Measure.euclideanHausdorffMeasure_smul₀ (μHE[k](r•S) = ‖r‖₊^k μHE[k] S) and the measure-preserving-embedding toolkit used by the children. The accepted ind_rs_* dilation lemmas concern y ↦ r⁻¹(y − x), have different frozen types and belong to another branch, so they are only optional templates. The six child names are globally unused. All six statements validate and elaborate in the comparator scope. The parent's exact type follows from them with standard axioms only, and a complete end-to-end prototype of every child plus the parent compiles with [propext, Classical.choice, Quot.sound].
