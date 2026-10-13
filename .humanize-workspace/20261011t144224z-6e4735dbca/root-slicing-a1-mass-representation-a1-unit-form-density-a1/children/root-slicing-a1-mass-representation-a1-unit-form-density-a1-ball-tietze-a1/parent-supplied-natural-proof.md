# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1.unit_form_density-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.unit_form_density-a1.ball_tietze-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with its Borel σ-algebra; all measures are measures on this σ-algebra. H := EuclideanSpace ℝ (Fin N) with standard orthonormal basis e_i = EuclideanSpace.single i 1 (i ∈ Fin N), Euclidean norm ‖·‖ and inner product ⟨a, b⟩ = inner ℝ a b = Σ_i a_i b_i. Source: Simon, Introduction to GMT, Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, 1.17 (Lusin) and 4.14 (Riesz), as detailed in the supplied proof of the parent theorem smr_exists_unit_form_gt, whose steps are cited here as U1–U9; this argument is extracted from that proof. This is step U5 of the parent proof.

Let B := closedBall(0, 1) ⊆ H.
1. (Restriction to C.) Since u is continuous on C and u(C) ⊆ B, the map f : C → B, f(x) := u(x), is a continuous map from the subspace C ⊆ ℝ^P to the subspace B ⊆ H.
2. (Tietze extension.) ℝ^P is a metric space, hence normal, and C is closed. The closed unit ball B of the finite-dimensional real normed space H has the Tietze extension property (Mathlib instance Set.instTietzeExtensionUnitClosedBall in Mathlib.Analysis.Complex.Tietze, with 𝕜 = ℝ). Hence by ContinuousMap.exists_restrict_eq there is a continuous g : ℝ^P → B whose restriction to C is f (equivalently, ContinuousMap.exists_forall_mem_restrict_eq applied to f viewed as a map C → H with values in B gives a continuous g : ℝ^P → H with g(x) ∈ B for all x and g = f on C).
(Elementary alternative for step 2: each coordinate x ↦ u(x)_i is a continuous real function on the closed set C, so by the real Tietze extension theorem it extends to a continuous real function on ℝ^P; together these give a continuous F : ℝ^P → H with F = u on C. The radial retraction ρ(y) := y / max(1, ‖y‖) is continuous on H (the denominator is continuous and ≥ 1), satisfies ‖ρ(y)‖ = ‖y‖/max(1, ‖y‖) ≤ 1 and ρ(y) = y when ‖y‖ ≤ 1; so g := ρ ∘ F is continuous with values in B and g = u on C because u(C) ⊆ B.)
3. (Conclusion.) Let w(x) := g(x) ∈ H (composition of g with the continuous inclusion B ⊆ H). Then w is continuous, ‖w(x)‖ ≤ 1 for all x because g(x) ∈ B, and for x ∈ C, w(x) = f(x) = u(x). ∎

Formalization note (not part of the argument): add `import Mathlib.Topology.TietzeExtension` and `import Mathlib.Analysis.Complex.Tietze` (the latter provides TietzeExtension (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)); checked to compile with the frozen submission.

## Key steps

1. Restrict u to a continuous map f : C → closedBall(0,1).
2. Tietze for the closed unit ball of the finite-dimensional space ℝ^N (or coordinatewise Tietze followed by the radial retraction y ↦ y/max(1,‖y‖)) gives a continuous extension g : ℝ^P → closedBall(0,1).
3. w := g viewed in ℝ^N is continuous, ‖w‖ ≤ 1 and w = u on C.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean vs git show d8d46c9:GMT/Ch06/{Contract,Submission}.lean (identical, sha256 ea3ee0dd…)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') via verifier/gmt-compare.py (child scope: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06 …; noncomputable section; end)`
- `grep -rn 'def covectorEuclideanNorm|abbrev NVector|abbrev Covector' simongmt/Poincare/SimonGMT/`
- `grep -n 'theorem\|lemma' simongmt Chapter01/Lusin.lean (exists_isClosed_continuousOn_of_measurable: closed-set regularity hypothesis hreg, MeasurableSet A, nu A ≠ ∞, Measurable f, ε ≠ 0)`
- `grep -rn Lusin mathlib/Mathlib --include=*.lean -l (only Polish/Basic Lusin separation and Jacobian Lusin N; no Lusin continuity theorem)`
- `grep instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace, MeasurableSet.exists_lt_isCompact_of_ne_top, MeasurableSet.exists_isCompact_isClosed_sdiff_lt in Mathlib/MeasureTheory/Measure/{RegularityCompacts,Regular}.lean`
- `grep Set.instTietzeExtensionUnitClosedBall (Analysis/Complex/Tietze.lean); ContinuousMap.exists_restrict_eq, ContinuousMap.exists_forall_mem_restrict_eq (Topology/TietzeExtension.lean)`
- `grep exists_continuous_one_zero_of_isCompact (Topology/UrysohnsLemma.lean); IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, closure_thickening_subset_cthickening, closure_eq_iInter_thickening (Topology/MetricSpace/Thickening.lean); IsOpen.exists_iUnion_isClosed (Topology/MetricSpace/HausdorffDistance.lean)`
- `grep tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop (MeasureTheory/Measure/Continuity.lean); integral_inter_add_sdiff, norm_setIntegral_le_of_norm_le_const (MeasureTheory/Integral/Bochner/Set.lean)`
- `grep Measurable.inner (MeasureTheory/Function/SpecialFunctions/Inner.lean, not imported by Submission); scoped inner notation and class Inner (Analysis/InnerProductSpace/Defs.lean)`
- `python3 over dag.json nodes lean_name/lean_statement (212 nodes): smr_covector_coord_isometry type, smr_* siblings, lpf_wtc_lusin_compact_pieces, slicing_mb_cutoff, isoperimetric_lattice_face_cutoff; grep -rl smr_ufd_* in dag.json, nodes/, simongmt (no matches)`
- `sed -n 255,320p book/sources/chapter-06-source.txt (Simon 2.7–2.9 text)`
- `lake build GMT.Ch06.Submission in scratch /tmp/ufd-split-IpAAXq (frozen d8d46c9, shared packages lake-packages-25730c7c)`
- `lake env lean Scratch/Children.lean, Scratch/Challenges.lean (5 child types in comparator scope), Scratch/Assembly.lean and Scratch/Assembly2.lean (#print axioms), Scratch/Avail.lean and Scratch/Avail2.lean (import availability), Scratch/Child{1..5}/Proof.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-unit-form-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-unit-form-density-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/tmp/ufd-split-IpAAXq/Scratch/Challenges.lean`
- `/tmp/ufd-split-IpAAXq/Scratch/Assembly2.lean`
- `/tmp/ufd-split-IpAAXq/Scratch/Child1/Proof.lean`
- `/tmp/ufd-split-IpAAXq/Scratch/Child2/Proof.lean`
- `/tmp/ufd-split-IpAAXq/Scratch/Child3/Proof.lean`
- `/tmp/ufd-split-IpAAXq/Scratch/Child4/Proof.lean`
- `/tmp/ufd-split-IpAAXq/Scratch/Child5/Proof.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the frozen Contract and Submission. Child types therefore use only contract names, SimonGMT names (Covector, NVector, covectorEuclideanNorm) and Mathlib names.

Available under the base import GMT.Ch06.Submission:
- measure_inter_conull, tendsto_measure_iUnion_atTop and tendsto_measure_iInter_atTop;
- IsCompact.exists_cthickening_subset_open and closure_thickening_subset_cthickening;
- Urysohn (exists_continuous_one_zero_of_isCompact);
- integral_inter_add_sdiff, norm_setIntegral_le_of_norm_le_const and LinearMap.continuous_of_finiteDimensional.

The following need extra imports, each checked to compile with the frozen submission:
- the Polish inner-regularity instance InnerRegularCompactLTTop and MeasurableSet.exists_lt_isCompact_of_ne_top / exists_isCompact_isClosed_sdiff_lt (RegularityCompacts);
- SimonGMT Lusin (Chapter01/Lusin; Mathlib has no Lusin continuity theorem);
- Tietze, ContinuousMap.exists_restrict_eq and the closed-unit-ball instance (TietzeExtension, Complex.Tietze).

Measurable.inner is not imported, so use continuous_inner. The ⟪·,·⟫_ℝ notation is scoped, so the types write inner ℝ.

No existing declaration matches any proposed child type. The Lusin and cutoff nodes in other branches have different types, so fresh smr_ufd_* names are used; none occurs in dag.json, nodes/, SimonGMT or Mathlib.

All five child types elaborate in the comparator child scope. The parent's exact frozen type is kernel-checked from the sibling isometry type and the five child types with axioms [propext, Classical.choice, Quot.sound]. Each child also has a sorry-free scratch proof with standard axioms.
