# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.uniform_lipschitz_near_compact-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^m = EuclideanSpace ℝ (Fin m) (Lean `Eucl m`) with Euclidean norm |·| = ‖·‖; L(E, F) is the space of (continuous) linear maps with the operator norm; Hⁿ = μHE[n] is Mathlib's normalized n-dimensional Hausdorff measure (on ℝⁿ it equals Lebesgue measure Lⁿ = volume); B_ρ(x) is the open ball. This is the uniform-Lipschitz part of Step 6 of the parent proof. Hypotheses: U ⊆ ℝ^P open; f : ℝ^P → ℝ^Q locally Lipschitz on U (for every z ∈ U there are C_z ≥ 0 and a neighbourhood t of z within U on which f is C_z-Lipschitz); K ⊆ U compact. We find C ≥ 0 and ρ > 0 such that for all x ∈ K: B_ρ(x) ⊆ U and f is C-Lipschitz on B_ρ(x).

1. (Empty case.) If K = ∅, take C := 0 and ρ := 1; the condition on x ∈ K is vacuous. Assume K ≠ ∅ from now on.

2. (A good ball around each point of K.) Let z ∈ K. Then z ∈ U. Since U is open, the neighbourhoods of z within U are ordinary neighbourhoods of z, so there are C_z ≥ 0 and a neighbourhood t_z of z with f C_z-Lipschitz on t_z. Choose ε_z > 0 with B_{ε_z}(z) ⊆ t_z ∩ U (both t_z and U are neighbourhoods of z) and put r_z := ε_z/2 > 0. Then B_{2r_z}(z) ⊆ U and f is C_z-Lipschitz on B_{2r_z}(z).

3. (Finite subcover.) The open balls B_{r_z}(z), z ∈ K, cover the compact set K, so there are finitely many points z_1, …, z_m ∈ K (m ≥ 1) with K ⊆ B_{r_1}(z_1) ∪ … ∪ B_{r_m}(z_m), where r_l := r_{z_l}. Put ρ := min_l r_l > 0 and C := max_l C_{z_l} ≥ 0.

4. (Uniform conclusion.) Let x ∈ K and choose l with x ∈ B_{r_l}(z_l). For y ∈ B_ρ(x): |y − z_l| ≤ |y − x| + |x − z_l| < ρ + r_l ≤ 2r_l, so B_ρ(x) ⊆ B_{2r_l}(z_l). Hence B_ρ(x) ⊆ U (step 2), and f is C_{z_l}-Lipschitz, hence C-Lipschitz (C ≥ C_{z_l}), on B_ρ(x) as a subset of B_{2r_l}(z_l). This holds for every x ∈ K with the same C and ρ. ∎

(Alternative route with the same conclusion, convenient in Lean: choose δ > 0 with the closed δ-thickening K_δ of K contained in U (Mathlib IsCompact.exists_cthickening_subset_open); K_δ is compact (IsCompact.cthickening), f is locally Lipschitz on K_δ (LocallyLipschitzOn.mono) hence C-Lipschitz on K_δ (LocallyLipschitzOn.exists_lipschitzOnWith_of_compact); take ρ := δ and use B_δ(x) ⊆ closedBall(x, δ) ⊆ K_δ ⊆ U for x ∈ K.)

## Key steps

1. Each z ∈ K has r_z > 0 with B_{2r_z}(z) ⊆ U and f C_z-Lipschitz on B_{2r_z}(z) (U open, f locally Lipschitz on U).
2. Finitely many balls B_{r_z}(z) cover K; set ρ := min r_l and C := max C_l.
3. For x ∈ K in B_{r_l}(z_l): B_ρ(x) ⊆ B_{2r_l}(z_l) ⊆ U and f is C-Lipschitz on B_ρ(x).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean and Submission.lean (all identical)`
- `python3 over dag.json: list lean_name/lean_statement of root.lipschitz_pushforward_im-a1 children and all 235 lean_names; check lpf_tde_* candidates (no match); inspect lpf_c1_local_antilipschitz, lpf_lipschitz_localization, lpf_lli_countable_lipschitz_cover, lpf_raf_chart_preimage_null, lpf_raf_lla_disjoint_lipschitz_pieces, lpf_wtc_cat_fderiv_lower_bound (none has an identical type)`
- `grep -rn lpf_tde GMT/ issue-workers.json DAG.md /tmp/all_names.json (no match)`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') -> child scope prefix; verifier/lean_contract.validate_lean_statement on the 5 child statements (all valid)`
- `grep -n 'def |theorem ' simongmt Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt.unique), Chapter03/Differential.lean, Chapter02/Lipschitz.lean (rademacher_ae_differentiableAt, euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `grep Mathlib/Analysis/Calculus/Rademacher.lean (LipschitzOnWith.ae_differentiableWithinAt_of_mem); rg 'LocallyLipschitzOn' (LocallyLipschitzOn.exists_lipschitzOnWith_of_compact)`
- `grep measurable_fderiv Mathlib/Analysis/Calculus/FDeriv/Measurable.lean; ContinuousLinearMap.instMeasurableSpace (borel) in MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean; Measurable.find in MeasureTheory/MeasurableSpace/Constructions.lean`
- `grep NormedRing.inverse_continuousAt (Analysis/Normed/Ring/Units.lean); adjoint API incl. adjoint_comp_self_injective_iff (Analysis/InnerProductSpace/Adjoint.lean)`
- `grep IsCompact.exists_cthickening_subset_open (Topology/MetricSpace/Thickening.lean); TopologicalSpace.isOpen_biUnion_countable (Topology/Bases.lean); EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean)`
- `grep MeasurableSet.image_of_continuousOn_injOn (MeasureTheory/Constructions/Polish/Basic.lean); ContinuousOn.measurable_piecewise, Continuous.measurable2 (BorelSpace/Basic.lean); hasDerivAt_iff_isLittleO, HasDerivAt.le_of_lip' (Deriv/Basic.lean); HasFDerivAt.comp_hasDerivAt_of_eq (Deriv/Comp.lean); hasDerivAt_iff_tendsto_slope (Deriv/Slope.lean)`
- `no-match: rg 'IsOpen.isSigmaCompact|IsSigmaCompact.measurableSet' in Mathlib snapshot (absent; Lusin–Souslin used instead)`
- `sed -n 320,400p book/chapter-03.txt (Simon Ch. 3 §2, 2.1–2.2)`
- `lake build GMT.Ch06.Submission; lake env lean /tmp/tde-decomp/{Stmts,Assembly,Proofs,ProofC1,ProofC3,ProofC5,Combined,FinalCheck,AssemblyExact}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tde-decomp/scope_prefix.txt`
- `/tmp/tde-decomp/Stmts.lean`
- `/tmp/tde-decomp/AssemblyExact.lean`
- `/tmp/tde-decomp/FinalCheck.lean`
- `/tmp/tde-decomp/Combined.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract. It is byte-identical to the workspace Contract and Submission.

In the comparator child scope (import GMT.Ch06.Submission plus the namespace and opens from contract_scope), the five proposed child statements elaborate and pass the lexical validator. The lpf_tde_* names are unused in the DAG, and no existing node has an identical type.

What the proofs rely on:
- **SimonGMT:** HasWeightedApproximateTangentSpaceAt and its .unique, Rademacher, and the Lipschitz image bound for μHE (Chapter02/Lipschitz euclideanHausdorffMeasure_image_le_of_lipschitzOn).
- **Mathlib, analysis:** LipschitzOnWith.ae_differentiableWithinAt_of_mem, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, IsCompact.exists_cthickening_subset_open, hasDerivAt_iff_isLittleO, HasDerivAt.le_of_lip'.
- **Mathlib, measurability:** measurable_fderiv (valid for an arbitrary f), the Borel instance on continuous linear maps, Measurable.find, Lusin–Souslin MeasurableSet.image_of_continuousOn_injOn, and μHE[n] = volume on Eucl n.
- **Mathlib, linear algebra:** NormedRing.inverse_continuousAt and the adjoint API.

IsOpen.isSigmaCompact and IsSigmaCompact.measurableSet are absent from this snapshot, so the C5 proof uses Lusin–Souslin (or the elementary rational-ball σ-compact argument) instead.

Kernel checks: the parent's exact frozen type was derived from the 5 child types plus the 2 uncle DAG types, with sorryAx coming only from those stubs. All 5 child statements were proved in scratch Lean using only propext, Classical.choice and Quot.sound.
