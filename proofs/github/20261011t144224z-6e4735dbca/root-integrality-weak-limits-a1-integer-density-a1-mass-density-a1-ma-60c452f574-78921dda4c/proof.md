# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1.mass_measure_ball_values-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 3 and 4 of the supplied proof of ind_md_mass_measure_balls (itself Step 1, (1a)–(1b), of the proof of ind_mass_density_bound), applied to an arbitrary given mass measure μ. Cf. Simon Ch. 6, 2.8: μ_T(W) = M_W(T) for W ⊂⊂ U, and in particular μ_T(U) = M(T).

Conventions.
- ℝ^P := Eucl P = EuclideanSpace ℝ (Fin P).
- M_W(T) := T.massOn W for W ⊆ ℝ^P. This is the supremum in [0, ∞] of ofReal(T(ω)) over test forms ω with tsupport ω ⊆ W and covectorEuclideanNorm(ω(x)) ≤ 1 for all x (GeometricCurrentOn.massOn).
- M(T) := T.mass, which by definition (GeometricCurrentOn.mass) is M_{ℝ^P}(T) = T.massOn univ.
- 'W ⊂⊂ ℝ^P' means CompactlyContainedOpen W univ: W is open, closure W is compact, and closure W ⊆ univ.
- IsMassMeasure T μ (contract definition, U = univ) means μ(univᶜ) = 0 and μ(W) = M_W(T) for every W ⊂⊂ ℝ^P.
- B_r(x) := ball x r.

1. Monotonicity of local mass. Let W ⊆ ℝ^P. Since W ⊆ univ, every form admissible for M_W(T) is admissible for M_univ(T). So GeometricCurrentOn.massOn_mono gives M_W(T) ≤ M_univ(T) = M(T).

2. Open balls are compactly contained in ℝ^P. Fix x ∈ ℝ^P and r ∈ ℝ.
 (a) ball x r is open (isOpen_ball).
 (b) closure(ball x r) ⊆ closedBall x r (closure_ball_subset_closedBall: closedBall x r is closed and contains ball x r).
 (c) ℝ^P is a finite-dimensional real normed space, hence a proper metric space, so closedBall x r is compact (isCompact_closedBall).
 (d) closure(ball x r) is closed (isClosed_closure) and, by (b), contained in the compact set closedBall x r. So it is compact (IsCompact.of_isClosed_subset).
 (e) closure(ball x r) ⊆ univ trivially.
 Hence CompactlyContainedOpen (ball x r) univ. This also holds when r ≤ 0: then ball x r = ∅ and the same argument applies verbatim.

3. Ball values. By step 2 and the second component of IsMassMeasure T μ, μ(ball x r) = T.massOn (ball x r) for all x ∈ ℝ^P and r ∈ ℝ. This is the second conclusion.

4. Exhaustion by balls. For k ∈ ℕ put B_k := ball 0 (k : ℝ).
 - If k ≤ k′ then (k : ℝ) ≤ (k′ : ℝ) (Nat.cast_le), so B_k ⊆ B_{k′} (ball_subset_ball). Thus k ↦ B_k is monotone.
 - ⋃_k B_k = ℝ^P (iUnion_ball_nat): for y ∈ ℝ^P, the Archimedean property gives a natural k > dist y 0, and then y ∈ B_k.

5. Continuity from below. For a monotone sequence of sets indexed by ℕ, μ(⋃_k B_k) = sup_k μ(B_k) (Monotone.measure_iUnion). With step 4, μ(ℝ^P) = μ(⋃_k B_k) = sup_k μ(B_k).
 Lean remark: rewrite only the measured set, for example with calc μ univ = μ (⋃ k : ℕ, ball (0 : Eucl P) k) := by rw [iUnion_ball_nat]. A global rewrite of univ also hits the current's domain inside T.mass and fails with a motive error.

6. Total-mass bound. For each k, step 3 (with x = 0, r = k) and step 1 (with W = B_k) give μ(B_k) = M_{B_k}(T) ≤ M(T). Hence sup_k μ(B_k) ≤ M(T) (iSup_le), and by step 5 μ(ℝ^P) ≤ M(T). This is the first conclusion.

7. Steps 3 and 6 are the two conclusions. Neither the first component of IsMassMeasure (μ(univᶜ) = 0) nor any finiteness of M(T) is used. ∎

## Key steps

1. For every W ⊆ ℝ^P, M_W(T) ≤ M(T) (massOn_mono, since W ⊆ univ).
2. Every open ball ball x r (any r ∈ ℝ) is CompactlyContainedOpen in univ: it is open, and its closure is a closed subset of the compact closed ball closedBall x r (ℝ^P is proper).
3. The second component of IsMassMeasure T μ gives μ(ball x r) = T.massOn (ball x r).
4. The balls ball 0 k (k ∈ ℕ) increase and exhaust ℝ^P (ball_subset_ball, iUnion_ball_nat), so μ(ℝ^P) = sup_k μ(ball 0 k) (Monotone.measure_iUnion).
5. Each μ(ball 0 k) = M_{ball 0 k}(T) ≤ M(T), hence μ(ℝ^P) ≤ M(T).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean and the snapshot Mathlib files below against the compiled workspace/.lake copies (all identical): MeasureTheory/Measure/Continuity.lean, MeasureTheory/Measure/Typeclasses/Finite.lean, Geometry/Manifold/PartitionOfUnity.lean, Topology/MetricSpace/Pseudo/Defs.lean`
- `cmp lake-packages-25730c7c simongmt Chapter06/{Mass,Currents}.lean and Chapter01/{VectorFunctionalEnvelope,RadonPolarRepresentation}.lean against the .lake/packages/simongmt copies (identical)`
- `grep -rn 'theorem exists_contDiff_support_eq_eq_one_iff|theorem ext_of_generate_finite|theorem iUnion_ball_nat|Monotone.measure_iUnion' snapshot mathlib/Mathlib`
- `grep -n 'def massOn|def mass|massOn_mono|le_massOn|TestFormOnConverges|structure GeometricCurrentOn|GeometricCurrentOn.ext' SimonGMT Chapter06/{Mass,Currents}.lean; sed Chapter06/{Forms,FormsDuality}.lean (Covector, DifferentialForm, IsTestForm, NVector)`
- `grep -n 'simon_theorem_4_14|vectorFunctionalEnvelopeMeasure|simon_theorem_4_14_positive_envelope|simon_theorem_4_14_bounded_caratheodory|IsLocallyBoundedCcFunctional|radonCaratheodoryMeasure' SimonGMT Chapter01/*.lean`
- `python3 -I scan of dag.json: lean_statements mentioning IsMassMeasure or massOn (ball; record of iwl_restriction_theory (status accepted, candidate b9f9acdc); occurrences of ind_md_* (ind_md_mmb_massMeasure_balls: 0)`
- `python3 -I scan of nodes/*/decomposition-v*.json and audits reusing iwl_restriction_theory or rectifiability_mass_measure_representation; this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json and parent-child-handoff.json`
- `git show d55387547b3a9f71614ac268bb0ba5c14d727a62:GMT/Ch06/Submission.lean | grep -c 'theorem Submission.' (0)`
- `git show b9f9acdc41eaa29f36e54d7e570ae94d8ca8b4a6:GMT/Ch06/Submission.lean: iwl_restriction_theory at line 927; helper blocks intOn, R0, setInt, R1, restrCur, massLe, massEq, extL, core; cited lemmas cmb_*, slicing_ru_*, polyhedral_approx_pairing_coordinate_bound`
- `grep in runtime.py: _existing_lean_name_problem, _solve_children (existing_by_name, parent.children), _overlay_accepted_children, _accepted_checkpoint; grep store.py: ensure`
- `python3 -I verifier/gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on both child types and the parent`
- `lake env lean /tmp/mmb-decomp-v2/{Challenge_c1,Challenge_c2,Challenge_parent,Assembly,Solutions}.lean with #print axioms`
- `sed -n 1510,1750p book/chapter-01.txt (Simon 4.12–4.14 and display (∗)); sed -n 230,300p book/chapter-06.txt (Simon 2.5–2.10)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalL1.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-046d2fc55f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-046d2fc55f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-046d2fc55f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/iwl_accepted_Submission.lean`
- `/tmp/mmb-decomp-v2/Assembly.lean`
- `/tmp/mmb-decomp-v2/Solutions.lean`

The snapshot is project d8d46c95 with Mathlib 25730c7c. Its frozen Ch06 Contract and Submission are byte-identical to the compiled workspace copies, and so are the Mathlib and SimonGMT files used.

The supplied proof is supported locally:
- SimonGMT GeometricCurrentOn.mass := massOn U, and massOn_mono (Chapter06/Mass.lean).
- Mathlib iUnion_ball_nat (Pseudo/Defs.lean:410), Monotone.measure_iUnion (Continuity.lean:71), closure_ball_subset_closedBall, isCompact_closedBall and IsCompact.of_isClosed_subset.

Submission.iwl_restriction_theory is absent from this node's proof base d5538754, which has no Submission theorems. It is present at accepted candidate b9f9acdc, line 927. The controller overlays only accepted children and dependencies (_overlay_accepted_children), so the byte-identical reuse child is required; _existing_lean_name_problem and _accepted_checkpoint permit it.

The repaired natural proof of that child follows Simon Ch. 1, 4.12–4.14 (chapter-01.txt lines 1522–1745, display (∗)) and Ch. 6, 2.7–2.9 (chapter-06.txt lines 264–290). It is backed by:
- SimonGMT vectorFunctionalEnvelopeMeasure (a regular measure), simon_theorem_4_14_positive_envelope = (∗), and simon_theorem_4_14_bounded_caratheodory (|ν| ≤ 1);
- Mathlib exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789) and ext_of_generate_finite (Typeclasses/Finite.lean:458);
- accepted helpers in b9f9acdc: cmb_exists_compactly_contained_exhaustion, cmb_exists_testForm_uniform_approx, cmb_abs_apply_le_of_massOn_le, cmb_covector_eq_sum_coord_smul_wedge, polyhedral_approx_pairing_coordinate_bound, slicing_ru_smooth_to_continuous and slicing_ru_continuous_to_bounded.

The new name ind_md_mmb_massMeasure_balls has no match in dag.json, the snapshot or SimonGMT.

Lean checks in /tmp/mmb-decomp-v2:
- All three frozen types elaborate in the replayed contract scope.
- On the accepted b9f9acdc Submission, Assembly.lean proves the new child and the exact parent type from the real iwl_restriction_theory, with 0 errors.
- The comparator-style `exact Submission.<name>` templates resolve.
- The only axioms are propext, Classical.choice and Quot.sound.
