# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.diffeo_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof. Simon 6.3.7 (chapter-06.txt lines 822–831) uses, without proof, that at H^n-a.e. point the approximate tangent space of f(M) is spanned by the images d^M f_x(τ_i); for the C¹ diffeomorphism φ this is supplied here from the siblings, with the details filled in. Notation: E := ℝ^P, H^n := μHE[n], λ := Lebesgue measure on ℝ^n (= μHE[n] there), Q(x) := approxTangentPlane n M x (by definition the chosen plane P with HasApproximateTangentSpaceAt n M x P when one exists, ⊥ otherwise). Replacing Λ by max(Λ, 1) (both Lipschitz and antilipschitz bounds survive enlarging the constant) we assume Λ ≥ 1. Provenance: this statement and its frozen Lean type are byte-identical to Submission.dpf_approxTangent_bilipschitz_image_ae (node root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1, not yet accepted, owned by another parent); the proof below is that node's parent-supplied proof with the sibling density lemma renamed to codim1_ldr_dpf_approxTangent_ae_bilipschitz_piece, and it does not use that node.
1. Pieces. By the sibling dpf_rectifiable_bilipschitz_pieces (M Borel, countably n-rectifiable) there are Lipschitz F_i (with constants L_i), Borel B_i ⊆ ℝ^n and m_i > 0 with m_i|a − a'| ≤ |F_i a − F_i a'| on B_i, F_i differentiable with injective derivative on B_i, P_i := F_i(B_i) Borel ⊆ M pairwise disjoint, and Z := M ∖ ⋃_i P_i H^n-null.
2. Tangent planes of M along the pieces. Apply the sibling codim1_ldr_dpf_approxTangent_ae_bilipschitz_piece with Y := M (Borel, ⊆ U, H^n(M ∩ C) < ∞ for compact C ⊆ U) and (F_i, B_i, L_i, m_i) (F_i(B_i) ⊆ M): for λ-a.e. b ∈ B_i, HasApproximateTangentSpaceAt n M (F_i b) (range DF_i(b)). For such b the existential in the definition of approxTangentPlane holds, so HasApproximateTangentSpaceAt n M (F_i b) Q(F_i b) (Exists.choose_spec), and by uniqueness of approximate tangent planes (SimonGMT HasApproximateTangentSpaceAt.unique; Simon Ch. 3 1.5(1)) Q(F_i b) = range DF_i(b).
3. Properties of φ(M). φ is continuous and injective (antilipschitz), so φ(M) is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn). Since φ^{-1}(U) = U, x ∈ M ⊆ U implies φ(x) ∈ U, so φ(M) ⊆ U. For compact C ⊆ U: φ^{-1}(C) is closed (φ continuous) and bounded (|x − x₀| ≤ Λ|φ(x) − φ(x₀)| for a fixed x₀), hence compact, and φ^{-1}(C) ⊆ φ^{-1}(U) = U; as φ(M) ∩ C ⊆ φ(M ∩ φ^{-1}(C)), H^n(φ(M) ∩ C) ≤ Λ^n H^n(M ∩ φ^{-1}(C)) < ∞ (LipschitzWith.hausdorffMeasure_image_le; μHE[n] is a fixed multiple of μH[n]).
4. Tangent planes of φ(M) along the pieces. Φ_i := φ∘F_i is (ΛL_i)-Lipschitz; for a, a' ∈ B_i, |Φ_i(a) − Φ_i(a')| ≥ Λ^{-1}|F_i(a) − F_i(a')| ≥ (m_i/Λ)|a − a'|; at b ∈ B_i, φ is differentiable at F_i(b) (φ is C¹) and F_i at b, so DΦ_i(b) = Dφ(F_i b)∘DF_i(b) (chain rule, fderiv_comp), which is injective as a composition of injective maps; Φ_i(B_i) ⊆ φ(M). Apply the sibling codim1_ldr_dpf_approxTangent_ae_bilipschitz_piece with Y := φ(M) (step 3) and (Φ_i, B_i, ΛL_i, m_i/Λ): for λ-a.e. b ∈ B_i, HasApproximateTangentSpaceAt n φ(M) (φ(F_i b)) (range(Dφ(F_i b)∘DF_i(b))), and range(Dφ(F_i b)∘DF_i(b)) = Dφ(F_i b)(range DF_i(b)) (LinearMap.range_comp, after ContinuousLinearMap.coe_comp).
5. Combination. By steps 2 and 4 there is a λ-null N_i ⊆ B_i such that for every b ∈ B_i ∖ N_i, x := F_i(b) satisfies HasApproximateTangentSpaceAt n M x Q(x) and, since Q(x) = range DF_i(b), HasApproximateTangentSpaceAt n φ(M) φ(x) (Dφ(x)(Q(x))).
6. Transfer to x. Every x ∈ M at which the conclusion fails lies in Z ∪ ⋃_i F_i(N_i) (an x ∈ P_i has the form F_i(b) with b ∈ B_i, and b ∈ N_i if the conclusion fails at x). H^n(Z) = 0 and H^n(F_i(N_i)) ≤ L_i^n H^n(N_i) = L_i^n λ(N_i) = 0. So the exceptional set is H^n-null, i.e. the conclusion holds for μHE[n]⌞M-a.e. x. (The argument is uniform in n ≥ 0; for n = 0 all planes are {0}.)

## Key steps

1. Decompose M into disjoint bi-Lipschitz pieces F_i(B_i) plus a null set (sibling bilipschitz_pieces).
2. The density lemma with Y = M gives T_{F_i b}M = range DF_i(b) for a.e. b, hence Q(F_i b) = range DF_i(b) by uniqueness.
3. φ(M) is Borel, contained in U and locally H^n-finite (φ bi-Lipschitz, φ^{-1}(U) = U).
4. The density lemma with Y = φ(M) and pieces φ∘F_i gives T_{φF_i b}φ(M) = Dφ(F_i b)(range DF_i(b)) for a.e. b.
5. Lipschitz images of λ-null parameter sets are H^n-null, so both statements hold H^n-a.e. on M.

## Reference use

### local-project

Queries:
- `python3 -I read of local-references/123e8435b4a2469b/manifest.json and local-references/123e8435b4a2469b/project/lake-manifest.json package revs; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -rn -E 'theorem (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|ae_tendsto_measure_inter_div|normDet_sq_eq_det_gram|normDet_comp|normDet_of_subsingleton|lintegral_iUnion|contDiff_symm|hasFDerivAt_convolution_right|contDiff_convolution_left|image_of_continuousOn_injOn)\b' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn -E 'theorem [A-Za-z.]*(image_of_continuousOn_injOn|contDiff_symm|hausdorffMeasure_image_le|euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_homothety_image|ae_tendsto_average_norm_sub|integral_eq_lintegral_pos_part_sub_lintegral_neg_part)\b' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn -E 'theorem (weighted_area_formula_lipschitz_injOn|HasApproximateTangentSpaceAt.unique|area_image_compl_regularSet_eq_zero|measurableSet_areaRegularSet|measurable_areaJacobianAt|exteriorDerivativeOn_pullbackFormWithin)\b|def (CountablyRectifiable|HasApproximateTangentSpaceAt|areaJacobianAt|areaRegularSet|blowUpMap)\b' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn -i -E '^(theorem|noncomputable def|def) .*pushforward' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06`
- `sed -n 60,140p GMT/Ch07/Submission.lean (IMRep fields, IMRep.action, IMRep.Represents, IsIntegerMultiplicity, BoundaryVanishes); grep -n 'def contract_scope' -A70 verifier/gmt-compare.py`
- `python3 -I scans of dag.json at 11:41:46Z and 11:55:52Z: status, candidate_commit, depends_on and frozen lean_statement of the 7 reused and 4 mirrored declarations and the subtree of root.minimizing_implies_stationary-a1.diffeo_pushforward-a1; lean_name hits for the 4 fresh names`
- `python3 -I diff of nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-v2.json subproblems against the 11 original parent-child-handoff.json files; equality check of /tmp/dpf-v3-check/final.json against decomposition-v2.json (all 11 children identical in every field)`
- `git show <candidate>:GMT/Ch07/Submission.lean for b44fe315b2 3de784c0d8 6b000c3693 74a1c6be70 a2ba78fca3 ee75447541 863f6d9cf6 36b2d37204: exact 'theorem Submission.<name> : <frozen type> :=' text found, one declaration each`
- `grep -rlE 'codim1_ldr_dpf_(approxTangent_ae_bilipschitz_piece|approxTangent_bilipschitz_image_ae|area_formula_bilipschitz_rectifiable|imrep_bilipschitz_image_rep)' over dag.json, nodes/*/decomposition-v*.json, GMT, .lake/packages/simongmt/Poincare, local-references/123e8435b4a2469b/project and local-references/123e8435b4a2469b/mathlib/Mathlib; /tmp/dpf-v3-scripts/refgrep.sh (git grep -l -E with the refs before the 'GMT/*.lean' pathspec) over all 4166 refs/heads and refs/remotes: 0 hits; positive control dpf_rectifiable_bilipschitz_pieces: 8 hits`
- `grep -n 'subproblem decomposition attempt|def _decompose|def _solve_children|def _existing_lean_name_problem|def _accepted_checkpoint|def _install_parent_supplied_child_handoff' /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py; sed -n 1,200p /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/decomposition_scope.py`
- `tail cluster-state/logs/gmt-ch07/30a94ba245764a7ba1e5ac06b265b8e7.log 2ee9f278722846438e9834336e81985e.log 9afc789922184ff18c490ae355f8dbcb.log; python3 -I issue-workers.json entries for issue 4957; python3 -I read of swarm-configs/9afc789922184ff18c490ae355f8dbcb.json (max_depth 6, max_children 12, max_nodes 5000)`
- `lake env lean -DautoImplicit=false /tmp/dpf-v3-check/Check.lean (exit 0); /tmp/dpf-v3-check/Cond.lean (exit 0; #print axioms: propext, Classical.choice, Quot.sound); /tmp/dpf-v3-check/Wiring.lean (exit 0; same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-scope-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-686bf23105/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-db3aef81cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-smooth-ap-e30aa8106d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-b3d596d026/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-4eba0cda06/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-jacobian-d0fc2e675e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-f9454fcfd5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-89b1ce4202/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9afc789922184ff18c490ae355f8dbcb.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/30a94ba245764a7ba1e5ac06b265b8e7.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/2ee9f278722846438e9834336e81985e.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/9afc789922184ff18c490ae355f8dbcb.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/decomposition_scope.py`
- `/tmp/dpf-v3-check/Check.lean`
- `/tmp/dpf-v3-check/Cond.lean`
- `/tmp/dpf-v3-check/Wiring.lean`
- `/tmp/dpf-v3-check/final.json`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt.
- The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library. Every Mathlib and SimonGMT lemma the child proofs cite exists at the pinned revisions:
- Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255); the Besicovitch, DensityTheorem and Differentiation density theorems; normDet_sq_eq_det_gram, normDet_comp, normDet_of_subsingleton and euclideanHausdorffMeasure_image; lintegral_iUnion; MeasurableSet.image_of_continuousOn_injOn; LipschitzWith.hausdorffMeasure_image_le; Homeomorph.contDiff_symm.
- SimonGMT: weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, HasApproximateTangentSpaceAt.unique, exteriorDerivativeOn_pullbackFormWithin.
- SimonGMT Chapter06 has only nVectorPushforward and the affine current push-forward, and no C¹ integer-multiplicity push-forward theorem, so the split is needed.
DAG (11:55:52Z, 1031 nodes).
- The 7 reused declarations are accepted with candidate commits. Each has a byte-identical frozen type, declared exactly once in its candidate, and matching depends_on.
- The 4 originals are still speculative-ready, so their mirrors get the fresh codim1_ldr_ names.
- The fresh names have 0 hits in the DAG, other proposals, sources, the snapshot and all 4166 refs (positive control: 8 hits).
Runtime. v1 and v2 were returned by _decompose (scope files written), but their workers stopped before activation. _install_parent_supplied_child_handoff returns early for accepted checkpoints.
Lean.
- All 11 child types, the dependency type and the parent type elaborate.
- The assembly proves the exact parent type from four child types plus the dependency, using only propext, Classical.choice and Quot.sound.
- All sibling applications used by the child proofs typecheck.
- The submitted children equal decomposition-v2.json in every field.
