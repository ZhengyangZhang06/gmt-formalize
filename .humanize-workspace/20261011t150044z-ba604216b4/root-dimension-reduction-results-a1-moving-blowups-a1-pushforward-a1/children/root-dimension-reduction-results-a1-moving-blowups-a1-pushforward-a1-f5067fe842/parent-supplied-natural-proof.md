# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.carrier_facts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (finite mass; Hⁿ(M ∖ K) = 0) and step 6 (support of a difference; supports in ℝ^P are closed) of the parent proof. Notation: Hⁿ = μHE[n]; in (1), M = R.carrier, θ = R.mult, μ_R = R.measure = θHⁿ⌞M, K := spt Y. All currents have the open domain U = ℝ^P.
1. By the sibling mass_and_support with U = ℝ^P (open) and T = Y: (i) M_W(Y) = μ_R(W) for every open W ⊆ ℝ^P, and (ii) spt Y = ℝ^P ∩ spt μ_R = spt μ_R.
2. Mass. The total mass of a current with domain ℝ^P is its local mass on the domain: M(Y) = M_{ℝ^P}(Y) (SimonGMT GeometricCurrentOn.mass = massOn of the domain). By 1(i) with W = ℝ^P, M(Y) = μ_R(ℝ^P).
3. Null complement of the support. ℝ^P is second countable, hence hereditarily Lindelöf, so the complement of the support of any measure ν on ℝ^P is ν-null: it is the union of the open ν-null sets, and countably many of them already cover it (Mathlib Measure.measure_compl_support). With 1(ii), μ_R(ℝ^P ∖ K) = 0.
4. K is closed (step 6 below), so ℝ^P ∖ K is Borel and μ_R(ℝ^P ∖ K) = ∫_{M∖K} θ dHⁿ (definition of the density measure μ_R on a Borel set). Since θ ≥ 1 on M (R.mult_pos, θ integer-valued), Hⁿ(M ∖ K) ≤ ∫_{M∖K} θ dHⁿ = 0. Hence Hⁿ(M ∖ spt Y) = 0.
5. Finiteness. If K is compact, then by step 3, μ_R(ℝ^P) = μ_R(K) + μ_R(ℝ^P ∖ K) = μ_R(K) = ∫_{M∩K} θ dHⁿ, which is finite by R.locallyIntegrable_mult applied to the compact set K ⊆ ℝ^P.
6. Closedness. For Y₁ ∈ 𝒟_n(ℝ^P), spt Y₁ = ℝ^P ∖ Z(Y₁), where the zero region Z(Y₁) is the union of the open sets W with compact closure on which Y₁ vanishes (SimonGMT GeometricCurrentOn.support and zeroRegion); a union of open sets is open, so spt Y₁ is closed.
7. Support of a difference. Let x ∉ spt Y₁ ∪ spt Y₂. As x ∈ ℝ^P, x ∈ Z(Y₁) ∩ Z(Y₂): there are open sets W₁, W₂ containing x, with compact closures (contained in ℝ^P), such that Y_i(ω) = 0 for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W_i (i = 1, 2). Then W := W₁ ∩ W₂ is open, contains x, and closure(W) ⊆ closure(W₁) is compact (a closed subset of a compact set). For every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W we have tsupport ω ⊆ W₁ and ⊆ W₂, so (Y₁ − Y₂)(ω) = Y₁(ω) − Y₂(ω) = 0 (the difference of currents is evaluated pointwise). Thus W is one of the sets forming Z(Y₁ − Y₂), x ∈ Z(Y₁ − Y₂) and x ∉ spt(Y₁ − Y₂). ∎

## Key steps

1. mass_and_support (U = ℝ^P) gives M_W(Y) = μ_R(W) for open W and spt Y = spt μ_R; with W = ℝ^P, M(Y) = μ_R(ℝ^P).
2. μ_R(ℝ^P ∖ spt μ_R) = 0 (second countability), and θ ≥ 1 on M gives Hⁿ(M ∖ spt Y) = 0.
3. For compact spt Y, μ_R(ℝ^P) = ∫_{M∩spt Y} θ dHⁿ < ∞ by local integrability of θ.
4. Supports are complements of open zero regions; a common relatively compact neighbourhood where Y₁ and Y₂ vanish lies in the zero region of Y₁ − Y₂.

## Reference use

### local-project

Queries:
- `cat RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/parent-child-handoff.json and parent-supplied-plan.md (frozen type, supplied proof, resolved dependencies)`
- `python3 scans of RUN/dag.json: lean_statement/status/candidate_commit of nodes whose types mention compContinuousLinearMap (fderiv, HasApproximateTangentSpaceAt or covectorEuclideanNorm; lean_name collision check for dimred_mbl_pf_* (no match)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_overlay_accepted_children' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `cmp RUN/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; rg -c sorry project/GMT/Ch07/Contract.lean`
- `rg -n 'lemma measure_compl_support :|theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem LipschitzWith.ae_differentiableAt|theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem norm_compContinuousLinearMap_le|theorem extDeriv_pullback|theorem map_linearDependent' RUN/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'pushforward|Pushforward' RUN/local-references/123e8435b4a2469b/project/GMT/Ch07/*.lean; rg -il pushforward lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -rn 'theorem area_image_criticalSet_eq_zero|theorem injective_area_formula_lipschitzOn|theorem weighted_area_formula_lipschitzOn_fiberSum|theorem weighted_area_formula_lipschitz_injOn|theorem exists_lipschitz_extension_finiteDimensional|theorem exteriorDerivativeOn_pullbackFormWithin' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `git log --all -S'dimred_mbl_pf_' --oneline (no match)`
- `lake env lean /tmp/pfdecomp/T1.lean (11 child types and the parent type as theorem Submission.X : T := by sorry after import GMT.Ch07.Submission)`
- `lake env lean /tmp/pfdecomp/T2.lean (conditional assembly from the 11 child types to the frozen parent type; #print axioms)`
- `python3 verifier lean_contract.validate_lean_statement on all 11 child types; topological sort of depends_on`
- `read RUN/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json and the parent-supplied-natural-proof.md of the three reused accepted nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-0354723769/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/tmp/pfdecomp/T1.lean`
- `/tmp/pfdecomp/T2.lean`

Pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308. Submission.lean is byte-identical to the frozen contract, whose only sorry is main_theorem. Neither the contract nor SimonGMT pushes currents forward by nonlinear maps: there is only the affine push-forward and the n-vector push-forward algebra. So the C¹ push-forward obligations are genuine. Every cited Mathlib and SimonGMT lemma exists in the pinned sources. Three accepted declarations are reused with byte-identical frozen types and candidate commits: dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub and dsmc_att_blowUp_points_of_approxTangent. The four push-forward lemmas of the projected_comparison node are still decomposing, so their exact types are mirrored under new dimred_mbl_pf_* names; these collide with nothing in dag.json or git history. All 11 child types and the parent type elaborate. A conditional assembly proves the exact frozen parent type from the child types, with axioms propext, Classical.choice and Quot.sound.
