# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.density_blowup_decay-a1`
- Child DAG node: `root.allard_tangent_cones-a1.density_blowup_decay-a1.lebesgue_density_open-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–4 and 7 of the parent proof (Simon Ch. 8, Remark 5.6(iii): approximate continuity of Θ^n(μ_V,·) used through Lebesgue density points; the localization is that of Simon Ch. 1, 3.23, "apply the above with μ⌞V_j"). The varifold facts μ_V(Uᶜ) = 0 and μ_V(K) < ∞ of the parent are here the hypotheses μ(Uᶜ) = 0 and μ(K) ≠ ∞. Notation: B_ρ(y) := closedBall y ρ (closed ball), B°_r(q) := ball q r (open ball), 1_A := A.indicator 1 with values in [0,∞]; quotients are taken in [0,∞] with Lean's conventions (a/0 = ∞ for a ≠ 0, 0/0 = 0); for a measure ν and a set K, ν⌞K := ν.restrict K.

1. Countable family of compact balls. ℝ^N is separable, so it has a countable dense subset D (TopologicalSpace.exists_countable_dense). Let I := {(q, r) ∈ D × ℚ : 0 < r and B_r(q) ⊆ U}. I is countable, being a subset of the countable set D × ℚ. For i = (q, r) ∈ I put K_i := B_r(q). K_i is closed and bounded in the finite-dimensional space ℝ^N, hence compact (isCompact_closedBall), and K_i ⊆ U, so μ(K_i) ≠ ∞ by hypothesis. Hence μ_i := μ⌞K_i has total mass μ_i(ℝ^N) = μ(K_i) < ∞: it is a finite measure, hence a locally finite measure.

2. Every point of U is interior to some K_i. Let x ∈ U. Since U is open there is ε > 0 with B°_ε(x) ⊆ U. Choose a rational r with 0 < r < ε/2, and, since D is dense, a point q ∈ D with dist(x, q) < r. Then (q, r) ∈ I: if dist(y, q) ≤ r then dist(y, x) ≤ dist(y, q) + dist(q, x) < 2r < ε, so B_r(q) ⊆ B°_ε(x) ⊆ U. Moreover dist(x, q) < r.

3. Lebesgue–Besicovitch differentiation for each μ_i. ℝ^N = EuclideanSpace ℝ (Fin N) is a finite-dimensional real normed space, so it has the Besicovitch covering property (Mathlib's HasBesicovitchCovering instance), it is a second-countable metric space, and its σ-algebra is the Borel σ-algebra. Apply Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet to the locally finite measure μ_i and the measurable set A. It gives a set Z_i with μ_i(Z_i) = 0 such that for every y ∉ Z_i,
   μ_i(A ∩ B_ρ(y)) / μ_i(B_ρ(y)) → 1_A(y) as ρ ↓ 0.
   Since K_i is closed, hence measurable, Measure.restrict_apply' gives μ(Z_i ∩ K_i) = μ_i(Z_i) = 0.

4. The exceptional set. Let Z' := Uᶜ ∪ ⋃_{i ∈ I} (Z_i ∩ K_i). By countable subadditivity, μ(Z') ≤ μ(Uᶜ) + Σ_{i ∈ I} μ(Z_i ∩ K_i) = 0 + 0 = 0.

5. Good points. Let x ∉ Z'. Then x ∈ U, so by step 2 there is i = (q, r) ∈ I with dist(x, q) < r; in particular x ∈ K_i. Since x ∉ Z_i ∩ K_i and x ∈ K_i, we get x ∉ Z_i, so by step 3
   μ_i(A ∩ B_ρ(x)) / μ_i(B_ρ(x)) → 1_A(x) as ρ ↓ 0.

6. Removing the restriction. Let δ := r − dist(x, q) > 0 and 0 < ρ < δ. If dist(y, x) ≤ ρ then dist(y, q) ≤ ρ + dist(x, q) < r, so B_ρ(x) ⊆ B°_r(q) ⊆ K_i. By Measure.restrict_apply' (K_i measurable):
   μ_i(A ∩ B_ρ(x)) = μ(A ∩ B_ρ(x) ∩ K_i) = μ(A ∩ B_ρ(x)) and μ_i(B_ρ(x)) = μ(B_ρ(x) ∩ K_i) = μ(B_ρ(x)).
   So the functions ρ ↦ μ_i(A ∩ B_ρ(x))/μ_i(B_ρ(x)) and ρ ↦ μ(A ∩ B_ρ(x))/μ(B_ρ(x)) agree on the interval (0, δ). That interval belongs to the filter 𝓝[>] 0, so (Tendsto.congr') the second function also tends to 1_A(x) as ρ ↓ 0.

7. Conclusion. Step 6 holds for every x outside the μ-null set Z' (step 4). This is exactly the claim: for μ-a.e. x, μ(A ∩ B_ρ(x))/μ(B_ρ(x)) → 1_A(x) as ρ ↓ 0. ∎

Formalization remark. This is an alternative, equally complete proof of the same statement, compiled sorry-free against the pinned snapshot in about 40 Lean lines. It runs steps 1–6 on the open subspace U itself instead of on countably many balls.
(a) U with the induced metric has the Besicovitch covering property, because a satellite configuration in U is also one in ℝ^N. This is SimonGMT's Poincare.SimonGMT.Chapter08.hasBesicovitchCovering_subtype, available after import GMT.Ch08.Submission. U is second countable, its subtype σ-algebra is Borel, and it is locally compact (IsOpen.locallyCompactSpace).
(b) μ_U := μ.comap Subtype.val is locally finite on U. Each z ∈ U has a compact neighbourhood C in U (exists_compact_mem_nhds), and μ_U(C) = μ(val '' C) < ∞ by MeasurableEmbedding.comap_apply, because val '' C is compact and contained in U.
(c) μ_U.map val = μ⌞U = μ, by map_comap_subtype_coe, μ(Uᶜ) = 0 and Measure.restrict_eq_self_of_ae_mem.
(d) For z ∈ U and measurable B, μ(B ∩ B_r(z)) = μ_U(val⁻¹B ∩ B^U_r(z)). This follows from (c) and Measure.map_apply, since the closed ball of U is, by definition, the preimage of the ambient closed ball. Also 1_{val⁻¹A}(z) = 1_A(z).
(e) Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet for μ_U and val⁻¹A, rewritten by (d), gives the convergence for μ_U-a.e. z ∈ U. MeasurableEmbedding.ae_map_iff (state the predicate explicitly, since higher-order unification fails otherwise) and (c) transfer it to μ-a.e. x.

## Key steps

1. Countable family K_i = B_r(q), with q in a countable dense set D, r ∈ ℚ_{>0} and B_r(q) ⊆ U: each μ⌞K_i is finite, hence locally finite, and every x ∈ U lies in the open ball B°_r(q) of some K_i.
2. Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet for μ⌞K_i and A gives a μ⌞K_i-null set Z_i off which the ratio tends to 1_A; μ(Z_i ∩ K_i) = μ⌞K_i(Z_i) = 0.
3. Z' := Uᶜ ∪ ⋃_i (Z_i ∩ K_i) is μ-null by countable subadditivity.
4. For x ∉ Z' pick K_i with dist(x,q) < r. For 0 < ρ < r − dist(x,q), B_ρ(x) ⊆ K_i, so the μ⌞K_i-ratio and the μ-ratio coincide and the limit 1_A(x) transfers (Tendsto.congr').

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_measure_inter_div_of_measurableSet|theorem ae_tendsto_measure_inter_div|theorem tendsto_filterAt' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -n 'instHasBesicovitchCovering' mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `grep -n "theorem restrict_apply'|theorem restrict_eq_self_of_ae_mem|theorem map_comap_subtype_coe" mathlib/Mathlib/MeasureTheory/Measure/`
- `grep -rn 'indicator_of_notMem|mulIndicator_of_notMem' Mathlib/Algebra/Notation/Indicator.lean`
- `grep -rn 'ae_tendsto_measure_inter_div|ae_tendsto_rnDeriv|Besicovitch\.|vitaliFamily' .lake/packages/simongmt/Poincare --include=*.lean`
- `grep -n 'structure Varifold|def weight|theorem weight_apply|theorem weight_finite_on_compact|domainWeight|map_domainWeight|instSigmaFinite' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `import chain check: grep '^public import' Chapter08/VarifoldConvergence.lean, FirstVariationRiesz.lean, FirstVariationDecomposition.lean (reaches FirstVariationDensity)`
- `sed -n 540,640p book/chapter-08.txt (Simon 5.5–5.7, proof of 5.5 (3)–(4)); sed -n 1040,1140p book/sources/chapter-01-source.txt (Simon Ch. 1, 3.23–3.24)`
- `python3 -I: gmt-compare.contract_scope(Contract.lean, 'GMT.Ch08.main_theorem'), gmt-compare.child_modules(...,'contract'), lean_contract.validate_lean_statement on both child statements`
- `lake env lean /tmp/dbd-decomp/scratch/{Stmts,ChildA,ChildB,Final,Stub2,Final2}.lean and /tmp/dbd-decomp/challenge/{allard_tc_dbd_lebesgue_density,allard_tc_dbd_relative_decay}_Challenge.lean`
- `python3 -I scan of dag.json lean_name (90 nodes, 90 distinct, proposed names absent); grep -rIl 'allard_tc_dbd_' over dag.json, nodes/ and GMT/ (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Notation/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-density-blowup-decay-a1/parent-child-handoff.json`
- `/tmp/dbd-decomp/scratch/Stub2.lean`
- `/tmp/dbd-decomp/scratch/Final2.lean`
- `/tmp/dbd-decomp/scratch/ChildA.lean`
- `/tmp/dbd-decomp/scratch/ChildB.lean`
- `/tmp/dbd-decomp/challenge/allard_tc_dbd_lebesgue_density_Challenge.lean`
- `/tmp/dbd-decomp/challenge/allard_tc_dbd_relative_decay_Challenge.lean`

Snapshot: project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission (sha256 2e5cd5b3…).

Mathlib:
- Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet (Covering/Besicovitch.lean:1089) needs IsLocallyFiniteMeasure on the whole space. μ_V can fail this at ∂U, which is why child A localizes.
- instHasBesicovitchCovering (BesicovitchVectorSpace.lean:499) covers Euclidean N.
- Measure.restrict_apply' (Restrict.lean:111), restrict_eq_self_of_ae_mem (:347) and map_comap_subtype_coe (:934) give the restriction and transfer steps.
- Set.indicator_of_notMem is the additive form of mulIndicator_of_notMem (Algebra/Notation/Indicator.lean).

SimonGMT (pinned 2b366308) is imported transitively by GMT.Ch08.Submission via VarifoldConvergence → FirstVariationRiesz → FirstVariationDecomposition → FirstVariationDensity.
- It supplies hasBesicovitchCovering_subtype and the varifold facts isOpen_domain, supported, weight_apply and weight_finite_on_compact.
- Its ae_tendsto_firstVariationDensity_of_domainMeasure is only the RN-derivative analogue for V.weight, not child A's density-point statement, so child A is new.
- No local declaration proves child B.

Both child statements validate and elaborate in the comparator scope, and the parent compiles from them. With full child proofs, every declaration uses only propext, Classical.choice and Quot.sound. The proposed names occur nowhere in the DAG, run nodes or GMT/.
