# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_monotone-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the selected node's supplied proof (parent 2(a), 2(b)) with Λ := rΛ_K as in its (0c); Simon 7.3.3, proof of (1), uses the monotonicity 4.7 of Ch. 4 for the members of 𝒯 (chapter-07.txt lines 474–483). Positive-scale members are written (a, t) = (z + rx, rλ). Siblings used: zero_limit_minimizing (Submission.dimred_tr_bc_zero_limit_minimizing, with (MB)) and ambient_calculus (Submission.idtp_fons_cc_ambient_calculus) parts (1), (2), (3).
Notation: μ_T := RT.measure, W := B_{2r}(z), K := B̄_{2r}(z), E := ℝ^{n+k}.
1. (Choice of Λ.) K is compact (isCompact_closedBall) and K ⊆ U. Apply (MON) to T with d := n + ℓ (1 ≤ n ≤ n + ℓ ≤ n + k; the other hypotheses are those of T) and part (i) to K: there is Λ_K ≥ 0 such that, whenever B̄_{R′}(c′) ⊆ K, the map τ ↦ ofReal(e^{Λ_Kτ}/τⁿ)·M_{B_τ(c′)}(T) is monotone on (0, R′). Put Λ := rΛ_K ≥ 0.
2. (Products.) If g : ℝ → [0, ∞] is monotone on (0, R) and κ ≥ 0, then ρ ↦ ofReal(e^{κρ})·g(ρ) is monotone on (0, R): both factors are nonnegative and monotone there (mul_le_mul'). For real κ₁, κ₂ and ρ > 0, ofReal(e^{(κ₁+κ₂)ρ}/ρⁿ) = ofReal(e^{κ₁ρ})·ofReal(e^{κ₂ρ}/ρⁿ) (Real.exp_add, ENNReal.ofReal_mul).
3. Let μ ∈ 𝓜, y ∈ E and R ∈ ℝ with B̄_R(y) ⊆ B̄_2(0). If R ≤ 0, then (0, R) = ∅ and there is nothing to prove; assume R > 0. Then ‖y‖ + R ≤ 2: since n + k ≥ 1, there is a unit vector u with y = ‖y‖u (u := ‖y‖⁻¹y if y ≠ 0, any unit vector otherwise); the point y + Ru lies in B̄_R(y) ⊆ B̄_2(0) and has norm ‖y‖ + R.
4. (Case PS.) μ = ofReal(t⁻¹ⁿ) • (μ_T⌞W).map(dilation a t) with 0 < t ≤ r and dist(a, z) ≤ r − t. Put c′ := a + t•y.
 (a) dist(c′, z) + tR ≤ dist(a, z) + t‖y‖ + tR ≤ (r − t) + t(‖y‖ + R) ≤ r − t + 2t = r + t ≤ 2r. Hence B̄_{tR}(c′) ⊆ K, and for 0 < ρ < R, B_{tρ}(c′) ⊆ W ⊆ U (if dist(v, c′) < tρ then dist(v, z) < tR + dist(c′, z) ≤ 2r).
 (b) For 0 < ρ < R: μ(B_ρ(y)) = ofReal(t⁻¹ⁿ)·(μ_T⌞W)((dilation a t)⁻¹(B_ρ(y))) (ambient_calculus (2)) = ofReal(t⁻¹ⁿ)·(μ_T⌞W)(B_{tρ}(c′)) (ambient_calculus (3)) = ofReal(t⁻¹ⁿ)·μ_T(B_{tρ}(c′)) (Measure.restrict_apply and B_{tρ}(c′) ⊆ W) = ofReal(t⁻¹ⁿ)·M_{B_{tρ}(c′)}(T) ((IM)(a) for T: U open, RT represents T, B_{tρ}(c′) open and ⊆ U).
 (c) Hence, for 0 < ρ < R, G(ρ) := ofReal(e^{tΛ_Kρ}/ρⁿ)·μ(B_ρ(y)) = ofReal(e^{Λ_K(tρ)}/(tρ)ⁿ)·M_{B_{tρ}(c′)}(T), since ofReal(e^{tΛ_Kρ}/ρⁿ)·ofReal(t⁻¹ⁿ) = ofReal(e^{Λ_K(tρ)}/(tρ)ⁿ) (ENNReal.ofReal_mul, (tρ)ⁿ = tⁿρⁿ). By step 1 with (c′, R′ := tR) and (a), the right side is a monotone function of τ = tρ on (0, tR); as ρ ↦ tρ is increasing and maps (0, R) into (0, tR), G is monotone on (0, R).
 (d) By step 2 with κ₁ := (r − t)Λ_K ≥ 0 and κ₂ := tΛ_K, ofReal(e^{Λρ}/ρⁿ)·μ(B_ρ(y)) = ofReal(e^{(r−t)Λ_Kρ})·G(ρ), which is monotone on (0, R).
5. (Case ZS.) μ = RS.measure for an IMRep RS of S in E with zero-scale data (c_i, t_i, b). Then dist(b, z) ≤ r (limit of dist(c_i, z) < r), so b ∈ U, and zero_limit_minimizing (with (MB), the hypotheses of T and x := b) shows that S is minimizing in E with ∂S = 0. Apply (MON) to S with P := n + k, d := n + k and U = N = univ: IsEmbeddedSubmanifold 2 (n + k) univ by ambient_calculus (1), (closure univ ∖ univ) ∩ univ = ∅, S is minimizing in univ ∩ univ = univ, spt S ⊆ univ ∩ univ, and ∂S = 0. Part (ii) (N = univ, B_R(y) ⊆ univ) shows that ρ ↦ ofReal(1/ρⁿ)·M_{B_ρ(y)}(S) is monotone on (0, R). By (IM)(a) for S (univ open, RS represents S), M_{B_ρ(y)}(S) = RS.measure(B_ρ(y)) = μ(B_ρ(y)). Since ofReal(e^{Λρ}/ρⁿ)·μ(B_ρ(y)) = ofReal(e^{Λρ})·(ofReal(1/ρⁿ)·μ(B_ρ(y))) and Λ ≥ 0, step 2 gives monotonicity on (0, R).
6. Steps 4 and 5 prove the claim with the single constant Λ = rΛ_K of step 1. ∎

## Key steps

1. (MON)(i) for T on the compact K = B̄_{2r}(z) gives Λ_K ≥ 0; take Λ := rΛ_K.
2. Positive scale (a, t): μ(B_ρ(y)) = t^{−n}M_{B_{tρ}(a+ty)}(T) with B̄_{tR}(a + ty) ⊆ K (since ‖y‖ + R ≤ 2), so e^{tΛ_Kρ}ρ^{−n}μ(B_ρ(y)) is the (MON)(i) quantity at τ = tρ; the extra factor e^{(r−t)Λ_Kρ} is nondecreasing.
3. Zero scale: S is minimizing with ∂S = 0 (zero_limit_minimizing), so (MON)(ii) on ℝ^{n+k} and (IM)(a) give monotonicity of ρ^{−n}μ(B_ρ(y)); multiply by e^{Λρ}.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Submission.lean`
- `rg -n dimred_tr_bc <snapshot>/project (exit 1, no match); grep -rn dimred_tr_bc GMT .lake/packages/simongmt/Poincare (no match)`
- `rg -n 'def VanishesOn|def zeroRegion|def support|def blowUp|def currentEval|def ConvergesWeakly|def MassMeasuresConverge|structure IMRep|def IMRep.measure' <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem tendsto_nhds_unique |theorem integral_smul_measure|theorem integral_map |theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem withDensity_congr_ae|theorem withDensity_indicator |theorem tendsto_add_atTop_nat|theorem integral_zero_measure|theorem integral_eq_zero_of_ae|theorem StrictMono.id_le' <snapshot>/mathlib/Mathlib`
- `rg -n -e '(theorem|lemma) [A-Za-z_.]*(StrictMono.tendsto_atTop|Tendsto.limsup_eq|closedBall_subset_closedBall_iff|Homeomorph.isProperMap|withDensity_apply |restrict_restrict )' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem tsupport_affinePullbackForm_subset|theorem affinePullbackForm_isTestForm' .lake/packages/simongmt/Poincare/SimonGMT; sed -n on SimonGMT Chapter06 Currents.lean, CurrentLocalEquality.lean, Mass.lean, AffineCurrentPushforward.lean`
- `python3 inspection of dag.json: selected node, its four registered dependencies, all ancestors' dependencies (lean names and status), and accepted lean_statements matching 'IsEmbeddedSubmanifold … univ', '∀ᵐ x ∂μHE[n], Tendsto', 'Set (Measure', 'ConvergesWeakly' uniqueness`
- `python3 reading of the accepted precedent cone_class decomposition-v1.json and of the parent-child-handoff.json of ambient_calculus, density_representation and borel_restriction`
- `python3 /tmp/bc-a1/scripts/check_reuse.py (git show <candidate>:GMT/Ch07/Submission.lean; declared type vs dag.json; sorry count) for aebb2ae, 1f0fe9f, 90d679a, cb3c7f3; git show 90d679a:GMT/Ch07/Submission.lean | grep '^theorem Submission'`
- `lake env lean /tmp/bc-a1/lean/Types.lean; lake env lean /tmp/bc-a1/lean/Assembly.lean; lake env lean /tmp/bc-a1/lean/Skeleton.lean; lake env lean /tmp/bc-a1/lean/Skeleton2.lean`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,inherited,store}.py?ref=feature/humanize-api-update-claude; grep -n '_inherited_prerequisites|_overlay_accepted_children|_render_parent_supplied_natural|_dependency_problem'`
- `grep -n on book/chapter-07.txt (class 𝒯 in the proof of 7.3.3, lines 443–486) and book/chapter-A.txt (A.4, line 35)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-class-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-class-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4e8b16732b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-699466b76b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/tmp/bc-a1/lean/Types.lean`
- `/tmp/bc-a1/lean/Assembly.lean`
- `/tmp/bc-a1/lean/Skeleton.lean`
- `/tmp/bc-a1/lean/Skeleton2.lean`
- `/tmp/bc-a1/scripts/check_reuse.py`
- `/tmp/bc-a1/scripts/build.py`
- `/tmp/bc-a1/mlf/inherited.py`
- `/tmp/bc-a1/mlf/runtime.py`

Pins and contract:
- The snapshot manifest pins project b4d606d and Mathlib 25730c7c. These equal the workspace HEAD and .lake/packages/mathlib.
- The snapshot Contract.lean, snapshot Submission.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- No dimred_tr_bc_* identifier exists in the snapshot (rg exit 1), in GMT, in SimonGMT or in dag.json.

Library facts cited by the children exist at these paths:
- tendsto_nhds_unique (Topology/Separation/Hausdorff.lean:180)
- StrictMono.tendsto_atTop (Order/Filter/AtTopBot/Tendsto.lean:84)
- integral_smul_measure and integral_map (MeasureTheory/Integral/Bochner/Basic.lean:1052, 1081)
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- withDensity_apply, withDensity_congr_ae and withDensity_indicator (Measure/WithDensity.lean:44, 88, 192)
- Filter.Tendsto.limsup_eq (Topology/Order/LiminfLimsup.lean:190)
- tendsto_add_atTop_nat (AtTopBot/Basic.lean:331)
- Homeomorph.isProperMap (Topology/Maps/Proper/Basic.lean:264)
- StrictMono.id_le (Order/WellFounded.lean:267)
- integral_eq_zero_of_ae and integral_zero_measure (Bochner/Basic.lean:349, 1020)
closedBall_subset_closedBall_iff has no match; the children use a unit-vector argument instead.

SimonGMT facts:
- affinePullbackForm, tsupport_affinePullbackForm_subset and affinePullbackForm_isTestForm are at AffineCurrentPushforward.lean:35–64.
- countablyRectifiable_of_measure_zero is at Rectifiable.lean:45.
- support = U ∖ zeroRegion, with VanishesOn, is at CurrentLocalEquality.lean:101–118.

Reuse:
- ambient_calculus (aebb2ae), density_representation (1f0fe9f) and dor_lmb_imrep_restrict_current (90d679a) are accepted, and their isolated comparators passed.
- Their candidates' declared types equal the DAG types, and each candidate's only sorry is main_theorem.
- The precedent cone_class decomposition reused the same three in the same way.

Lean checks:
- All 8 new child types elaborate.
- The assembly of the selected frozen type compiles from the 5 class children and the 4 registered dependencies, with only standard axioms otherwise.
- class_rescale is fully proved from its siblings.
- The key steps of class_tangent, class_monotone and class_finite_density compile.

Framework (math-lean-flow inherited.py) and its effect on the split:
- A child inherits every ancestor dependency whose Lean name appears in its proof text, and waits for it to be accepted.
- So new children take unaccepted results as hypotheses, and a script checks that their proofs avoid all twelve ancestor-dependency names.
