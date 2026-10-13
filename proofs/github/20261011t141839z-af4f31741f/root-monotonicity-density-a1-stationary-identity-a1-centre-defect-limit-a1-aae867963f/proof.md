# Parent-supplied natural-language proof

- Parent DAG node: `root.monotonicity_density-a1.stationary_identity-a1`
- Child DAG node: `root.monotonicity_density-a1.stationary_identity-a1.centre_defect_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 (3.1–3.3) of the parent node's supplied proof of Simon, Introduction to Geometric Measure Theory, Ch. 8, 3.4 (printed p. 211). That step uses continuity from below of the defect measure and the vanishing of the integrand at the centre; it is made self-contained here. The passage from a sequence of inner radii to the one-sided limit σ → 0+ is added via monotonicity. This is pure measure theory: no stationarity, first-variation or finiteness hypothesis is used, and the statement holds for every real ρ.

Implementation note: this node is a leaf. Its implementation must be the single declaration Submission.normalDefect_annulus_tendsto_closedBall, using only the frozen contract's imports. A scratch proof of exactly this shape compiled and passed the leaf-delta check. The withDensity route below needs no measurability of the integrand.

Notation. Fix N, n, U, V, x and ρ ∈ ℝ.
- G := Grassmannian N n; p_S := Grassmannian.project S; B_s := closedBall x s for s ∈ ℝ.
- For z = (y,S) ∈ ℝ^N × G, f(z) := ofReal(|(y − x) − p_S(y − x)|²/|y − x|^{n+2}) ∈ [0,∞). By definition, normalDefect V x A = ∫⁻_{A×G} f dV (the lintegral of f over A ×ˢ univ with respect to V.measure) for every set A ⊆ ℝ^N.
- D(σ) := normalDefect V x (B_ρ ∖ B_σ) for σ ∈ ℝ, and T := normalDefect V x (B_ρ).
- The sets B_s, B_ρ ∖ B_s and B_ρ ∖ {x}, and their products with G, are measurable, since closed balls and singletons are closed and hence Borel.

1. The integrand vanishes at the centre. If y = x then |y − x|^{n+2} = 0^{n+2} = 0 because n + 2 ≥ 1. So the real quotient is (…)/0 = 0 by the convention a/0 = 0, and f(x,S) = ofReal(0) = 0 for every S ∈ G.

2. Removing the centre does not change the defect. Pointwise on ℝ^N × G, 1_{(B_ρ∖{x})×G}·f = 1_{B_ρ×G}·f.
   - If z = (y,S) with y ≠ x, then z ∈ (B_ρ∖{x})×G ⇔ y ∈ B_ρ ⇔ z ∈ B_ρ×G, so both sides agree.
   - If y = x, the left side is 0 because z ∉ (B_ρ∖{x})×G, and the right side is 0 or f(x,S) = 0 by 1.
   Both sets are measurable, so the lintegral of an indicator equals the set lintegral (lintegral_indicator). Hence normalDefect V x (B_ρ ∖ {x}) = ∫⁻ 1_{(B_ρ∖{x})×G} f dV = ∫⁻ 1_{B_ρ×G} f dV = T.

3. Monotonicity in σ. If σ ≤ σ' then B_σ ⊆ B_{σ'}, so (B_ρ ∖ B_{σ'}) × G ⊆ (B_ρ ∖ B_σ) × G. The set lintegral is monotone in the set (lintegral_mono_set), so D(σ') ≤ D(σ): D is antitone on ℝ. Likewise (B_ρ ∖ B_σ) × G ⊆ B_ρ × G gives D(σ) ≤ T for every σ.

4. An increasing sequence of annuli. For k ∈ ℕ let σ_k := 1/(k+1) > 0 and s_k := (B_ρ ∖ B_{σ_k}) × G.
   - If k ≤ l then σ_l ≤ σ_k, so B_{σ_l} ⊆ B_{σ_k} and s_k ⊆ s_l. Thus (s_k) is increasing.
   - Its union is (B_ρ ∖ {x}) × G. If z = (y,S) ∈ s_k then y ∈ B_ρ and dist(y,x) > σ_k > 0, so y ≠ x. Conversely, if y ∈ B_ρ and y ≠ x, then dist(y,x) > 0, and by the Archimedean property there is k with 1/(k+1) < dist(y,x) (exists_nat_one_div_lt); then y ∉ B_{σ_k} and z ∈ s_k.

5. Continuity from below. Let ν := V.measure.withDensity f. This is a measure on ℝ^N × G with ν(E) = ∫⁻_E f dV for every measurable E (withDensity_apply, which needs no measurability of f).
   - ν(s_k) = D(σ_k) for every k.
   - By 4 and 2, ν(⋃_k s_k) = ν((B_ρ ∖ {x}) × G) = normalDefect V x (B_ρ ∖ {x}) = T.
   Measures are continuous along increasing sequences of sets (tendsto_measure_iUnion_atTop), so D(σ_k) = ν(s_k) → ν(⋃_k s_k) = T as k → ∞.

6. From the sequence to σ → 0+. D is antitone on ℝ (step 3) with values in the complete linear order [0,∞], so it has a right limit at 0 equal to L := sup{D(σ) : σ > 0}; that is, D(σ) → L as σ → 0 with σ > 0 (Antitone.tendsto_nhdsGT).
   - By 3, L ≤ T.
   - Each σ_k > 0, so D(σ_k) ≤ L for all k. Letting k → ∞ in 5 gives T ≤ L (le_of_tendsto').
   Hence L = T, that is, normalDefect V x (closedBall x ρ ∖ closedBall x σ) → normalDefect V x (closedBall x ρ) as σ → 0+, along the filter 𝓝[>] 0. As N, n, U, V, x and ρ were arbitrary, the statement holds.

## Key steps

1. The normalDefect integrand f vanishes on {x} × G(N,n), since the denominator is 0^{n+2} = 0 and a/0 = 0. So 1_{(B_ρ∖{x})×G}·f = 1_{B_ρ×G}·f, and normalDefect V x (B_ρ ∖ {x}) = normalDefect V x (B_ρ) by lintegral_indicator.
2. D(σ) := normalDefect V x (B_ρ ∖ B_σ) is antitone in σ, and D(σ) ≤ normalDefect V x (B_ρ), by monotonicity of set lintegrals.
3. With σ_k = 1/(k+1), the measurable sets (B_ρ ∖ B_{σ_k}) × G increase to (B_ρ ∖ {x}) × G. Continuity from below of ν = V.measure.withDensity f, where ν(E) = ∫⁻_E f dV for measurable E, gives D(σ_k) → normalDefect V x (B_ρ).
4. Antitone right limit: D(σ) → sup_{σ>0} D(σ) as σ → 0+ (Antitone.tendsto_nhdsGT). This sup equals normalDefect V x (B_ρ) by the upper bound and the sequence limit.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum <snapshot>/project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); git -C .lake/packages/simongmt rev-parse HEAD (2b3663083f3fe399b6296fb8eaee52169170e197, clean)`
- `grep -n 'tendsto_nhdsWithin_Ioo_right|Antitone.tendsto_nhdsGT' <snapshot>/mathlib/Mathlib/Topology/Order/Monotone.lean (457, 536); grep 'protected theorem Tendsto.const_mul' Topology/Instances/ENNReal/Lemmas.lean (354); grep 'Ioc_mem_nhdsGT' (MeasureTheory/Covering/Besicovitch.lean usage)`
- `grep -n 'inv_ne_top|protected theorem mul_inv|div_eq_inv_mul' <snapshot>/mathlib/Mathlib/Basic/ENNReal/Inv.lean (205, 245, 48); grep 'theorem ofReal_pow' Basic/ENNReal/Real.lean (306); grep 'theorem measure_ball_pos' MeasureTheory/Measure/OpenPos.lean (212)`
- `grep -n 'theorem lintegral_mono_set|theorem lintegral_indicator' MeasureTheory/Integral/Lebesgue/Basic.lean (98, 510); grep 'lintegral_tendsto_of_tendsto_of_monotone' Integral/Lebesgue/Add.lean (115); grep 'theorem withDensity_apply' Measure/WithDensity.lean (44); grep 'theorem tendsto_measure_iUnion_atTop' Measure/Continuity.lean (198)`
- `grep -n '^theorem|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/{StationaryMonotonicity,StationaryCutoff}.lean; grep normalProject_eq_sub|norm_normalProject_radial_sq|radialNormalSq Chapter08/RadialFirstVariation.lean; grep monotonicityCutoff|scaledRadialCutoffDeriv_support Chapter04/FirstVariation.lean`
- `python import-closure walk of Poincare.SimonGMT.Chapter08.VarifoldConvergence + Chapter03.Rectifiable + Chapter02.Submanifold vs Poincare.SimonGMT.Chapter08.StationaryMonotonicity (7 extra modules: Chapter04.Basic, Chapter04.FirstVariation, RadialCutoffDifferentiation, RadialFirstVariation, StationaryCutoff, StationaryMonotonicity, WeightedRadialIdentity)`
- `grep -rn 'def densityRatio|def unitBallVolume|def HasDensity|def normalDefect' .lake/packages/simongmt/Poincare (no clash with contract names)`
- `grep -c 'annular_identity_limit_at_zero|normalDefect_annulus_tendsto_closedBall' .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json (0); git log --all -S annular_identity_limit_at_zero (none)`
- `read /runtime/flows/gmt-claude-ceab09671123/_recursive_lean/leaf_verification.py (check_source_delta forbids import/extra declarations in leaves) and parent_verification.py (check_parent_git_delta); verifier/gmt-compare.py candidate_inputs and challenge generation (line ~597); verifier/lean_contract.validate_lean_statement on both child types (OK)`
- `lean (LEAN_PATH=private Submission olean + lake packages) /tmp/stat_id_split/final/FinalTypes.lean, LeafB.lean -> SolutionB.lean, LeafC.lean -> SolutionC.lean, ParentCandidate.lean -> SolutionParent.lean; earlier /tmp/stat_id_split/src/{Types,Assembly,ChildA,ChildB}.lean; reviewer /tmp/stat_id_review/src/{RestructC,RestructParent}.lean`
- `grep -n '3.4' book/chapter-08.txt (printed 3.3-3.4 text, p. 210-211)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-stationary-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryMonotonicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryCutoff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialCutoffDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-ceab09671123/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-ceab09671123/_recursive_lean/parent_verification.py`
- `/tmp/stat_id_split/final/FinalTypes.lean`
- `/tmp/stat_id_split/final/LeafB.lean`
- `/tmp/stat_id_split/final/SolutionB.lean`
- `/tmp/stat_id_split/final/LeafC.lean`
- `/tmp/stat_id_split/final/SolutionC.lean`
- `/tmp/stat_id_split/final/ParentCandidate.lean`
- `/tmp/stat_id_split/final/SolutionParent.lean`
- `/tmp/stat_id_split/src/Assembly.lean`
- `/tmp/stat_id_split/src/ChildA.lean`
- `/tmp/stat_id_review/src/RestructC.lean`
- `/tmp/stat_id_review/src/RestructParent.lean`

Snapshot and pinning: the snapshot is project 63436ae6 plus Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission (sha256 2e5cd5b3…). SimonGMT is pinned at 2b366308 with a clean worktree.

Mathlib supplies every lemma the two leaves need:
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457) and Antitone.tendsto_nhdsGT (:536);
- ENNReal.Tendsto.const_mul (Topology/Instances/ENNReal/Lemmas.lean:354);
- lintegral_mono_set and lintegral_indicator (Integral/Lebesgue/Basic.lean:98 and :510);
- withDensity_apply (Measure/WithDensity.lean:44) and tendsto_measure_iUnion_atTop (Measure/Continuity.lean:198);
- ENNReal.inv_ne_top, mul_inv and div_eq_inv_mul (Basic/ENNReal/Inv.lean:205, 245, 48), ofReal_pow (Basic/ENNReal/Real.lean:306), and measure_ball_pos (Measure/OpenPos.lean:212).
Mathlib has no varifold material.

The annular identity is SimonGMT's Varifold.StationaryOn.stationaryMonotonicity (StationaryMonotonicity.lean:131). It relies on normalizedBallMass (:111), annularMonotonicityDefect (:120), StationaryOn (StationaryCutoff.lean:28), and normalProject_eq_sub and norm_normalProject_radial_sq (RadialFirstVariation.lean:81, :123). All of these sit in seven modules outside the contract's import closure. The active leaf gate (check_source_delta) forbids `import` in leaf deltas, while check_parent_git_delta lets a non-leaf edit Submission.lean. So the identity stays in this node and both children are import-free. There are no name clashes.

Kernel checks import GMT.Ch08.Submission in the contract scope and use only the axioms propext, Classical.choice and Quot.sound:
- Both child types elaborate and pass validate_lean_statement.
- Both names are unused, both for #check_failure and in dag.json.
- Each leaf candidate (contract plus one theorem) passes check_source_delta, compiles, and `exact Submission.<name>` closes its frozen type.
- A full parent candidate (contract, the StationaryMonotonicity import, both leaves, then the parent theorem) compiles, and `exact Submission.stationary_monotonicity_identity_8_3_4` closes StationaryMonotonicityIdentity.

An independent reviewer agent confirmed the mathematics and all cited line numbers.
