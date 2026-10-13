# Parent-supplied natural-language proof

- Parent DAG node: `root.monotonicity_density-a1.monotonicity_formula-a1`
- Child DAG node: `root.monotonicity_density-a1.monotonicity_formula-a1.exp_weighted_density_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 8 of the parent node's supplied proof of Simon, Introduction to Geometric Measure Theory, Ch. 8, 3.3 (printed p. 210): existence and finiteness of Θⁿ(μ_V, x) and the bound Θ ≤ e^{Λσ}ω_n^{-1}σ^{-n}μ_V(B_σ(x)) follow from monotonicity of e^{Λρ}ω_n^{-1}ρ^{-n}μ_V(B_ρ(x)) on (0, ρ0) and e^{Λρ} → 1 as ρ ↓ 0. It is stated here abstractly for a [0,∞]-valued function P; in the parent it is applied with P = densityRatio n μ_V x (so the conclusion Tendsto P (𝓝[>] 0) (𝓝 θ) is HasDensity n μ_V x θ by definition). Only the order topologies of ℝ and [0,∞] and continuity of multiplication on [0,∞] away from (0,∞),(∞,0) are used.

Implementation note: this node is expected to be a leaf: a single declaration Submission.mono833_exp_weighted_density_limit using only the frozen contract's imports. A scratch proof of exactly this shape compiled with only `import GMT.Ch08.Submission` (axioms: propext, Classical.choice, Quot.sound) and passed the leaf-delta check, using MonotoneOn.tendsto_nhdsWithin_Ioo_right (with nonempty_Ioo and OrderBot.bddBelow), sInf_le with mem_image_of_mem, ENNReal.ofReal_mul, Real.exp_add, ENNReal.continuous_ofReal, Real.continuous_exp, nhdsWithin_le_nhds, ENNReal.Tendsto.mul (side conditions Or.inl one_ne_zero and Or.inr ENNReal.one_ne_top), Filter.Tendsto.congr, ENNReal.mul_ne_top and ne_top_of_le_ne_top.

Notation. For ρ ∈ ℝ put h(ρ) := ofReal(e^{Λρ})·P(ρ) ∈ [0,∞]; I := (0, ρ0) = Ioo 0 ρ0; "t → 0+" means along the filter 𝓝[>] 0 of ℝ.

Proof. Fix P : ℝ → [0,∞] and ρ0, Λ ∈ ℝ with (H1) ρ0 > 0; (H2) h is monotone (non-decreasing) on I; (H3) P(ρ0/2) ≠ ∞.

1. Definition of θ. I is nonempty (ρ0/2 ∈ I by (H1)) and h(I) ⊆ [0,∞] is bounded below by 0. Put θ := inf h(I) ∈ [0,∞].

2. h(t) → θ as t → 0+. This is MonotoneOn.tendsto_nhdsWithin_Ioo_right applied to h on I = (0, ρ0); directly: in the order topology of [0,∞] it suffices that (a) for every a < θ, h(t) > a for all t in a set of 𝓝[>] 0, and (b) for every b > θ, h(t) < b for all t in a set of 𝓝[>] 0. For (a) take I itself, which belongs to 𝓝[>] 0 since ρ0 > 0: for t ∈ I, h(t) ≥ θ > a. For (b), b > θ = inf h(I) gives s ∈ I with h(s) < b; every t ∈ (0, s) lies in I with t ≤ s, so h(t) ≤ h(s) < b by (H2); and (0, s) ∈ 𝓝[>] 0.

3. Lower bound. For every σ with 0 < σ < ρ0, σ ∈ I, so θ = inf h(I) ≤ h(σ) = ofReal(e^{Λσ})·P(σ). This is the third conclusion.

4. Finiteness. By 3 with σ = ρ0/2 (0 < ρ0/2 < ρ0 by (H1)), θ ≤ ofReal(e^{Λρ0/2})·P(ρ0/2); the first factor is finite (ofReal of a real number) and the second is finite by (H3), so their product is finite and θ ≠ ∞.

5. Removing the weight. For every t ∈ ℝ, since e^{−Λt} ≥ 0, ofReal(e^{−Λt})·h(t) = (ofReal(e^{−Λt})·ofReal(e^{Λt}))·P(t) = ofReal(e^{−Λt}·e^{Λt})·P(t) = ofReal(e^{0})·P(t) = ofReal(1)·P(t) = P(t).

6. The function t ↦ ofReal(e^{−Λt}) from ℝ to [0,∞] is continuous (composition of continuous maps), with value ofReal(1) = 1 at t = 0; hence it tends to 1 as t → 0 and a fortiori as t → 0+ (𝓝[>] 0 ≤ 𝓝 0).

7. Multiplication [0,∞] × [0,∞] → [0,∞] is continuous at (1, θ) because 1 ≠ 0 and 1 ≠ ∞ (ENNReal.Tendsto.mul, whose side conditions are "1 ≠ 0 or θ ≠ ∞" and "θ ≠ 0 or 1 ≠ ∞"). By 2 and 6, ofReal(e^{−Λt})·h(t) → 1·θ = θ as t → 0+, and by 5 the left side equals P(t) for every t. Hence P(t) → θ as t → 0+.

8. Conclusion. θ witnesses the statement: P → θ along 𝓝[>] 0 (step 7), θ ≠ ∞ (step 4), and θ ≤ ofReal(e^{Λσ})·P(σ) for all 0 < σ < ρ0 (step 3). As P, ρ0, Λ were arbitrary, the statement holds.

## Key steps

1. θ := inf of h(ρ) = ofReal(e^{Λρ})·P(ρ) over (0, ρ0); the monotone h tends to θ at 0+ (MonotoneOn.tendsto_nhdsWithin_Ioo_right).
2. θ ≤ h(σ) for 0 < σ < ρ0; in particular θ ≤ h(ρ0/2) < ∞.
3. P(t) = ofReal(e^{−Λt})·h(t) for all t, and ofReal(e^{−Λt}) → 1 as t → 0+.
4. ENNReal.Tendsto.mul at (1, θ) (1 ≠ 0, 1 ≠ ∞) gives P(t) → θ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean <snapshot>/project/GMT/Ch08/Contract.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487); git -C .lake/packages/simongmt rev-parse HEAD (2b3663083f3fe399b6296fb8eaee52169170e197)`
- `grep -n '^public import' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/*.lean (VarifoldConvergence -> FirstVariationRiesz; radial modules reachable only via StationaryMonotonicity)`
- `lake env lean /tmp/mono833_split/Avail.lean (after import GMT.Ch08.Submission: Varifold.isFirstVariationPolarRepresentation_riesz, lintegral_eq_lintegral_meas_le, MonotoneOn.tendsto_nhdsWithin_Ioo_right available; Chapter04.monotonicityCutoff, Varifold.cutoffMass, Grassmannian.radialNormalSq unknown)`
- `read /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py (check_source_delta) and parent_verification.py (check_parent_git_delta)`
- `git show e163fc58e786f6e1d09778b6af00bb997d28a43e:GMT/Ch08/Submission.lean (accepted 8.3.4 parent adds import Poincare.SimonGMT.Chapter08.StationaryMonotonicity); git show 3c6818bddadb89b47160584ce4f8ef0c883fcc29:GMT/Ch08/Submission.lean (accepted weighted-radial parent, ~150-line glue)`
- `python3 scan of dag.json lean_name / lean_statement / status (227 names; no mono833_* names; related accepted nodes intcpt_allard_first_variation_le_sup_mul, intcpt_allard_wrm_cutoff_mass_hasDerivAt not reusable for the weighted bound)`
- `grep -n in snapshot mathlib: lintegral_eq_lintegral_meas_le (MeasureTheory/Integral/Layercake.lean:445), MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457), IsClosed.csSup_mem (Topology/Order/Monotone.lean:426), setLIntegral_mono' (Integral/Lebesgue/Basic.lean:254), lintegral_const_mul' (Integral/Lebesgue/Add.lean:420), monotoneOn_of_deriv_nonneg (Analysis/Calculus/Deriv/MeanValue.lean:411), ENNReal.Tendsto.mul (Topology/Instances/ENNReal/Lemmas.lean:337), integral_eq_lintegral_of_nonneg_ae (Integral/Bochner/Basic.lean:515), abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471), contDiff_norm_sq (InnerProductSpace/Calculus.lean:140), ENNReal.toReal_mono (Basic/ENNReal/Real.lean:67)`
- `grep -n theorem names in SimonGMT Chapter08: isFirstVariationPolarRepresentation_riesz (FirstVariationRiesz.lean:133), hasDerivAt_integral_radialCutoff_of_radius (RadialCutoffDifferentiation.lean:91), weightedCutoffMass_eq_weight_integral / hasDerivAt_weightedCutoffNormalMass / hasDerivAt_normalized_weightedCutoffMass (WeightedRadialIdentity.lean:76/96/200), tendsto_integral_radialCutoff / tendsto_cutoffMass / scaledRadialCutoffDeriv_defect_bounds (StationaryCutoff.lean:63/111/142), integrableOn_truncatedRadialDefect / integrableOn_radialDefect_annulus / ofReal_normalizedBallMass_real (StationaryMonotonicity.lean:28/37/124), normalProject_eq_sub / norm_normalProject_radial_sq (RadialFirstVariation.lean:81/123); Chapter04/FirstVariation.lean monotonicityCutoff lemmas (828-886)`
- `lake env lean /tmp/mono833_split/Types.lean (four child types elaborate; #check_failure confirms names unused)`
- `lake env lean /tmp/mono833_split/Parent.lean (parent glue with sorried children; axioms propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean /tmp/mono833_split/ChildC1a.lean, ChildC1.lean, ChildC2C3.lean (each child proved with only import GMT.Ch08.Submission; standard axioms)`
- `lake env lean /tmp/mono833_split/EndToEnd_nowarn.lean (#print axioms Submission.monotonicity_formula_8_3_3: propext, Classical.choice, Quot.sound; no warnings) and LeavesInSubmission.lean (four leaves inside the real frozen Submission.lean)`
- `python3 check_source_delta(frozen Submission, Submission + one child declaration) for each child (all OK)`
- `sed -n 262,330p book/chapter-08.txt (printed 3.1-3.6, p. 210-211); sed -n 380,432p book/chapter-04.txt (3.15-3.17 integrating factor, p. 92-93)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-monotonicity-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-monotonicity-formula-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-monotonicity-density-a1-stationary-identity-a1-density-limit-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryMonotonicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryCutoff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialCutoffDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/mono833_split/Types.lean`
- `/tmp/mono833_split/Parent.lean`
- `/tmp/mono833_split/ChildC1a.lean`
- `/tmp/mono833_split/ChildC1.lean`
- `/tmp/mono833_split/ChildC2C3.lean`
- `/tmp/mono833_split/EndToEnd_nowarn.lean`
- `/tmp/mono833_split/LeavesInSubmission.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c; its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot's Mathlib has no varifold or monotonicity-formula material, so the analytic content comes from the pinned SimonGMT package (rev 2b366308).

SimonGMT already proves the Λ = 0 case and every radial ingredient of the general-Λ proof, but those modules are reachable only through Chapter08.StationaryMonotonicity, which the frozen imports exclude. Workflow leaves cannot add imports (leaf_verification.check_source_delta). The accepted 8.3.4 parent shows that a non-leaf parent may add that import.

Hence the split: the SimonGMT-dependent glue stays in this (now non-leaf) parent, and the four children are generic lemmas provable from the frozen imports alone:
- the polar representation isFirstVariationPolarRepresentation_riesz (FirstVariationRiesz.lean:133) is reachable via VarifoldConvergence;
- the layer cake (Layercake.lean:445), the mean value theorem (Deriv/MeanValue.lean:411) and MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457) are in Mathlib.

Scratch Lean files confirm the plan:
- each child, as a single declaration with only `import GMT.Ch08.Submission`, compiles with standard axioms and passes the leaf-delta check;
- the parent glue plus the four children yields Submission.monotonicity_formula_8_3_3 : MonotonicityFormula with axioms propext, Classical.choice, Quot.sound.

No existing DAG declaration has these types; the proposed names are fresh. An independent reviewer agent reproduced all checks and approved.
