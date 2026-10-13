# Parent-supplied natural-language proof

- Parent DAG node: `root.monotonicity_density-a1.monotonicity_formula-a1`
- Child DAG node: `root.monotonicity_density-a1.monotonicity_formula-a1.integrating_factor_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 (4.1 and 4.3) of the parent node's supplied proof of Simon, Introduction to Geometric Measure Theory, Ch. 8, 3.3 (printed p. 210, "Cf. 4.7 of Ch. 4"; the integrating-factor argument of Ch. 4, 3.15–3.17, printed pp. 92–93): multiplying the differential inequality for f = I/tⁿ by the integrating factor e^{Lt} and integrating from a to b by the mean value theorem. It is stated here for arbitrary real functions. In the parent it is applied, for each small ε > 0, on [a, b] = [σ, ρ] with L = (1 + ε)Λ, f(t) = I_ε(t)/tⁿ (I_ε = SimonGMT's cutoffMass x (monotonicityCutoff ε)), f'(t) = J'_ε(t)/tⁿ − δV(X_t)/t^{n+1} (SimonGMT's hasDerivAt_normalized_weightedCutoffMass with h ≡ 1), g = G_ε (the truncated-defect cutoff integral) and g' = G'_ε.

Implementation note: this node is expected to be a leaf: a single declaration Submission.mono833_integrating_factor_comparison using only the frozen contract's imports. A scratch proof of exactly this shape compiled with only `import GMT.Ch08.Submission` (axioms: propext, Classical.choice, Quot.sound) and passed the leaf-delta check, using HasDerivAt.const_mul and HasDerivAt.exp on (hasDerivAt_id t), HasDerivAt.mul, HasDerivAt.fun_sub (the pointwise-difference form, so that HasDerivAt.deriv rewrites `deriv (fun s ↦ e^{Ls} f s − g s) t`), monotoneOn_of_deriv_nonneg on convex_Icc, interior_subset, Real.one_le_exp and nlinarith.

Proof. Fix L, a, b ∈ ℝ and f, g, f', g' : ℝ → ℝ with: (H1) L ≥ 0; (H2) a ≥ 0; (H3) a ≤ b; (H4) for every t ∈ [a, b], f has derivative f'(t) at t; (H5) for every t ∈ [a, b], g has derivative g'(t) at t; (H6) 0 ≤ f'(t) + L·f(t) for every t ∈ [a, b]; (H7) g'(t) ≤ f'(t) + L·f(t) for every t ∈ [a, b]. We show e^{La}·f(a) + (g(b) − g(a)) ≤ e^{Lb}·f(b).

1. Let F(s) := e^{Ls}·f(s). For t ∈ [a, b], s ↦ e^{Ls} has derivative L·e^{Lt} at t (chain rule), so by (H4) and the product rule F has derivative F'(t) = L·e^{Lt}·f(t) + e^{Lt}·f'(t) = e^{Lt}·(f'(t) + L·f(t)) at t.

2. Let H(s) := F(s) − g(s). By 1 and (H5), for every t ∈ [a, b], H has derivative H'(t) = e^{Lt}·(f'(t) + L·f(t)) − g'(t) at t. In particular H is continuous at every point of [a, b] (hence continuous on [a, b]) and differentiable at every point of the open interval (a, b), with deriv H(t) = H'(t) there.

3. H' ≥ 0 on (a, b). Let t ∈ (a, b) ⊆ [a, b]. Then t ≥ a ≥ 0 and L ≥ 0, so L·t ≥ 0 and e^{Lt} ≥ 1. Put u := f'(t) + L·f(t); u ≥ 0 by (H6). Hence e^{Lt}·u ≥ u (as (e^{Lt} − 1)·u ≥ 0) and u ≥ g'(t) by (H7), so H'(t) = e^{Lt}·u − g'(t) ≥ 0.

4. By the mean value theorem in the form "a function continuous on the convex set [a, b], differentiable on its interior (a, b) with nonnegative derivative there, is monotone on [a, b]" (monotoneOn_of_deriv_nonneg; interior [a, b] = (a, b)), H is non-decreasing on [a, b]. Since a, b ∈ [a, b] and a ≤ b (H3), H(a) ≤ H(b), i.e.
   e^{La}·f(a) − g(a) ≤ e^{Lb}·f(b) − g(b).

5. Adding g(b) to both sides gives e^{La}·f(a) + (g(b) − g(a)) ≤ e^{Lb}·f(b), the claim. As L, a, b, f, g, f', g' were arbitrary, the statement holds.

## Key steps

1. F(t) = e^{Lt}·f(t) has derivative e^{Lt}·(f'(t) + L·f(t)) at each t ∈ [a, b] (chain and product rules).
2. H = F − g has derivative e^{Lt}·(f' + L·f) − g' on [a, b], so H is continuous on [a, b] and differentiable on (a, b).
3. On (a, b): L·t ≥ 0 gives e^{Lt} ≥ 1, and f' + L·f is both ≥ 0 and ≥ g', so H' ≥ 0.
4. Mean value theorem (monotoneOn_of_deriv_nonneg on the convex set [a, b]) gives H(a) ≤ H(b), which rearranges to the claim.

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
