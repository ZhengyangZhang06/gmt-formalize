# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1`
- Child DAG node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1.density_borel_representative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 (Borel representative of θ) of the parent proof.

Notation: B_r(x) := closedBall x r, and densityRatio n μ x r = μ(B_r(x)) / (ω_n · ofReal(r)^n), where ω_n := unitBallVolume n does not depend on x.

1. Ball masses are Borel functions of the centre. Fix r ∈ ℝ. The set S_r := {(x, y) ∈ ℝ^N × ℝ^N : dist(y, x) ≤ r} is closed, as the preimage of (−∞, r] under the continuous map (x, y) ↦ dist(y, x). Since ℝ^N is second countable, the product σ-algebra of ℝ^N × ℝ^N is its Borel σ-algebra, so S_r is measurable. Its section at x is {y : dist(y, x) ≤ r} = B_r(x). Because μ is s-finite, Mathlib's measurable_measure_prodMk_left (MeasureTheory/Measure/Prod.lean:97) shows that x ↦ μ({y : (x, y) ∈ S_r}) = μ(B_r(x)) is measurable.
2. Consequently, for every r ∈ ℝ, x ↦ densityRatio n μ x r = μ(B_r(x)) / (ω_n · ofReal(r)^n) is measurable: it is a measurable [0, ∞]-valued function divided by a constant (Measurable.div_const).
3. Define g(x) := liminf_{k → ∞} densityRatio n μ x (1/(k + 1)), with k ∈ ℕ and the liminf taken along atTop. As a liminf along ℕ of measurable [0, ∞]-valued functions, g is measurable (Measurable.liminf, MeasureTheory/Constructions/BorelSpace/Order.lean:1058).
4. Let x ∈ ℝ^N and t ∈ [0, ∞] with HasDensity n μ x t, i.e. densityRatio n μ x ρ → t as ρ → 0 within (0, ∞) (the filter 𝓝[>] 0). The numbers ρ_k := 1/(k + 1) are positive and tend to 0 (tendsto_one_div_add_atTop_nhds_zero_nat), hence ρ_k → 0 within (0, ∞) (tendsto_nhdsWithin_iff). Composing the two limits, densityRatio n μ x (1/(k + 1)) → t as k → ∞. Since atTop on ℕ is a nontrivial filter, the liminf equals t (Filter.Tendsto.liminf_eq). Thus g(x) = t.
5. Hence g is Borel measurable and g(x) = t whenever HasDensity n μ x t. ∎

## Key steps

1. x ↦ μ(B_r(x)) is Borel: measurable_measure_prodMk_left for the s-finite μ and the closed set {(x, y) : dist(y, x) ≤ r}.
2. Hence x ↦ densityRatio n μ x r is Borel for each r.
3. g(x) := liminf_k densityRatio n μ x (1/(k+1)) is Borel (Measurable.liminf).
4. If HasDensity n μ x t, the ratios along ρ_k = 1/(k+1) → 0⁺ tend to t, so g(x) = t.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); sha256sum GMT/Ch08/{Contract,Submission}.lean (2e5cd5b3…, identical)`
- `rg -n 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_measure_inter_div' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -rn 'theorem restrict_iUnion_apply_eq_iSup|setLIntegral_iUnion_of_directed|lintegral_restrict_iUnion_of_directed' mathlib/Mathlib/MeasureTheory`
- `grep -rn 'CompactExhaustion|exists_open_between_and_isCompact_closure|exists_compact_between|IsSigmaCompact' mathlib/Mathlib/Topology (no open-subset exhaustion lemma)`
- `rg -n 'measurable_measure_prodMk_left|Measurable.liminf|withDensity_rnDeriv_eq|withDensity_congr_ae|withDensity_apply|volume_euclideanSpace_eq_dirac|notMem_iff_infDist_pos|exists_nat_one_div_lt|ae_restrict_mem₀|measure_eq_zero_iff_ae_notMem|le_toOuterMeasure_caratheodory|Tendsto.liminf_eq|Tendsto.limsup_eq|Directed.measure_iUnion|measure_le_inter_add_sdiff|interior_closedBall|continuous_infDist_pt|infDist_zero_of_mem|tendsto_one_div_add_atTop_nhds_zero_nat|isFiniteMeasure_restrict|measure_ball_lt_top|measure_ball_pos' mathlib/Mathlib`
- `grep -rn 'protected theorem Tendsto.mul|protected theorem Tendsto.div|theorem inv_mul_cancel|theorem mul_inv|top_div_of_ne_top' mathlib ENNReal files`
- `grep -rn 'theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem volume_euclidean_ball_eq|realUnitBallVolume_zero|theorem simonHausdorffMeasureReal_toOuterMeasure|theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|def dimensionalUpperDensity|def dimensionalDensityQuotient|def realUnitBallVolume' simongmt/Poincare/SimonGMT (rev 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `grep -n 'weight_finite_on_compact|weight.instSigmaFinite|isOpen_domain' simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `grep -rln 'exhaust' simongmt/Poincare/SimonGMT (no reusable open-set exhaustion lemma)`
- `python3 dag.json: frozen lean_statement of the four sibling nodes; lean_name collision check for frt_weq_* in dag.json, run directory, .swarm-worktrees and .recursive-lean-dispatch-worktrees (0 hits)`
- `gmt-compare.py contract_scope/child_modules replay + lean_contract.validate_lean_statement on the 5 child statements`
- `lake env lean Scratch/Children.lean, Scratch/NC_<key>.lean (5 NodeChallenge files), Scratch/FullNames.lean (pp.fullNames)`
- `lake env lean Scratch/Combined.lean (5 child proofs + sorry-free parent assembly; #print axioms)`
- `sed book/chapter-08.txt lines 1-240 (printed proof of 1.2) and book/chapter-03.txt lines 280-420 (Ch. 3, 1.7-1.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-eq-theta-hausdorff-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Contract.lean and Submission.lean are byte-identical.

Mathlib supplies all of the following, so none of them needs a separate node:
- Besicovitch.ae_tendsto_rnDeriv and ae_tendsto_measure_inter_div (Besicovitch.lean:1078 and :1105).
- withDensity_rnDeriv_eq (RadonNikodym.lean:60) and withDensity_congr_ae / withDensity_apply (WithDensity.lean:88 and :44).
- measurable_measure_prodMk_left (Prod.lean:97) and Measurable.liminf (BorelSpace/Order.lean:1058).
- setLIntegral_iUnion_of_directed (Lebesgue/Basic.lean:668), which needs no measurability, and Directed.measure_iUnion (Continuity.lean:36).
- volume_euclideanSpace_eq_dirac (Haar/InnerProductSpace.lean:142) and IsClosed.notMem_iff_infDist_pos (HausdorffDistance.lean:584).
- ENNReal.Tendsto.mul and ENNReal.Tendsto.div (ENNReal/Lemmas.lean:337 and :471).

Mathlib has CompactExhaustion only for whole spaces. Neither Mathlib nor SimonGMT has a ready exhaustion of an open subset with K_p ⊆ interior K_{p+1}, so child 1 is a genuine obligation.

SimonGMT supplies:
- Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity (DensityComparison.lean:251), valid for every real dimension n ≥ 0.
- simonHausdorffMeasureReal_toOuterMeasure (Hausdorff.lean:445) and realUnitBallVolume_zero (Hausdorff.lean:510).
- volume_euclidean_ball_eq (EuclideanHausdorffUpper.lean:71, n > 0).
- Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (AreaLiteral.lean:42, every n ∈ ℕ).
- Varifold.weight_finite_on_compact and weight.instSigmaFinite (Varifold.lean:576 and :615).
With these, the upper-density child holds uniformly for every n ≥ 0.

All five child lean_statements elaborate in the comparator's NodeChallenge scope and pass validate_lean_statement. Complete scratch proofs of all five use only propext, Classical.choice and Quot.sound. The parent proof checks against its exact frozen type, with sorryAx coming only from the four sibling stubs, whose types are byte-identical to dag.json. The frt_weq_* names collide with nothing.
