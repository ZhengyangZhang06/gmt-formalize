# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.homogeneous_infinite_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, used where it verifies Simon's hypothesis A.3(1) (book/chapter-A.txt lines 26–27: sing φ = ∅ if φ is a constant multiple of the indicator function of an n-dimensional subspace) for its density-threshold map sing (parent step 7 (A.3)(1)), and in its conclusion, step 8. Simon prints no such lemma; it is needed only because the parent's sing is a density threshold (the parent's departure [D1]). Step 8 reads: "Finally ν(ℝ^P) = ∞. First, ν ≠ 0, since otherwise dens ν ≡ 0 < c and E = ∅. With y = 0, dens ν(λx) = dens ν x. By (2) and Hⁿ(λ·s) = λⁿHⁿ(s) … ν(λ·s) = λⁿν(s) … ν(B_{tR₁}(0)) = tⁿν(B_{R₁}(0)) → ∞". The lemma below states this for a measure whose density is its own homogeneous density function g. The scaling half of that argument is exactly the sibling nonhomogeneous_mass (Submission.idtp_fons_cc_psf_nonhomogeneous: a measure of finite positive total mass is not Hⁿ.withDensity f with f(t·w) = f(w)), which is used here. In the parent, the same statement also settles the case c′ ≥ c of step 7 (A.3)(1), where μ = Hⁿ.withDensity(ofReal(c′)·1_L): the density c′·1_L is 0-homogeneous (L is a linear subspace) and equals c′ ≥ c > 0 at x₀ = 0 ∈ L, so μ(ℝ^P) = ∞ follows without computing Hⁿ(L) through an isometry with ℝⁿ.
1. (Nonzero mass.) Suppose μ(ℝ^P) = 0. Then μ = 0 (Measure.measure_univ_eq_zero). Hence μ(B_ρ(x₀)) = 0 for every ρ, so μ(B_ρ(x₀))/(ω_n·ofReal(ρⁿ)) = 0 for every ρ (0 divided by anything is 0 in [0, ∞]). The limsup of the constant function 0 along the nontrivial filter 𝓝[>]0 is 0 (limsup_const), so g(x₀) = (0).toReal = 0 by the first hypothesis. This contradicts g(x₀) > 0. Hence μ(ℝ^P) ≠ 0.
2. (Finite mass is impossible.) Suppose μ(ℝ^P) ≠ ∞. Put f(x) := ofReal(g(x)) ∈ [0, ∞]. For t > 0 and x ∈ ℝ^P, f(t·x) = ofReal(g(t·x)) = ofReal(g(x)) = f(x). The sibling nonhomogeneous_mass applies to ν := μ and this f: n ≥ 1, μ(ℝ^P) ≠ 0 (step 1), μ(ℝ^P) ≠ ∞ and f(t·w) = f(w) for all t > 0 and w. It gives μ ≠ Hⁿ.withDensity f. But μ = Hⁿ.withDensity(x ↦ ofReal(g(x))) = Hⁿ.withDensity f by hypothesis, a contradiction.
3. Hence μ(ℝ^P) = ∞. ∎

## Key steps

1. If μ(ℝ^P) = 0 then μ = 0, every density ratio vanishes, and g(x₀) = 0, contradicting g(x₀) > 0.
2. f := ofReal ∘ g is 0-homogeneous, so nonhomogeneous_mass shows that μ = Hⁿ.withDensity f cannot have finite positive total mass.
3. Hence μ(ℝ^P) = ∞.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git -C .lake/packages/mathlib rev-parse HEAD; git log --oneline -1`
- `sed -n 1,260p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, euclideanHausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume)`
- `rg --no-ignore --hidden -n "theorem MonotoneOn.tendsto_nhdsWithin_Ioo_right|theorem le_limsup_of_frequently_le|theorem Ioo_mem_nhdsGT |theorem measure_ball_pos|theorem measure_ball_lt_top|theorem ofReal_inv_of_pos|theorem le_div_iff_mul_le|theorem preimage_closure|protected theorem Tendsto.mul |protected theorem Tendsto.div_const|theorem Tendsto.limsup_eq|theorem ofReal_le_ofReal_iff " <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg --no-ignore --hidden -n "tendsto_nhdsWithin_Ioo_right|^lemma le_limsup_of_frequently_le|Ioo_mem_nhdsGT \(" <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `grep -rn "theorem extraction_of_frequently_atTop \|theorem IsCompact.tendsto_subseq\|theorem Ioo_mem_nhdsLT" <snapshot>/mathlib/Mathlib --include=*.lean`
- `rg --no-ignore --hidden -n "dimred_tr_mcr|idtp_fons_cr_density|cbr_vague_portmanteau|idtp_fons_cc_psf|idtp_fons_cc_tm" <snapshot>/project (exit 1, no match); grep -rn dimred_tr_mcr GMT .lake/packages/simongmt --include=*.lean (no match)`
- `python3 over dag.json: lean_statement searches for 'limsup', 'MonotoneOn'+'Real.exp (Λ', 'univ = ∞', 'withDensity', "''"+'ENNReal.ofReal (lam ^ n)', '∃ k₀'+'dist x z < ε'; lean_name collision check for the three new names`
- `python3 /tmp/mcr-split/check_reuse.py <six reused names>: git cat-file -e <candidate>^{commit}; git show <candidate>:GMT/Ch07/Submission.lean; declared type of Submission.X vs dag.json lean_statement up to whitespace; sorry lines`
- `git show 509564aca5:GMT/Ch07/Submission.lean, lines 2134-2400 (proof of Submission.idtp_fons_flat_class_reduction, the analogous application of abstract_dimension_reduction)`
- `lake env lean /tmp/mcr-split/lean/Types.lean; lake env lean /tmp/mcr-split/lean/Assembly.lean; lake env lean /tmp/mcr-split/lean/N1.lean; lake env lean /tmp/mcr-split/lean/Small.lean; lake env lean /tmp/mcr-split/lean/Names.lean`
- `lake env lean /tmp/mcr-split/reuse/<name>/Submission.lean (candidate file + #print axioms GMT.Ch07.Submission.<name>) for the six reused candidates`
- `grep -n 'semicontinu\|A\.4' book/chapter-07.txt; sed -n 320,330p;378,406p;474,492p book/chapter-07.txt; sed -n 1,80p book/chapter-A.txt (book citations for the new children)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-095240e0d0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-59efd7b202/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3a383ffd93/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5a68c13034/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-644d8df7fd/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-66521e895c/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-959ef3c94c/isolated-comparator-result.json`
- `/tmp/mcr-split/lean/Types.lean`
- `/tmp/mcr-split/lean/Assembly.lean`
- `/tmp/mcr-split/lean/N1.lean`
- `/tmp/mcr-split/lean/Small.lean`
- `/tmp/mcr-split/check_reuse.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`

Pins match: the snapshot manifest records project b4d606d and mathlib 25730c7c, which equal the workspace HEAD and .lake/packages/mathlib. Every library fact used by the new children and the assembly exists in the snapshot mathlib, for example: MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457), le_limsup_of_frequently_le (Order/LiminfLimsup.lean:241), Ioo_mem_nhdsLT (Topology/Order/OrderClosed.lean:282), extraction_of_frequently_atTop (Order/Filter/AtTopBot/Basic.lean:114), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), ENNReal.Tendsto.mul/div_const (Topology/Instances/ENNReal/Lemmas.lean:337/481), ENNReal.le_div_iff_mul_le (Basic/ENNReal/Inv.lean:369), Homeomorph.preimage_closure (Topology/Homeomorph/Defs.lean:300) and euclideanHausdorffMeasure_def (Geometry/Euclidean/Volume/Measure.lean:74). The DAG search found six comparator-accepted declarations, reused at identical frozen types. Four give steps 1–4 after rewriting with the defining equation of dens; step 4 then has an existential constant κ > 0 in place of c_n⁻¹. The other two are the step-8 infinite-mass core and the portmanteau claim of Lemma D. No dimred_tr_mcr_ identifier exists in dag.json, the snapshot project, GMT or simongmt, so the three new names are unreserved. Lean checks: all child types elaborate; the selected type compiles from (ADR) and the seven directly used children with no sorryAx; each new child compiles from exactly its declared sibling dependencies; each reused candidate recompiles with only propext, Classical.choice and Quot.sound.
