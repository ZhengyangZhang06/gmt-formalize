# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1.monotone_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: extracted from the parent's supplied proof of idtp_fons_cc_monotonicity_bounds, steps A3–A5. The same argument is used in step B1 with Λ = 0. It is the 'monotonicity gives a lower density bound' step of Simon 7.3.1/7.3.3 (chapter-07.txt lines 326–330 and 420–430).

Notation. ω := ω_n = unitBallVolume n = volume(B_1(0)) in Euclid n = ℝ^n, and ofReal = ENNReal.ofReal. For τ ∈ ℝ put
  f(τ) := ofReal(e^{Λτ}/τ^n)·m(τ),
  q(τ) := m(τ)/(ω·ofReal(τ^n)).
Hypotheses:
- 1 ≤ θ and 0 < σ < ρ;
- f is nondecreasing on (0, ρ): if a ≤ b are in (0, ρ), then f(a) ≤ f(b);
- q(τ) → ofReal θ in [0, ∞] along 𝓝[>]0.
All arithmetic is in [0, ∞] unless stated otherwise.

1. (0 < ω < ∞.) Volume on the finite-dimensional inner product space Euclid n is an additive Haar measure. So it is positive on nonempty open sets and finite on bounded subsets of the proper space Euclid n. The open unit ball B_1(0) is nonempty, open and bounded, so ω ≠ 0 (measure_ball_pos) and ω ≠ ∞ (measure_ball_lt_top). No restriction on n is needed: for n = 0, Euclid 0 is a point and ω = 1. Also, for τ > 0 we have τ^n > 0, so ofReal(τ^n) is positive and finite.

2. (Factorization of f on (0, ∞).) Let τ > 0.
- Since τ^n > 0, ENNReal.ofReal_div_of_pos gives ofReal(e^{Λτ}/τ^n) = ofReal(e^{Λτ})/ofReal(τ^n).
- Since ω ≠ 0 and ω ≠ ∞, mul_div_assoc and then ENNReal.mul_div_mul_left give ω·q(τ) = (ω·m(τ))/(ω·ofReal(τ^n)) = m(τ)/ofReal(τ^n).
- Writing a/b = a·b⁻¹ and using commutativity and associativity in [0, ∞]: f(τ) = ofReal(e^{Λτ})·ofReal(τ^n)⁻¹·m(τ) = ofReal(e^{Λτ})·(ω·q(τ)).

3. (Limit of f at 0⁺.)
- The map τ ↦ ofReal(e^{Λτ}) is continuous on ℝ: it composes τ ↦ Λτ, Real.exp and the continuous map ENNReal.ofReal. So it tends to ofReal(e^{Λ·0}) = ofReal(1) = 1 as τ → 0, and also along 𝓝[>]0 ≤ 𝓝 0.
- By hypothesis q(τ) → ofReal θ along 𝓝[>]0. Since ω ≠ ∞, ENNReal.Tendsto.const_mul gives ω·q(τ) → ω·ofReal θ.
- ENNReal.Tendsto.mul applies to these two limits because the first limit is 1, which is neither 0 nor ∞. It gives ofReal(e^{Λτ})·(ω·q(τ)) → 1·(ω·ofReal θ) = ω·ofReal θ along 𝓝[>]0.
- By step 2 this function equals f on (0, ∞), which belongs to 𝓝[>]0 (self_mem_nhdsWithin). Hence f(τ) → ω·ofReal θ as τ → 0⁺ (Tendsto.congr').

4. (Comparison by monotonicity.) Let τ ∈ (0, σ]. Then 0 < τ ≤ σ < ρ, so τ and σ both lie in (0, ρ) and τ ≤ σ. Since f is nondecreasing on (0, ρ), f(τ) ≤ f(σ). Because σ > 0, the interval (0, σ] belongs to 𝓝[>]0 (Ioc_mem_nhdsGT). So f(τ) ≤ f(σ) holds eventually along 𝓝[>]0, which is a nontrivial filter on ℝ (nhdsGT_neBot). By step 3 and le_of_tendsto, ω·ofReal θ ≤ f(σ).

5. (Use of θ ≥ 1.) From 1 ≤ θ we get 1 ≤ ofReal θ (ENNReal.one_le_ofReal). Hence
  ω = ω·1 ≤ ω·ofReal θ ≤ f(σ) = ofReal(e^{Λσ}/σ^n)·m(σ).

6. (Removing the weight.) Multiplication in [0, ∞] is monotone in each factor. Multiply the inequality ω ≤ f(σ) of step 5 on the right by ofReal(σ^n), then on the left by ofReal(e^{−(Λσ)}):
  ofReal(e^{−(Λσ)})·(ω·ofReal(σ^n)) ≤ ofReal(e^{−(Λσ)})·(ofReal(e^{Λσ}/σ^n)·m(σ)·ofReal(σ^n)).
The real numbers e^{−(Λσ)} and e^{−(Λσ)}·(e^{Λσ}/σ^n) are ≥ 0 because σ > 0. So two applications of ENNReal.ofReal_mul, together with commutativity, rewrite the right-hand side as
  ofReal(e^{−(Λσ)}·(e^{Λσ}/σ^n)·σ^n)·m(σ).
Finally e^{−(Λσ)} = (e^{Λσ})⁻¹ (Real.exp_neg), e^{Λσ} ≠ 0 and σ^n ≠ 0. So e^{−(Λσ)}·(e^{Λσ}/σ^n)·σ^n = 1, and the right-hand side equals ofReal(1)·m(σ) = 1·m(σ) = m(σ).

7. Therefore ofReal(e^{−(Λσ)})·(ω_n·ofReal(σ^n)) ≤ m(σ). ∎

## Key steps

1. 0 < ω_n < ∞ because volume on Euclid n is an additive Haar measure and the unit ball is nonempty, open and bounded. Also ofReal(τ^n) ∈ (0, ∞) for τ > 0.
2. For τ > 0, f(τ) = ofReal(e^{Λτ})·(ω_n·q(τ)), by ENNReal.ofReal_div_of_pos and ENNReal.mul_div_mul_left.
3. ofReal(e^{Λτ}) → 1 and ω_n·q(τ) → ω_n·ofReal θ, so f(τ) → ω_n·ofReal θ as τ → 0⁺ (ENNReal.Tendsto.mul, then congruence on (0, ∞)).
4. f(τ) ≤ f(σ) for τ ∈ (0, σ], and (0, σ] ∈ 𝓝[>]0, so ω_n·ofReal θ ≤ f(σ) by le_of_tendsto. θ ≥ 1 then gives ω_n ≤ f(σ).
5. Multiply by ofReal(e^{−(Λσ)})·ofReal(σ^n). The real factor e^{−(Λσ)}·(e^{Λσ}/σ^n)·σ^n equals 1, which gives ofReal(e^{−(Λσ)})·(ω_n·ofReal(σ^n)) ≤ m(σ).

## Reference use

### local-project

Queries:
- `python3 -I extraction of keys, subproblem.lean_statement, natural_proof, proof_key_steps, depends_on and resolved_dependencies from nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8bcfcf93a4/parent-child-handoff.json`
- `python3 -I scan of dag.json: children of ...cone_class-a1; lean_statement of dimred_im_mass_measure and idtp_fons_cc_ambient_calculus; statements containing 'MonotoneOn' with 'Real.exp' or '1 ≤ θ', 'limsup' with 'unitBallVolume', 'univ = 0 ∨' or 'univ = ∞'; lean_name collisions for idtp_fons_cc_mb_* and '_mb_'`
- `rg -n 'idtp_fons_cc_mb_|monotone_lower_bound|mass_dichotomy' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib .lake/packages/simongmt (no match)`
- `grep -rn 'theorem measure_null_of_locally_null|theorem ofReal_div_of_pos|theorem Tendsto.limsup_eq|theorem toReal_ofReal |one_le_ofReal|protected theorem Tendsto.mul |protected theorem Tendsto.const_mul|theorem ofReal_mul |theorem mul_div_mul_left|theorem measure_ball_pos|theorem measure_ball_lt_top|theorem tendsto_ofReal_atTop|theorem tendsto_pow_atTop |theorem le_of_tendsto |instance nhdsGT_neBot|theorem mul_top |Ico_mem_nhdsLT|lemma nhdsWithin_univ|theorem ball_mem_nhds|theorem exp_neg' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; grep -n 'def unitBallVolume|def HasMassDensity|def IMRep.measure' project/GMT/Ch07/Contract.lean`
- `git show 01ae2c59 -- GMT/Ch07/Submission.lean (declaration form `theorem Submission.X` inside namespace GMT.Ch07)`
- `sed -n 300,335p and 420,472p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt (Simon 7.3.1 and proof of 7.3.3)`
- `lake env lean /tmp/mb_split_k3x9/Types.lean, Children.lean, Assembly.lean, Assembly2.lean and final/Check.lean (generated by final/gen_check.py from final/subs.json and dag.json), with #print axioms`
- `sed -n 1388,1470p and 6512,6590p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (max_depth gate, _dependency_problem, _existing_lean_name_problem, _topological), plus a replay of the key, name and dependency checks`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8bcfcf93a4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Ring.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/mb_split_k3x9/final/subs.json`
- `/tmp/mb_split_k3x9/final/gen_check.py`
- `/tmp/mb_split_k3x9/final/Check.lean`
- `/tmp/mb_split_k3x9/Children.lean`
- `/tmp/mb_split_k3x9/Assembly2.lean`

Pins match: manifest project b4d606db1 = workspace HEAD; Mathlib 25730c7c = .lake/packages/mathlib HEAD. The snapshot Contract.lean is byte-identical to GMT/Ch07/Submission.lean; it defines unitBallVolume n = volume (ball (0 : Euclid n) 1) at :143, HasMassDensity at :147 and IMRep.measure at :88.

No accepted DAG node or library declaration states either child. The nearest node, idtp_cse_massOn_ball_lower_bound, covers only n = 2, is unaccepted and sits in another branch. The names idtp_fons_cc_mb_* occur nowhere. Accepted candidates are declared as `theorem Submission.X` inside namespace GMT.Ch07.

Snapshot lemmas used in the child proofs:
- measure_null_of_locally_null (MeasureTheory/OuterMeasure/Basic.lean:150), measure_mono (:51)
- ENNReal.Tendsto.mul (Topology/Instances/ENNReal/Lemmas.lean:337), ENNReal.Tendsto.const_mul (:354), ENNReal.tendsto_ofReal_atTop (:160)
- ENNReal.mul_div_mul_left (Basic/ENNReal/Inv.lean:264), ENNReal.ofReal_div_of_pos (Inv.lean:960)
- ENNReal.one_le_ofReal (Basic/ENNReal/Real.lean:216), ENNReal.ofReal_mul (Real.lean:297)
- ENNReal.toReal_ofReal (Basic/ENNReal/Basic.lean:252), ENNReal.mul_top (Operations.lean:187)
- Filter.Tendsto.limsup_eq (Topology/Order/LiminfLimsup.lean:190), used in the parent's inline B3
- le_of_tendsto (Topology/Order/OrderClosed.lean:133); Ioc_mem_nhdsGT is the @[to_dual] of Ico_mem_nhdsLT (OrderClosed.lean:311)
- nhdsGT_neBot (Topology/Order/DenselyOrdered.lean:222)
- measure_ball_pos (Measure/OpenPos.lean:212), measure_ball_lt_top (Typeclasses/Finite.lean:373)
- tendsto_pow_atTop (Order/Filter/AtTopBot/Ring.lean:36), nhdsWithin_univ (Topology/NhdsWithin.lean:77), ball_mem_nhds (MetricSpace/Pseudo/Defs.lean:839), Real.exp_neg (Analysis/Complex/Exponential.lean:240)

Lean results:
- Both child types elaborate, and both children are fully proved using only the standard axioms.
- The parent's frozen type compiles from the two children plus the frozen types of dimred_im_mass_measure and idtp_fons_cc_ambient_calculus (as axioms).
- The runtime's max_depth gate allows depth 5 to split. Key, name, dependency and cycle checks pass, with no cross-branch name collisions.
