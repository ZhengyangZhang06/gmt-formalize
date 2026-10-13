# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1.mollified_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 1 of the parent's supplied proof ('Each v_{m,k} is continuous … Dominated convergence gives v_{m,k}(y_n) → v_{m,k}(y)'). The support radius 1 of ρ_m is replaced by a radius r of the compact support of a general ρ, and no measurability of F is assumed. It is the continuity of mollifications used in the proof of Simon, Ch. 2, Theorem 2.6 (chapter-02.txt lines 598–620; mollification argument of [GT01, Thm 7.22]).

Notation.
- ν := L^N⌞F, the restriction of L^N to F. For every set F this is a Borel measure, and ν(A) ≤ L^N(A) for every A.
- v(y) := ∫_F ρ(y − z) dz = ∫ ρ(y − z) dν(z).

1. (Bounds on ρ.) ρ is continuous and tsupport ρ is compact, so ρ is bounded: M := sup_w |ρ(w)| < ∞. Also tsupport ρ is bounded, so there is r ≥ 0 with tsupport ρ ⊆ B̄_r(0). Hence ρ(w) = 0 whenever |w| > r.

2. (Local finiteness.) For every bounded Borel set A, ν(A) ≤ L^N(A) < ∞.

3. (Reduction to sequences.) ℝ^N is a metric space, so it suffices to show v(y_n) → v(y) for every y ∈ ℝ^N and every sequence y_n → y. Fix such y and (y_n). Since y_n → y, there is n₀ with |y_n − y| ≤ 1 for all n ≥ n₀. Discard the finitely many terms before n₀; this does not affect convergence. So assume |y_n − y| ≤ 1 for all n.

4. (Hypotheses of dominated convergence.)
 (a) For each n, z ↦ ρ(y_n − z) is continuous, hence Borel measurable.
 (b) For each z, ρ(y_n − z) → ρ(y − z), because ρ is continuous and y_n − z → y − z.
 (c) If ρ(y_n − z) ≠ 0, then |y_n − z| ≤ r by step 1, so |z| ≤ |y_n| + r ≤ |y| + 1 + r. Hence |ρ(y_n − z)| ≤ g(z) := M·1_{B̄_{|y|+1+r}(0)}(z) for all n and z.
 (d) g is ν-integrable: ∫ g dν = M·ν(B̄_{|y|+1+r}(0)) < ∞ by step 2.

5. (Conclusion.) By the dominated convergence theorem, v(y_n) = ∫ ρ(y_n − z) dν(z) → ∫ ρ(y − z) dν(z) = v(y). Since y and (y_n) were arbitrary, v is continuous. ∎

Lean pointer (Mathlib 25730c7c). v equals the convolution (fun _ ↦ (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume.restrict F] ρ, by convolution_def and 1 • ρ(y − t) = ρ(y − t). The constant 1 is locally integrable for the locally finite measure volume.restrict F (locallyIntegrable_const). So HasCompactSupport.continuous_convolution_right gives the continuity directly. A 6-line sorry-free Lean proof along this route compiled during decomposition.

## Key steps

1. ρ is bounded by M and vanishes outside B̄_r(0). ν = L^N⌞F satisfies ν(A) ≤ L^N(A) < ∞ for bounded A.
2. For y_n → y with |y_n − y| ≤ 1: ρ(y_n − ·) → ρ(y − ·) pointwise, and |ρ(y_n − z)| ≤ M·1_{B̄_{|y|+1+r}(0)}(z), which is ν-integrable.
3. Dominated convergence gives v(y_n) → v(y); sequential continuity on the metric space ℝ^N gives continuity.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; cat <snapshot>/manifest.json`
- `grep -n 'theorem continuous_convolution_right\|theorem continuous_convolution_left\|HasCompactSupport.continuous_convolution' <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean; grep -n '^theorem convolution_def\|^noncomputable def convolution' (same file)`
- `grep -n "theorem setLIntegral_mono'\|theorem lintegral_add_left'\|theorem lintegral_add_right'\|theorem setLIntegral_const \|theorem lintegral_indicator_one₀\|theorem lintegral_indicator_one \|theorem setLIntegral_mono_ae" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `grep -rn 'protected theorem symmDiff' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean; grep -n "theorem restrict_apply'\|theorem restrict_apply \|theorem restrict_apply₀" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `grep -rn 'theorem integral_sub_left_eq_self\|theorem lintegral_lintegral_swap\|theorem ofReal_integral_eq_lintegral_ofReal\|theorem integral_indicator \|theorem setIntegral_congr_set\|theorem indicator_ae_eq_of_ae_eq_set\|theorem toMeasurable_ae_eq\|theorem preimage_ae_eq\|theorem lintegral_const_mul \|theorem lintegral_mul_const \|theorem locallyIntegrable_const\|theorem lintegral_congr_ae\|theorem ae_eq_set_symmDiff\|theorem norm_integral_le_integral_norm' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'theorem integral_div_left_eq_self\|theorem measurePreserving_mul_right' <snapshot>/mathlib/Mathlib/MeasureTheory (to_additive sources of integral_sub_left_eq_self, measurePreserving_add_right)`
- `grep -n 'IsLocallyFiniteMeasure (μ.restrict' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean; grep -n 'theorem ae_eq_set_inter' <snapshot>/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean; grep -rn 'indicator_of_notMem' <snapshot>/mathlib/Mathlib/Algebra; grep -rn 'theorem Continuous.integrable_of_hasCompactSupport' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem continuous_convolution_right|theorem integral_sub_left_eq_self|...' <snapshot>/mathlib/Mathlib (timed out after 2 min; replaced by the targeted greps above)`
- `grep -rn -i 'mollif\|convolution\|continuous_convolution\|translat' .lake/packages/simongmt/Poincare/SimonGMT --include=*.lean | grep -i 'theorem\|lemma\|def '`
- `python3 -I scope.py GMT/Ch03/Contract.lean (importlib of verifier/gmt-compare.py; contract_scope(text, 'GMT.Ch03.main_theorem'))`
- `python3 -I validate.py stmtA.txt stmtB.txt (importlib of verifier/lean_contract.py; validate_lean_statement)`
- `lake env lean /tmp/mollcauchy-decomp/lean/Challenge_A.lean; Challenge_B.lean; Assembly.lean; ChildProofs.lean; FullCheck.lean; FullCheck2.lean (#print axioms)`
- `python3 -I lean_name/statement collision check over dag.json (168, later 185 nodes); grep -rho "indCompact_[A-Za-z0-9_']*" nodes dag.json issue-workers.json; grep -rl indCompact_mollCauchy nodes issue-workers.json`
- `git show <de-giorgi branches>:GMT/Ch03/Submission.lean | grep -n 'theorem Submission\.' (child declaration convention inside namespace GMT.Ch03)`
- `sed -n 590,632p book/chapter-02.txt; grep -n '2.6 Theorem (Compactness\|GT01, The\|orem 7.22' book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/mollcauchy-decomp/lean/Challenge_A.lean`
- `/tmp/mollcauchy-decomp/lean/Challenge_B.lean`
- `/tmp/mollcauchy-decomp/lean/Assembly.lean`
- `/tmp/mollcauchy-decomp/lean/ChildProofs.lean`
- `/tmp/mollcauchy-decomp/lean/FullCheck2.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c).

What the libraries lack:
- Neither Mathlib nor SimonGMT has an L¹ mollification-error bound derived from translation estimates.
- Neither has a continuity lemma for y ↦ ∫_F ρ(y − z) dz.
- The SimonGMT grep matches only the Chapter08 constancyMollifier and convolution-derivative lemmas.
So both facts become children.

Mathlib provides everything needed to prove them:
- HasCompactSupport.continuous_convolution_right (Convolution.lean:640) with convolution_def, locallyIntegrable_const, and the IsLocallyFiniteMeasure instance for μ.restrict s (Finite.lean:336).
- toMeasurable_ae_eq, setIntegral_congr_set, indicator_ae_eq_of_ae_eq_set, QuasiMeasurePreserving.preimage_ae_eq, ae_eq_set_inter and ae_eq_set_symmDiff.
- integral_indicator, integral_sub_left_eq_self (to_additive of integral_div_left_eq_self), ofReal_integral_eq_lintegral_ofReal and lintegral_lintegral_swap.
- lintegral_const_mul and lintegral_mul_const, lintegral_indicator_one and lintegral_indicator_one₀, Measure.restrict_apply and restrict_apply', NullMeasurableSet.symmDiff, setLIntegral_mono', lintegral_add_left' and lintegral_add_right', setLIntegral_const, and Continuous.integrable_of_hasCompactSupport.

Lean results:
- Both child types elaborate in the exact NodeChallenge scope and pass validate_lean_statement.
- The parent's frozen type is proved from the child stubs with no extra imports.
- Complete proofs of both children compile.
- The combined file proves A, B and the parent through comparator-style `exact Submission.X` targets, with axioms propext, Classical.choice and Quot.sound only.
- Neither lean_name collides with dag.json (185 nodes) or with GMT/.
