# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.first_variation_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 4, 2.2 and Ch. 2, 5.2–5.3 (the area formula expresses the mass of φ_{t#} as ∫ θJ^Mφ_t and J^Mφ_t = 1 + t div_M X + o(t)); this is the differentiation step C2d of the parent proof, in the one-sided form that suffices for minimality; it is used through the sibling stationary_of_minimizing. Write CB for the sibling covector_gram_bounds (Submission.covectorEuclideanNorm_gram_bounds) and TM for the sibling tangent_projection_measurable (Submission.imrep_approxTangent_starProjection_aesm). Notation: K := tsupport X ⊆ W, Q(x) := approxTangentPlane n M x, p(x) its projection, div_M X(x) := tangentialDivergence n M X x = trace(p(x)DX(x)), m := (R.measure W).toReal = ∫_{M∩W} θ dH^n, A := sup_x ‖DX(x)‖ < ∞, and R.firstVariation X = ∫_M θ div_M X dH^n.
1. Good points. For H^n-a.e. x ∈ M there are an orthonormal basis τ = (τ_1, …, τ_n) of an approximate tangent plane and s = ±1 with ξ(x)(β) = s·β(τ) for all n-covectors β (R.orients); by uniqueness that plane is Q(x), and then div_M X(x) = Σ_a τ_a·DX(x)τ_a (trace of p(x)DX(x) computed in an orthonormal basis of ℝ^P adapted to Q(x)).
2. Jacobian inequality. For a linear map L and orthonormal τ_1, …, τ_n let G := (Lτ_a·Lτ_b)_{a,b}, a positive semidefinite matrix. If λ_1, …, λ_n ≥ 0 are its eigenvalues then det G = Πλ_a ≤ Π e^{λ_a − 1} = exp(tr G − n) (as λ ≤ e^{λ−1}), and tr G = Σ_a |Lτ_a|². Take L = I + tDX(x) + E with ‖E‖ ≤ η|t|, η ≤ 1, |t| ≤ 1. Then |Lτ_a|² = 1 + 2tτ_a·DX(x)τ_a + 2τ_a·Eτ_a + |tDX(x)τ_a + Eτ_a|² ≤ 1 + 2tτ_a·DX(x)τ_a + 2η|t| + (A + 1)²t², so (det G)^{1/2} ≤ exp(σ) with σ := t·div + nη|t| + n(A+1)²t²/2, where div := Σ_a τ_a·DX(x)τ_a. Put c_0 := (n + 1)(A + 2 + (A+1)²) > 0. Then |σ| ≤ |t|c_0 ≤ 1 for |t| ≤ 1/c_0, and e^σ ≤ 1 + σ + σ² for |σ| ≤ 1, so: (det G)^{1/2} ≤ 1 + t·div + |t|(nη + n(A+1)²|t|/2 + c_0²|t|). Hence, given ε' > 0, choosing η := min(1, ε'/(2n + 1)) and then |t| small, (det G)^{1/2} ≤ 1 + t·div + ε'|t| uniformly in x and τ. (For n = 0 both sides reduce to det of the empty matrix, 1 ≤ 1 + ε'|t|.)
3. Choice of δ. Given ε > 0 put ε' := ε/(m + 1), η as in step 2, and choose δ ∈ (0, 1] with δ ≤ δ(η) from the hypothesis, δ ≤ 1/c_0, δ·(n(A+1)²/2 + c_0²) ≤ ε'/2 and δ·(nA + ε') ≤ 1, so that step 2 yields (det G)^{1/2} ≤ 1 + t·div + ε'|t| for |t| < δ (and 1 + t·div_M X + ε'|t| ≥ 0).
4. Pointwise bound. Fix |t| < δ, S as in the statement and an admissible ω (ω ∈ 𝒟^n(U), tsupport ω ⊆ W, |ω(y)|_E ≤ 1 for all y). Let g(x) := θ(x)ξ(x)(ω(φ_t x)∘Dφ_t(x)), so S(ω) = ∫_M g dH^n. At a good point x ∈ M ∩ W: g(x) = sθ(x)·ω(φ_t x)(Dφ_t(x)τ_1, …, Dφ_t(x)τ_n), so by CB(1) and step 2 (with L = Dφ_t(x), E := Dφ_t(x) − I − tDX(x), ‖E‖ ≤ η|t|): |g(x)| ≤ θ(x)·|ω(φ_t x)|_E·(det G)^{1/2} ≤ θ(x)(1 + t·div_M X(x) + ε'|t|). At a good point x ∈ M ∖ W: x ∉ K, so φ_t(x) = x ∉ W ⊇ tsupport ω and g(x) = 0. Hence g ≤ h a.e. on M, where h := 1_W·θ·(1 + t·div_M X + ε'|t|).
5. Integration. g is a.e. strongly measurable (θ measurable, ξ a.e. strongly measurable, x ↦ ω(φ_t x) continuous, x ↦ fderiv ℝ (φ_t) x measurable by Mathlib measurable_fderiv) and |g| ≤ θ·1_W·(1 + |t|(nA + ε')), which is integrable because ∫_{M∩W} θ = m < ∞; h is integrable because div_M X is H^n⌞M-a.e. strongly measurable (TM: it is the trace of p(x)∘DX(x), a continuous function of (p(x), DX(x))) and bounded by nA. Therefore S(ω) ≤ ∫_M h dH^n = m + t∫_{M∩W} θ div_M X dH^n + ε'|t|m. Since DX(x) = 0 on the open set ℝ^P ∖ K, div_M X vanishes off K ⊆ W, so ∫_{M∩W} θ div_M X = R.firstVariation X. With ε'm ≤ ε: S(ω) ≤ m + t·R.firstVariation X + ε|t|.
6. Conclusion. ofReal is monotone, so ofReal(S ω) ≤ ofReal(m + t·R.firstVariation X + ε|t|) for every admissible ω, and taking the supremum, S.massOn W ≤ ENNReal.ofReal((R.measure W).toReal + t·R.firstVariation X + ε|t|).

## Key steps

1. CB(1) bounds the integrand by θ·|ω|_E·(det Gram(Dφ_tτ))^{1/2}.
2. det G ≤ exp(tr G − n) and the expansion Dφ_t = I + tDX + o(t) give (det G)^{1/2} ≤ 1 + t div_M X + ε'|t| uniformly.
3. φ_t = id off spt X ⊆ W kills the integrand off W; integrate (measurability from TM) and take the supremum over admissible forms.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IMRep, IMRep.measure, IsMinimizingIn, HasMassDensity, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, regularSet, approxTangentPlane, IMRep.firstVariation, IMRep.IsStationaryAlong, MinimizingImpliesStationary, DensityOneImpliesRegular)`
- `sed -n 1,40p simongmt/Poincare/SimonGMT/Chapter05/Basic.lean; grep -rln -i allard simongmt/Poincare/SimonGMT; grep -rn 'theorem.*stationary|def .*Stationary' simongmt/Poincare/SimonGMT; ls simongmt/Poincare/SimonGMT/{Chapter04,Chapter06,Chapter07}`
- `python3 -I scans of dag.json (2026-10-13T04:47Z to 05:01Z): status, candidate_commit, depends_on, children and frozen lean_statement of the 8 reused and 4 mirrored declarations; accepted-checkpoint predicate per node; unaccepted descendants of the allard_graph, diffeo_pushforward and first_variation_mass_bound subtrees`
- `python3 -I: compare nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/decomposition-v1.json subproblems with the 12 original parent-child-handoff.json files (statement, title, key steps; natural_proof diff; audit.acceptable and natural_proof_acceptable)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def _solve_children|def _install_parent_supplied_child_handoff' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; sed -n 60,260p store.py (refresh, update); class RefreshLock in parallel.py; def merge_nodes in shared_dag.py; diff of store.py and shared_dag.py between flows d253855dab51 and b888e19cffb1 (identical)`
- `ps -eo pid,ppid,lstart,args (controller pid 38505 run-workflow.py with swarm config 5354b742..., issue 4368; this session spawned 04:46:13); stat dag.json and decomposition-v1.json; ls -la --time-style=full-iso nodes/root-minimizing-implies-stationary-a1-tangential-deformation-a1`
- `grep -c NAME dag.json; grep -rl NAME GMT simongmt/Poincare local-references/123e8435b4a2469b/{project,mathlib/Mathlib} for the 4 codim1_ldr_ names; git for-each-ref refs/heads refs/remotes (2681 refs) | xargs -n 200 git grep -l codim1_ldr -- 'GMT/*.lean' (no match)`
- `lean -DautoImplicit=false /tmp/ldr-v2/Types.lean; lean -DautoImplicit=false /tmp/ldr-v2/Assembly.lean; lean -DautoImplicit=false /tmp/ldr-v2/AssemblyC.lean (LEAN_PATH from .lake/build/lib/lean/GMT/Ch07/Submission.trace); python3 -I check that each child lean_statement occurs verbatim in Types.lean and equals the DAG frozen type`
- `sed -n 605,632p and 670,676p book/sources/chapter-07-source.txt; sed -n 1008,1031p book/sources/chapter-05-source.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangent-projection-measurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangential-deformation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-stationary-of-minimizing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parallel.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/shared_dag.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/5354b74280214eb69162b9250d4053da.json`
- `/tmp/ldr-v2/Types.lean`
- `/tmp/ldr-v2/Assembly.lean`
- `/tmp/ldr-v2/AssemblyC.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt.
- The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter05/Basic.lean states that the compactness, Lipschitz approximation, excess-decay and Allard regularity theorems are not provided, and no Chapter07 module exists.
- Chapter04 has stationary-varifold density and monotonicity lemmas, but nothing on stationarity of minimizing currents. The snapshot Mathlib has no GMT regularity theory.
- So Allard, Simon 7.1.2 and the C¹ push-forward of integer multiplicity currents stay as children, cited from the book (Simon 7.4.2–7.4.4: chapter-07-source.txt lines 605–632 and 670–676; Ch. 5, 5.1–5.2: chapter-05-source.txt lines 1008–1031).
DAG.
- The 8 reused declarations are accepted with candidate commits and byte-identical types.
- The 4 mirrored originals are still speculative-ready under other parents, so they get fresh codim1_ldr_ names with byte-identical types.
- The supplied child proofs equal the original handoff proofs (statements, titles and key steps identical; every original audit acceptable), except for the role line and sibling names.
- The 4 new names are free in dag.json, GMT/, SimonGMT, the snapshot Mathlib and all 2681 git refs.
Runtime. The attempt-1 rejection of tangential_c1_deformation_exists came from a DAG snapshot older than its acceptance (04:24:57Z). Store.refresh merges the disk state on every update; the controller (pid 38505, issue 4368) refreshed at 04:46:13Z, so the accepted status is now visible to the name check.
Lean.
- Types.lean elaborates all 12 child types and the parent type (exit 0, only sorry warnings); each lean_statement matches the DAG verbatim.
- Assembly.lean proves the exact parent type from the six directly used child types (exit 0).
- AssemblyC.lean proves the stationary_of_minimizing type from its four sibling types (exit 0).
- Both depend only on propext, Classical.choice and Quot.sound.
