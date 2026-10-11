# gmt-formalize

Lean 4 formalization of Leon Simon, *Introduction to Geometric Measure Theory* (2014 Tsinghua
lecture notes), run as eight independent problems, one per chapter.

Each chapter has a frozen contract `GMT/ChNN/Contract.lean`: faithful definitions plus one theorem
`GMT.ChNN.main_theorem`, the conjunction of the chapter's headline results. The prover completes
`GMT/ChNN/Submission.lean`; a solution is accepted only when an exact comparator confirms the same
statement and definitions, a kernel replay succeeds, and no axioms beyond `propext`, `Quot.sound` and
`Classical.choice` are used. `GMT/ChNN/README.md` maps every conjunct to the book.

| Chapter | Problem | Book pages |
| --- | --- | --- |
| 1 | [Preliminary Measure Theory](GMT/Ch01) | 1–38 |
| 2 | [Some Further Preliminaries from Analysis](GMT/Ch02) | 39–68 |
| 3 | [Countably n-Rectifiable Sets](GMT/Ch03) | 69–84 |
| 4 | [Rectifiable n-Varifolds](GMT/Ch04) | 85–102 |
| 5 | [The Allard Regularity Theorem](GMT/Ch05) | 103–130 |
| 6 | [Currents](GMT/Ch06) | 131–180 |
| 7 | [Area Minimizing Currents](GMT/Ch07) | 181–204 |
| 8 | [Theory of General Varifolds](GMT/Ch08) | 205–224 |

## How the proofs are produced

The [humanize theorem workflow](https://github.com/humanfia/math-lean-flow/tree/feature/humanize-api-update-claude)
works through GitHub issues and pull requests in this repository. Every chapter starts from a root
issue; each accepted decomposition opens one issue per sub-theorem, and every proved node gets its
own solution PR. Workers poll open issues autonomously on a Docker Swarm fleet.

- Prover: Claude Opus 5.5 (`max` effort). Reviewer: Codex `gpt-6-astra` (`max`).
- Natural-language proofs and decompositions are reviewed independently before any Lean work.
- Each chapter's base branch is `problems/chNN`; root solutions merge into it.

## Build

Lean `v4.35.0-rc3`, Mathlib `25730c7c`, and the `simongmt` package pinned on this repository's
[`simongmt-library`](https://github.com/ZhengyangZhang06/gmt-formalize/tree/simongmt-library) branch:
an earlier, partial formalization of the same book whose kernel-checked lemmas the prover may reuse.

```sh
lake exe cache get   # Mathlib oleans
lake env lean GMT/Ch01/Contract.lean
```
