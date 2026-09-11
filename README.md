# Mutate.lean — mutation testing for Lean4
Checks that your theorems constrain your `def`s. It mutates `def`/`instance`/`abbrev` bodies, re-elaborates each mutant in-process, and classifies via the compiler.

The tool requires **Lean >=4.28**. It is supposed to always support the latest version of Lean, because internally it uses the Lean compiler frontend.

## Usage
Run it from the target project's `lake` dir:
```
cd <your-lean-project>
lake env lean --run /path/to/Mutate.lean/Mutate.lean [-v] [--include-def P,..] [--exclude-def P,..] [--ops O,..] [--no-ops O,..] [--sample N] [--seed S] [--shard I/N] YourFile.lean
```

Output: one line per mutant `  <def>  <op>  <verdict>  <killer-theorem>`, then a summary `killed=.. survived=.. stillborn=..`. A clean run is `survived=0` (modulo provably-equivalent noise).
- **killed** — some theorem/`example` now fails to elaborate => that operator is constrained. Good.
- **stillborn** — the mutant is ill-typed. Skip.
- **survived** — everything still compiles with the mutated def => a coverage gap. Add an invariant.

### Options
`-v`/`--verbose` shows progress: site count, baseline time + ETA, `[i/N]`, running tally. Off by default.

`--include-def P,..` / `--exclude-def P,..` mutate only defs whose name contains one of the substrings / skip those that do. Unset by default.

`--ops O,..` / `--no-ops O,..` mutate only these operator classes / skip them. Names: the operators from the swap table plus `lit`, `ident`, `flip`, `args`, `body`. Unset by default.

`--sample N` `--seed S` mutate a deterministic random subset of N sites; the summary then says which sample it was. Off by default.

`--shard I/N` mutate only sites `i % N == I`, so N processes can run disjoint slices in parallel; concatenate their output. Off by default.

## Use-cases
The main purpose of the tool is to **get extra feedback to LLMs writing specifications**.

This tool gives the model cheap, fast feedback, so the generated code is more complete before manual review. Example — proving some Move smart-contract properties:

![](./img/llm-screenshot.png)

It works great with small isolated spec files describing math algorithms.

For good-quality hand-written specs, the tool generates mostly noise, while it is still capable of highlighting some specification gaps or dead code; here is [an example finding](https://github.com/Verified-zkEVM/CompPoly/issues/248).
