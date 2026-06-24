# Mutate.lean — mutation testing for Lean4
Checks that your theorems constrain your `def`s. It mutates `def`/`instance`/`abbrev` bodies, re-elaborates each mutant in-process, and classifies via the compiler.

The tool requires **Lean >=4.28**. It is supposed to always support the latest version of Lean, because internally it uses the Lean compiler frontend.

## Usage
Run it from the target project's `lake` dir:
```
cd <your-lean-project>
lake env lean --run /path/to/Mutate.lean/Mutate.lean YourFile.lean
```

Output: one line per mutant `  <def>  <op>  <verdict>  <killer-theorem>`, then a summary `killed=.. survived=.. stillborn=..`. A clean run is `survived=0` (modulo provably-equivalent noise).
- **killed** — some theorem/`example` now fails to elaborate => that operator is constrained. Good.
- **stillborn** — the mutant is ill-typed. Skip.
- **survived** — everything still compiles with the mutated def => a coverage gap. Add an invariant.

## Use-cases
The main purpose of the tool is to **get extra feedback to LLMs writing specifications**.

This tool gives the model cheap, fast feedback, so the generated code is more complete before manual review. Example — proving some Move smart-contract properties:

![](./img/llm-screenshot.png)

It works great with small isolated spec files describing math algorithms.

For good-quality hand-written specs, the tool generates mostly noise, while it is still capable of highlighting some specification gaps or dead code; here is [an example finding](https://github.com/Verified-zkEVM/CompPoly/issues/248).
