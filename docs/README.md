# lean-mend design documents

lean-mend mends a Lean 4 project after a toolchain or dependency bump. It
repairs the build by rules, checks each repair at its site, and proves that no
theorem statement and no axiom set changed.

Read the documents in this order:

| Document | What it states |
|---|---|
| [what-lean-mend-is.md](what-lean-mend-is.md) | The problem, the evidence, the scope and the acceptance test. |
| [glossary.md](glossary.md) | The vocabulary. One word for one concept. |
| [concepts.md](concepts.md) | Every design concept the program must embody, with its source. Functional core, imperative shell is one of about thirty. |
| [machine.md](machine.md) | The machine: operands, states, transitions, refusals, the one invariant and the termination measure. |
| [architecture.md](architecture.md) | The Lean layout: Spec, Core, Shell and the Probe; the version boundary; the two stores; the trust partition. |
| [rules.md](rules.md) | The repair rule language, where rules come from, and how a proposed rule becomes a ratified rule. |
| [breaking-changes.md](breaking-changes.md) | The breaking changes of Lean 4.30–4.35 with a downstream symptom, each mapped to a lean-mend rule or operation, and learnings from hopscotch and AXLE. |
| [verification.md](verification.md) | How lean-mend proves it did no harm to a target, and how lean-mend itself is verified. |
| [static-diff.md](static-diff.md) | Design, not built: predict a bump's axiom and behavior findings, and their causes, from the two toolchains' elaborated terms, before any repair runs. |
| [process.md](process.md) | The order of work, the strata and their gates, and stage 0. |
| [decisions.md](decisions.md) | The decisions taken, with reasons, and the open questions. |

All prose follows ASD-STE100 Simplified Technical English.
