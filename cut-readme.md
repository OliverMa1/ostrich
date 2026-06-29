# Cut Traces and Experimental Cut Picking

This note describes the diagnostic final-cut trace and the hook for trying a
custom cut picker. Both features are off by default.

## Printing the cut trace

Build the assembly jar:

```sh
sbt assembly
```

Run OSTRICH with `+cutTrace` in the string-solver parameter list:

```sh
java -Xss20000k -Xmx2000m \
  -cp target/scala-2.11/ostrich-assembly-2.1.jar \
  ostrich.OstrichMain \
  -stringSolver=ostrich.OstrichStringTheory:+cutTrace \
  -timeout=30000 path/to/benchmark.smt2
```

The trace is printed to stderr at the final cut rule. It shows the semantic
goal before the cut: arithmetic constraints, string/function constraints,
regular-language domains, available cut variables, the chosen proposal, and a
compact line for each actual cut.

Use `-cutTraceLimit=N` to bound the number of full pre-cut blocks:

```sh
java -Xss20000k -Xmx2000m \
  -cp target/scala-2.11/ostrich-assembly-2.1.jar \
  ostrich.OstrichMain \
  -stringSolver=ostrich.OstrichStringTheory:+cutTrace,-cutTraceLimit=3 \
  -timeout=30000 path/to/benchmark.smt2
```

For benchmarks that do not reach the final cut rule under the default
propagation setup, it can be useful to compare with selected propagation rules
disabled:

```sh
java -Xss20000k -Xmx2000m \
  -cp target/scala-2.11/ostrich-assembly-2.1.jar \
  ostrich.OstrichMain \
  -stringSolver=ostrich.OstrichStringTheory:+cutTrace,-cutTraceLimit=3,-nielsenSplitter,-forwardPropagation,-backwardPropagation \
  -timeout=30000 path/to/benchmark.smt2
```

## Adding a custom cut picker

The hook is in:

```text
src/main/scala/ostrich/proofops/OstrichCut.scala
```

Look for:

```scala
private def chooseExperimentalCut(
  goal: Goal,
  stringVariables: IndexedSeq[ConstantTerm]
): Option[CutProposal]
```

Enable this hook with `+experimentalCutPicker`:

```sh
java -Xss20000k -Xmx2000m \
  -cp target/scala-2.11/ostrich-assembly-2.1.jar \
  ostrich.OstrichMain \
  -stringSolver=ostrich.OstrichStringTheory:+cutTrace,+experimentalCutPicker,-cutTraceLimit=3 \
  -timeout=30000 path/to/benchmark.smt2
```

The picker should return a proposal, not proof actions:

```scala
CutProposal(
  variable = someStringVariable,
  preferredWord = Some(Seq('V'.toInt)),
  method = "my-picker",
  details = "short diagnostic note"
)
```

Use `preferredWord = None` when the picker only chooses the variable and wants
OSTRICH to keep the legacy accepted-word enumeration.

The soundness boundary is `cutForProposal`/`cutForWord` in `OstrichCut.scala`.
If a proposal contains a concrete word, OSTRICH validates it against the current
regular constraints and length facts before using it. The proof step remains
the exhaustive split `x = w` versus `x` in the complement of `{w}`; the picker
only changes which split is tried next.
