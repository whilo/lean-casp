# Comparing Lean with both SWI engines

The shared driver generates one source fixture for all engines. It checks 32
whole-program brave verdicts and eleven open queries, including five that read the checked-in Prolog tutorial clauses. The archived results.csv predates the five tutorial queries. For open queries SWI first
solves with free variables, then the harness projects each answer onto the
finite Lean domain and compares the complete set of tuples. This preserves
the distinction between one jointly possible binding and two individually
possible bindings. Lean also checks every comparison against its exhaustive
grounding oracle. Exceptions, timeouts and missing outputs fail the run.

## Reproduce

Use SWI-Prolog 10.0.1 and the following s(CASP) revision. Install SWI in
any local prefix. The measured run used the release source tarball with
SHA-256 `a9504745310e36195cf8cee9ad9164a7aa99e389c669ca6d279e321efc2ad9d4`.
The SWI executable needs its usual bundled packages, including CLP(Q) and
HTTP JSON. From the Lean project root:

```sh
git clone https://github.com/SWI-Prolog/sCASP /tmp/scasp-reference
git -C /tmp/scasp-reference checkout ebfa1708f6edf2adadaf752f459a0afff473fdfb
lake build caspCompare
python3 comparison/run.py --swipl /path/to/swipl --scasp /tmp/scasp-reference
```

The driver verifies the SWI version and reference commit. Source templates
are adapted from the upstream differential, constructive-negation and
`forall_over_facts` tests. They also cover a deterministic 32-step chain,
connected choices, an unrelated inconsistent component, and a rule with
two body-local variables.

## Reading the CSV

All timing columns are nanoseconds. Each solver prepares each ground fixture
seven times and runs an untimed query before the timed query. The output gives
the medians of preparation and warm time to the first verdict. Lean prepares a
query-specific ground slice; SWI compiles the source program. Classic SWI's
file interface includes reading the file in preparation. SWI materializes a
partial answer, and Lean checks a model of its slice. These routines perform
different amounts of work even when their verdicts agree.

For successful ground queries, `kernel_ns` is the median of five calls to
Lean's declaration checker on a proof using a full-grounding witness.
Importing the environment, constructing the witness, and quoting it are
outside that timer. Unsuccessful queries have no witness replay time.
Open-query rows report distinct projected bindings. The separate command
`lake exe caspBench` includes the selective reachability workload.

## Additional upstream suites

Run these commands from the pinned SWI checkout, with SWI 10.0.1 on PATH:

```sh
swipl -p library=prolog -s test/test_differential.pl -g test_differential -t halt
swipl -p library=prolog -s test/test_forall.pl -s test/test_clpq.pl \
  -g 'test_forall:test_forall,test_clpq:test_clpq' -t halt
swipl -Dsscasp -Dscasp_expect=semantics -p library=prolog -s test/test_differential.pl \
  -g test_differential -t halt
swipl -Dsscasp -p library=prolog -s test/test_forall.pl -s test/test_clpq.pl \
  -s test/sscasp/test_crossings.pl \
  -g 'test_forall:test_forall,test_clpq:test_clpq,test_crossings:test_crossings' -t halt
```

The upstream differential suite selects its expected behavior for an undefined
top-level predicate using `scasp_expect`. Classic SWI raises an exception in
the documented case; the newer engine answers according to the stable-model
semantics. The native CLP(Q) suites exercise capabilities beyond the common
finite fragment. The shared driver compares finite bindings and ground verdicts.
