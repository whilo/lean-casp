"""Compare whole-program brave answers. Run from the project root after lake build caspCompare."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

PIN = "ebfa1708f6edf2adadaf752f459a0afff473fdfb"


def atom(text):
    m = re.fullmatch(r"([a-z]\w*)(?:\(([A-Za-z0-9_,]+)\))?", text.strip())
    if not m:
        raise ValueError(text)
    return {"pred": m[1], "args": m[2].split(",") if m[2] else []}


def body(text):
    pos, neg = [], []
    for literal in re.split(r",(?![^()]*\))", text) if text else []:
        literal = literal.strip()
        (neg if literal.startswith("not ") else pos).append(atom(literal.removeprefix("not ")))
    return {"pos": pos, "neg": neg}


def fixture(name, program, query):
    rules = []
    for rule in program.split(";"):
        head, _, tail = rule.partition(":-")
        rules.append({"head": atom(head) if head.strip() else None, **body(tail.strip())})
    return ({"name": name, "enumerate": False, "rules": rules, **body(query)},
            program.replace(";", ".\n") + ".\n?- " + query + ".\n")


def corpus():
    cases = []
    def add(name, source, *queries):
        for i, query in enumerate(queries):
            cases.append(fixture(f"{name}_{i+1}", source, query))

    choice = "p :- not q;q :- not p"
    add("even", choice, "p", "not p", "p,q")
    add("odd", "p :- not p", "p", "not p")
    add("defused", "p;p :- not p", "p", "not p")
    add("founded", "p :- q;q :- p;p", "q")
    add("unsupported", "p :- q;q :- p", "p", "not p")
    add("denial", choice+";:- p", "p", "q")
    add("disconnected", choice+";z :- not z", "p")
    add("chain32", "v0;"+";".join(f"v{i} :- v{i-1}" for i in range(1,33)), "v32")
    add("connected", choice+";a :- p,not b;b :- p,not a;c :- q", "a,p", "a,c")
    filtered = "q(a);q(b);r(b);p(X) :- q(X),not r(X)"
    add("filter", filtered, "p(a)", "p(b)", "not p(b)")
    fo = "dom(a);dom(b);p(X) :- dom(X),not q(X);q(X) :- dom(X),not p(X)"
    add("fo_choice", fo, "p(a),q(b)", "p(a),q(a)")
    add("fo_denial", fo+";:- p(a)", "p(a)", "p(b)")
    add("forall", "person(ann);person(bob);food(cake);food(rice);eats(ann,cake);likes(X) :- food(F),eats(X,F)",
        "likes(ann)", "not likes(ann)", "not likes(bob)")
    add("local_choice", choice+";hit(a) :- p;hit(b) :- q;blocked :- hit(Y)",
        "blocked", "not blocked")
    add("two_local", "edge(a,b);edge(b,c);bad(c);blocked(X) :- edge(X,Y),edge(Y,Z),bad(Z)",
        "not blocked(a)", "not blocked(b)")
    add("repeated", "edge(a,a);edge(a,b);same(X) :- edge(X,X)", "same(a)", "not same(b)")
    def open_case(name, source, query):
        f, program = fixture(name, source, query)
        f["enumerate"] = True
        cases.append((f, program))

    open_case("open_filter", filtered, "p(X)")
    open_case("open_choice", fo, "p(X),q(Y)")
    open_case("open_negative", "person(ann);person(bob);food(cake);food(rice);"
              "eats(ann,cake);likes(X) :- food(F),eats(X,F)", "not likes(X)")
    open_case("open_impossible", fo, "p(X),q(X)")
    open_case("open_join", "edge(a,b);edge(b,c);path(X,Z) :- edge(X,Y),edge(Y,Z)", "path(X,Z)")
    open_case("open_repeated", "edge(a,b);edge(a,a);same(X) :- edge(X,X)", "same(X)")
    return cases


def run(args, **kw):
    return subprocess.run(args, text=True, capture_output=True, check=True, timeout=120, **kw).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--swipl", required=True)
    parser.add_argument("--scasp", required=True, type=Path)
    args = parser.parse_args()
    if run([args.swipl, "--version"]).split()[2] != "10.0.1":
        parser.error("comparison expects SWI-Prolog 10.0.1")
    if run(["git", "-C", args.scasp, "rev-parse", "HEAD"]).strip() != PIN:
        parser.error("unexpected reference revision")
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        cases = corpus()
        data = folder / "fixtures.json"
        data.write_text(json.dumps([case for case, _ in cases]))
        try:
            rows = run(["lake", "env", ".lake/build/bin/caspCompare", data]).splitlines()
        except subprocess.CalledProcessError as err:
            raise RuntimeError(f"Lean comparison failed: {err.stderr}") from err
        if len(rows) != len(cases):
            raise RuntimeError("missing Lean verdicts")
        print("case,verdict,lean_prep_ns,lean_warm_ns,kernel_ns,classic_prep_ns,classic_warm_ns,new_prep_ns,new_warm_ns")
        for row, (case, program) in zip(rows, cases):
            name, verdict, *stats = row.split("\t")
            if name != case["name"]:
                raise RuntimeError(f"unexpected case {name}")
            file = folder / (name + ".pl")
            file.write_text(program)
            enumerate_rows = case.get("enumerate", False)
            domain = sorted({arg for r in case["rules"] for a in [r["head"], *r["pos"], *r["neg"]]
                             if a for arg in a["args"] if arg[0].islower()})
            for engine in ["classic", "new"]:
                try:
                    cmd = [args.swipl, "-p", "library="+str(args.scasp.resolve()/"prolog"),
                           "-s", "comparison/swi.pl", "--", engine, file]
                    if enumerate_rows:
                        actual = json.loads(run(cmd + [",".join(domain)]))
                        if sorted(actual) != sorted(json.loads(verdict)):
                            raise RuntimeError(f"{name}/{engine} bindings: {actual}; Lean: {verdict}")
                        continue
                    answer, prep, warm = run(cmd).strip().split("\t")
                except subprocess.CalledProcessError as err:
                    raise RuntimeError(f"{name}/{engine}: {err.stderr}") from err
                if answer != verdict:
                    raise RuntimeError(f"{name}/{engine} answered {answer}; Lean answered {verdict}")
                stats += [prep, warm]
            if enumerate_rows:
                print(f"{name},{len(json.loads(verdict))} bindings,,,,,,,", flush=True)
            else:
                print(",".join([name, verdict, *stats]), flush=True)


if __name__ == "__main__":
    main()
