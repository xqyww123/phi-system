#!/usr/bin/env python3
"""Compare ledger_dump.pre.txt / ledger_dump.post.txt per
DEBT_AXIOM_POLY_SUPPORT_PLAN.md section 8.3-1.

Acceptance:
- per LEDGER ENTRY: byte-identical proposition (prop_ml is the byte-exact
  witness) AND unchanged maxidx; prop_pretty must ALSO be byte-identical
  after normalizing the two session-local serial families inside PIDE YXML
  markup (entity ref=<serial> and def_id=<serial>) -- a second, rendering-
  level acceptance witness (review proposal R6);
- per DEBT FACT: prop_ml/tags/shyps/hyps_count equal AND either
  maxidx_post == maxidx_pre (the observed zero-deviation case) or
  maxidx_post == max(0, maxidx_pre) (the plan-formula-allowed chain-level
  flip); the verdict reports which case fired.
"""
import sys, re

SERIALS = re.compile(r"\b(ref|def_id)=\d+")

def normalize_pretty(s):
    return SERIALS.sub(r"\1=*", s)

FIELD = re.compile(r"^(ENTRY: |LEDGER (?:prop_ml|prop_pretty|maxidx): |FACT\[\d+\] (?:prop_ml|prop_pretty|maxidx|tags|shyps|hyps_count): |FACT: NONE$|DEBT COUNT: )")

def parse(path):
    entries = {}
    cur = None          # current entry name
    curfield = None     # (dict, key) receiving continuation lines
    count = None
    with open(path, encoding="utf-8", errors="surrogateescape") as f:
        for raw in f.read().split("\n"):
            m = FIELD.match(raw)
            if not m:
                if curfield is not None:      # continuation of a wrapped field
                    d, k = curfield
                    d[k] += "\n" + raw
                continue
            head = m.group(0)
            rest = raw[len(head):]
            if head == "DEBT COUNT: ":
                count = int(rest); curfield = None
            elif head == "ENTRY: ":
                cur = rest
                entries[cur] = {"facts": []}
                curfield = None
            elif head.startswith("LEDGER "):
                key = head[len("LEDGER "):-2]
                entries[cur][key] = rest
                curfield = (entries[cur], key)
            elif head == "FACT: NONE":
                entries[cur]["facts"].append(None)
                curfield = None
            else:                              # FACT[i] field
                i = int(head[head.index("[")+1:head.index("]")])
                key = head[head.index("]")+2:-2]
                facts = entries[cur]["facts"]
                while len(facts) <= i:
                    facts.append({})
                facts[i][key] = rest
                curfield = (facts[i], key)
    return count, entries

def main(pre_path, post_path):
    npre, pre = parse(pre_path)
    npost, post = parse(post_path)
    problems, infos = [], []
    if npre != npost:
        problems.append(f"DEBT COUNT differs: pre={npre} post={npost}")
    if set(pre) != set(post):
        problems.append(f"entry-name sets differ: only-pre={sorted(set(pre)-set(post))} only-post={sorted(set(post)-set(pre))}")
    flips = 0
    for name in sorted(set(pre) & set(post)):
        a, b = pre[name], post[name]
        if a.get("prop_ml") != b.get("prop_ml"):
            problems.append(f"{name}: LEDGER prop_ml differs")
        if a.get("maxidx") != b.get("maxidx"):
            problems.append(f"{name}: LEDGER maxidx {a.get('maxidx')} -> {b.get('maxidx')}")
        if normalize_pretty(a.get("prop_pretty", "")) != normalize_pretty(b.get("prop_pretty", "")):
            problems.append(f"{name}: LEDGER prop_pretty differs beyond session serials")
        fa, fb = a["facts"], b["facts"]
        if len(fa) != len(fb) or [x is None for x in fa] != [x is None for x in fb]:
            problems.append(f"{name}: FACT shape differs (pre {len(fa)}, post {len(fb)})")
            continue
        for i, (x, y) in enumerate(zip(fa, fb)):
            if x is None:
                continue
            for k in ("prop_ml", "tags", "shyps", "hyps_count"):
                if x.get(k) != y.get(k):
                    problems.append(f"{name}: FACT[{i}] {k} differs:\n  pre : {x.get(k)}\n  post: {y.get(k)}")
            mi_pre = int(x.get("maxidx").replace('~', '-'))
            mi_post = int(y.get("maxidx").replace('~', '-'))
            if mi_post == mi_pre:
                pass                       # zero deviation (the observed case)
            elif mi_post == max(0, mi_pre):
                flips += 1                 # the plan-formula-allowed chain-level flip
            else:
                problems.append(f"{name}: FACT[{i}] maxidx {mi_pre} -> {mi_post}, "
                                f"outside {{{mi_pre}, {max(0, mi_pre)}}}")
            if normalize_pretty(x.get("prop_pretty", "")) != normalize_pretty(y.get("prop_pretty", "")):
                problems.append(f"{name}: FACT[{i}] prop_pretty differs beyond session serials")
    print(f"entries compared: {len(set(pre) & set(post))} (pre count {npre}, post count {npost})")
    print(f"fact maxidx flips to max(0, maxidx) (allowed by the plan formula): {flips}")
    for s in infos:
        print("INFO:", s)
    if problems:
        print(f"VERDICT: FAIL ({len(problems)} problems)")
        for s in problems:
            print("PROBLEM:", s)
        return 1
    print("VERDICT: PASS — ledger byte-identical (prop_ml AND serial-normalized "
          "prop_pretty) with unchanged maxidx; facts identical in all fields, "
          + ("with zero maxidx deviation" if flips == 0
             else f"with {flips} plan-formula-allowed maxidx flips"))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
