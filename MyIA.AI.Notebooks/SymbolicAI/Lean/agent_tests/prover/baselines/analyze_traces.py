#!/usr/bin/env python3
"""Forensic analysis of multi-agent Lean prover traces (Epic #1453)."""

import json
import os
import glob
import re
from collections import defaultdict, Counter
import hashlib
import statistics

TRACE_DIR = os.path.join(os.path.dirname(__file__), "traces")

jsonl_files = sorted(glob.glob(os.path.join(TRACE_DIR, "*.spans.jsonl")))

def extract_target(filename):
    base = filename.replace(".spans.jsonl", "")
    for prefix in ["auto_", "multi_", "custom_"]:
        if base.startswith(prefix):
            base = base[len(prefix):]
            break
    base = re.sub(r'_(zai|local|openrouter)_[\d]+$', '', base)
    base = re.sub(r'_(zai|local|openrouter)$', '', base)
    return base

def parse_all_spans():
    all_spans = []
    for fpath in jsonl_files:
        fname = os.path.basename(fpath)
        target = extract_target(fname)
        with open(fpath, "r", encoding="utf-8") as f:
            for line_no, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    span = json.loads(line)
                    span["_file"] = fname
                    span["_line"] = line_no
                    span["_target"] = target
                    all_spans.append(span)
                except json.JSONDecodeError:
                    pass
    return all_spans

all_spans = parse_all_spans()
print(f"Total spans: {len(all_spans)}, Files: {len(jsonl_files)}")

# ===== 1. ERROR RATE BY TARGET =====
print("\n" + "="*80)
print("1. ERROR RATE BY TARGET")
print("="*80)

target_status = defaultdict(lambda: {"ERROR": 0, "UNSET": 0, "total": 0})
for s in all_spans:
    st = s.get("status", "UNSET")
    if st not in ("ERROR",):
        st = "UNSET"
    target_status[s["_target"]][st] += 1
    target_status[s["_target"]]["total"] += 1

print(f"\n{'Target':<45} {'Total':>6} {'ERROR':>6} {'Err%':>6}")
print("-"*65)
for target in sorted(target_status.keys(), key=lambda t: target_status[t]["ERROR"]/max(1,target_status[t]["total"]), reverse=True):
    d = target_status[target]
    err_pct = d["ERROR"] / d["total"] * 100 if d["total"] > 0 else 0
    print(f"{target:<45} {d['total']:>6} {d['ERROR']:>6} {err_pct:>5.1f}%")

# ===== 2. DURATION STATS =====
print("\n" + "="*80)
print("2. DURATION STATS BY AGENT/TOOL")
print("="*80)

name_durations = defaultdict(list)
for s in all_spans:
    dur = s.get("duration_ms")
    if dur is not None and dur >= 0:
        name = s.get("name", "UNKNOWN")
        name_durations[name].append(dur)

# Focus on the important ones
important_names = [
    "proof_session.auto-zai", "proof_session.multi", "workflow.run",
    "invoke_agent TacticAgent", "invoke_agent CoordinatorAgent", "invoke_agent AutonomousProver",
    "invoke_agent SearchAgent", "invoke_agent CriticAgent", "invoke_agent DirectorAgent",
    "chat glm-5.1", "chat gpt-5.5", "chat qwen3.6-35b-a3b", "chat anthropic/claude-sonnet-4-6",
    "execute_tool compile_probe_goal", "execute_tool file_replace_sorry",
    "execute_tool file_replace_lines", "execute_tool file_read_lines",
    "execute_tool search_mathlib_lemmas", "execute_tool compile",
    "executor.process verify_executor",
]

print(f"\n{'Span Type':<55} {'Count':>6} {'Median':>10} {'P95':>10} {'Max':>10}")
print("-"*95)
for name in important_names:
    if name not in name_durations:
        continue
    durs = sorted(name_durations[name])
    n = len(durs)
    med = statistics.median(durs)
    p95 = durs[int(n * 0.95)] if n >= 20 else durs[-1]
    mx = durs[-1]
    def fmt_dur(ms):
        if ms > 60000:
            return f"{ms/1000:.0f}s"
        elif ms > 1000:
            return f"{ms/1000:.1f}s"
        else:
            return f"{ms:.0f}ms"
    print(f"{name:<55} {n:>6} {fmt_dur(med):>10} {fmt_dur(p95):>10} {fmt_dur(mx):>10}")

# ===== 3. OUTLIERS > 120s =====
print("\n" + "="*80)
print("3. OUTLIERS (>120s)")
print("="*80)

outliers = [(s["duration_ms"]/1000, s) for s in all_spans if s.get("duration_ms", 0) > 120000]
outliers.sort(key=lambda x: -x[0])
print(f"\nTotal spans >120s: {len(outliers)}")
for dur_s, o in outliers[:15]:
    print(f"  {dur_s:.0f}s  {o.get('name','?')[:50]:<50}  {o['_target']}")

# ===== 4. MODEL COMPARISON =====
print("\n" + "="*80)
print("4. MODEL COMPARISON")
print("="*80)

model_stats = defaultdict(lambda: {"count": 0, "errors": 0, "durations": [], "tokens_in": 0, "tokens_out": 0})
for s in all_spans:
    attrs = s.get("attributes", {})
    model = attrs.get("gen_ai.request.model")
    if not model:
        continue
    model_stats[model]["count"] += 1
    if s.get("status") == "ERROR":
        model_stats[model]["errors"] += 1
    dur = s.get("duration_ms")
    if dur is not None:
        model_stats[model]["durations"].append(dur)
    ti = attrs.get("gen_ai.usage.input_tokens")
    to = attrs.get("gen_ai.usage.output_tokens")
    if ti: model_stats[model]["tokens_in"] += ti
    if to: model_stats[model]["tokens_out"] += to

print(f"\n{'Model':<35} {'Count':>6} {'Errors':>6} {'Err%':>6} {'Med':>8} {'P95':>8} {'Max':>8}")
print("-"*85)
for model in sorted(model_stats.keys(), key=lambda m: model_stats[m]["count"], reverse=True):
    d = model_stats[model]
    err_pct = d["errors"] / d["count"] * 100 if d["count"] > 0 else 0
    durs = sorted(d["durations"])
    if durs:
        med = statistics.median(durs) / 1000
        p95 = durs[int(len(durs)*0.95)] / 1000 if len(durs) >= 20 else durs[-1] / 1000
        mx = durs[-1] / 1000
    else:
        med = p95 = mx = 0
    print(f"{model:<35} {d['count']:>6} {d['errors']:>6} {err_pct:>5.1f}% {med:>7.1f}s {p95:>7.1f}s {mx:>7.1f}s")

# ===== 5. LOOP DETECTION =====
print("\n" + "="*80)
print("5. EXACT LOOP DETECTION (identical consecutive calls)")
print("="*80)

loop_examples = []
file_loop_counts = defaultdict(int)

for fpath in jsonl_files:
    fname = os.path.basename(fpath)
    target = extract_target(fname)

    spans = []
    with open(fpath, "r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                span = json.loads(line)
                spans.append((line_no, span))
            except json.JSONDecodeError:
                pass

    prev_tool = None
    prev_args_hash = None
    repeat_count = 0

    for line_no, span in spans:
        name = span.get("name", "")
        attrs = span.get("attributes", {})

        tool_name = None
        args_str = ""
        if name.startswith("execute_tool "):
            tool_name = name.replace("execute_tool ", "")
            tool_args = attrs.get("tool.arguments", attrs.get("tool_args", ""))
            args_str = str(tool_args)[:500] if tool_args else ""
        elif name.startswith("AutonomousProver.tool_call."):
            tool_name = "AutoProver." + name.replace("AutonomousProver.tool_call.", "")
            tool_args = attrs.get("tool.arguments", attrs.get("function.arguments", ""))
            args_str = str(tool_args)[:500] if tool_args else ""

        if tool_name:
            args_hash = hashlib.md5(args_str.encode()).hexdigest()
            if tool_name == prev_tool and args_hash == prev_args_hash:
                repeat_count += 1
                if repeat_count == 2:
                    loop_examples.append({
                        "file": fname,
                        "line": line_no,
                        "tool": tool_name,
                        "args_preview": args_str[:200],
                        "target": target,
                    })
                    file_loop_counts[fname] += 1
            else:
                repeat_count = 0
            prev_tool = tool_name
            prev_args_hash = args_hash
        else:
            prev_tool = None
            prev_args_hash = None
            repeat_count = 0

print(f"\nTotal exact loops (3+ identical consecutive): {len(loop_examples)}")
tool_loop_counts = Counter(e["tool"] for e in loop_examples)
print(f"\nLoops by tool:")
for tool, cnt in tool_loop_counts.most_common():
    print(f"  {tool}: {cnt}")

print(f"\nTop files by loop count:")
for fname, cnt in sorted(file_loop_counts.items(), key=lambda x: -x[1])[:10]:
    print(f"  {fname}: {cnt}")

print(f"\nLoop examples (first 10):")
for ex in loop_examples[:10]:
    print(f"  [{ex['target']}] {ex['file']}:{ex['line']}  tool={ex['tool']}")
    print(f"    args: {ex['args_preview'][:120]}...")

# ===== 6. SEMANTIC LOOPS (same tool, different args) =====
print("\n" + "="*80)
print("6. SEMANTIC LOOPS (8+ consecutive same-tool calls)")
print("="*80)

long_runs = []
for fpath in jsonl_files:
    fname = os.path.basename(fpath)
    target = extract_target(fname)

    tool_runs = []
    with open(fpath, "r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                span = json.loads(line)
            except:
                continue
            name = span.get("name", "")
            if name.startswith("execute_tool "):
                tool_name = name.replace("execute_tool ", "")
                tool_runs.append((line_no, tool_name))
            elif name.startswith("AutonomousProver.tool_call."):
                tool_name = "Auto." + name.replace("AutonomousProver.tool_call.", "")
                tool_runs.append((line_no, tool_name))

    if not tool_runs:
        continue
    cur_tool = tool_runs[0][1]
    cur_start = 0
    for i in range(1, len(tool_runs)):
        if tool_runs[i][1] != cur_tool:
            run_len = i - cur_start
            if run_len >= 8:
                long_runs.append((target, fname, cur_tool, run_len, tool_runs[cur_start][0], tool_runs[i-1][0]))
            cur_tool = tool_runs[i][1]
            cur_start = i
    run_len = len(tool_runs) - cur_start
    if run_len >= 8:
        long_runs.append((target, fname, cur_tool, run_len, tool_runs[cur_start][0], tool_runs[-1][0]))

print(f"\nTop 20 longest same-tool runs:")
for target, fname, tool, count, start_ln, end_ln in sorted(long_runs, key=lambda x: -x[3])[:20]:
    print(f"  [{target}] {tool} x{count} (L{start_ln}-L{end_ln})  {fname}")

# ===== 7. RATE LIMIT ANALYSIS =====
print("\n" + "="*80)
print("7. RATE LIMIT (429) ERRORS")
print("="*80)

rl_by_model = defaultdict(int)
rl_total = 0
for s in all_spans:
    if s.get("status") != "ERROR":
        continue
    attrs = s.get("attributes", {})
    model = attrs.get("gen_ai.request.model", "unknown")
    events = s.get("events", [])
    for e in events:
        if e.get("name") == "exception":
            msg = str(e.get("attributes", {}).get("exception.message", ""))
            if "429" in msg or "Rate limit" in msg:
                rl_by_model[model] += 1
                rl_total += 1

print(f"\nTotal 429 errors: {rl_total}")
print(f"\n429 by model:")
for model, cnt in sorted(rl_by_model.items(), key=lambda x: -x[1]):
    total_calls = model_stats.get(model, {}).get("count", 0)
    pct = cnt / max(1, total_calls) * 100
    print(f"  {model}: {cnt} ({pct:.1f}% of {total_calls} calls)")

# ===== 8. WRITE-COMPILE CYCLES =====
print("\n" + "="*80)
print("8. WRITE-COMPILE CYCLES PER TARGET")
print("="*80)

wc = defaultdict(lambda: {"writes": 0, "compiles": 0, "reads": 0, "searches": 0})
for s in all_spans:
    name = s.get("name", "")
    target = s["_target"]
    if "file_replace_sorry" in name or "file_replace_lines" in name:
        wc[target]["writes"] += 1
    elif "compile_probe_goal" in name:
        wc[target]["compiles"] += 1
    elif name == "execute_tool file_read_lines":
        wc[target]["reads"] += 1
    elif "search_mathlib" in name:
        wc[target]["searches"] += 1

print(f"\n{'Target':<40} {'Writes':>6} {'Compiles':>8} {'Reads':>6} {'Search':>7} {'C/W':>5}")
print("-"*75)
for target in sorted(wc.keys(), key=lambda t: wc[t]["compiles"], reverse=True)[:15]:
    d = wc[target]
    ratio = d["compiles"] / max(1, d["writes"])
    print(f"{target:<40} {d['writes']:>6} {d['compiles']:>8} {d['reads']:>6} {d['searches']:>7} {ratio:>5.1f}")

# ===== 9. SESSION OUTCOMES =====
print("\n" + "="*80)
print("9. SESSION OUTCOMES")
print("="*80)

outcomes = defaultdict(lambda: defaultdict(int))
for s in all_spans:
    name = s.get("name", "")
    target = s["_target"]
    if "sorry_guard" in name:
        outcomes[target]["sorry_guard"] += 1
    elif "intractable" in name:
        outcomes[target]["intractable"] += 1
    elif "iteration_cap" in name:
        outcomes[target]["iteration_cap"] += 1
    elif "already_solved" in name:
        outcomes[target]["already_solved"] += 1
    elif "f1_escalation" in name:
        outcomes[target]["f1_escalation"] += 1

print(f"\n{'Target':<40} {'IterCap':>7} {'SorryG':>7} {'Intrac':>7} {'F1Esc':>6} {'Solved':>6}")
print("-"*80)
for target in sorted(outcomes.keys()):
    d = outcomes[target]
    total = sum(d.values())
    if total > 0:
        print(f"{target:<40} {d['iteration_cap']:>7} {d['sorry_guard']:>7} {d['intractable']:>7} {d['f1_escalation']:>6} {d['already_solved']:>6}")

# ===== 10. AUTO vs MULTI MODE COMPARISON =====
print("\n" + "="*80)
print("10. AUTO vs MULTI MODE COMPARISON")
print("="*80)

mode_stats = defaultdict(lambda: {"files": 0, "spans": 0, "errors": 0, "total_duration_s": 0, "sessions": []})
for fpath in jsonl_files:
    fname = os.path.basename(fpath)
    target = extract_target(fname)
    mode = "auto" if fname.startswith("auto_") else "multi" if fname.startswith("multi_") else "custom"

    file_spans = []
    with open(fpath, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                span = json.loads(line)
                file_spans.append(span)
            except:
                pass

    errors = sum(1 for s in file_spans if s.get("status") == "ERROR")
    duration_s = max((s.get("duration_ms", 0) for s in file_spans), default=0) / 1000

    mode_stats[mode]["files"] += 1
    mode_stats[mode]["spans"] += len(file_spans)
    mode_stats[mode]["errors"] += errors
    mode_stats[mode]["total_duration_s"] += duration_s

print(f"\n{'Mode':<10} {'Files':>6} {'Spans':>8} {'Errors':>8} {'Err%':>6} {'TotalDur':>10} {'AvgDur':>8}")
print("-"*60)
for mode in ["auto", "multi", "custom"]:
    d = mode_stats[mode]
    err_pct = d["errors"] / max(1, d["spans"]) * 100
    avg_dur = d["total_duration_s"] / max(1, d["files"])
    print(f"{mode:<10} {d['files']:>6} {d['spans']:>8} {d['errors']:>8} {err_pct:>5.1f}% {d['total_duration_s']:>9.0f}s {avg_dur:>7.0f}s")
