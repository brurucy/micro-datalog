"""OWL2RL Incremental Evaluation Benchmark.

Compares three incremental evaluation strategies on LUBM1 data:
  1. Semi-naive incremental: full materialization via poll() + query()
  2. MST IncrementalQueryView: Magic Sets demand-driven, delta-driven
  3. SDT IncrementalQueryView: Subsumptive Demand Transformation, delta-driven

Facts are split into 20 batches and inserted incrementally.
Per-batch timing uses time.perf_counter_ns().
Results saved to /tmp/owl2rl_incremental_results.json.
"""

import json
import sys
import time
from collections import Counter
from pathlib import Path

from pymycrodatalog import IncrementalQueryView, MicroRuntime, Variable

# Import helpers from sibling modules
sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate import lubm_to_binary_facts
from rules import OWL2RL_ALL_RULES


# ============================================================================
# Convert str-variable rules to Variable-based rules
# ============================================================================

def convert_rule(rule: tuple) -> tuple:
    """Convert string-variable rules from rules.py to Variable-based rules."""
    def convert_term(t):
        if isinstance(t, str) and t[0].isupper() and len(t) <= 2:
            return Variable(t)
        return t

    def convert_atom(atom: tuple) -> tuple:
        pred, terms = atom
        return (pred, tuple(convert_term(t) for t in terms))

    return tuple(convert_atom(a) for a in rule)


OWL2RL = [convert_rule(r) for r in OWL2RL_ALL_RULES]


# ============================================================================
# Benchmark helpers
# ============================================================================

def make_batches(facts: list, n_batches: int) -> list[list]:
    """Split facts into n_batches roughly equal batches."""
    batch_size = max(1, len(facts) // n_batches)
    batches = [facts[i:i + batch_size] for i in range(0, len(facts), batch_size)]
    # Merge any trailing runt batch into the last full batch
    if len(batches) > n_batches:
        batches[-2].extend(batches[-1])
        batches.pop()
    return batches


def bench_semi_naive_incremental(
    rules: list,
    batches: list[list],
    pred: str,
    pattern: tuple,
) -> list[dict]:
    """Semi-naive: MicroRuntime with poll() + query() after each batch."""
    rt = MicroRuntime(rules)
    rows = []
    cumulative = 0
    for batch_idx, batch in enumerate(batches):
        for f in batch:
            rt.insert(f)
        cumulative += len(batch)
        t0 = time.perf_counter_ns()
        rt.poll()
        results = rt.query(pred, pattern)
        elapsed_us = (time.perf_counter_ns() - t0) / 1000
        rows.append({
            "batch_idx": batch_idx,
            "cumulative_facts": cumulative,
            "result_count": len(results),
            "time_us": elapsed_us,
        })
    return rows


def bench_incremental_view(
    rules: list,
    batches: list[list],
    pred: str,
    pattern: tuple,
    strategy: str,
) -> list[dict]:
    """IncrementalQueryView: persistent transformed runtime, delta-driven."""
    view = IncrementalQueryView(rules, pred, pattern, strategy=strategy)
    rows = []
    cumulative = 0
    for batch_idx, batch in enumerate(batches):
        for f in batch:
            view.insert(f)
        cumulative += len(batch)
        t0 = time.perf_counter_ns()
        view.poll()
        results = view.query()
        elapsed_us = (time.perf_counter_ns() - t0) / 1000
        rows.append({
            "batch_idx": batch_idx,
            "cumulative_facts": cumulative,
            "result_count": len(results),
            "time_us": elapsed_us,
        })
    return rows


# ============================================================================
# Main
# ============================================================================

def main():
    print("Loading LUBM1 data...")
    facts = lubm_to_binary_facts("lubm1")
    print(f"  {len(facts)} binary facts loaded")
    print(f"  OWL2RL: {len(OWL2RL)} rules")

    # Pick a query entity: find the most common professor for a BF query
    # We query the "professor" predicate with a specific entity bound
    # First, do a quick full materialization to find a good query entity
    rt_probe = MicroRuntime(OWL2RL)
    for f in facts:
        rt_probe.insert(f)
    rt_probe.poll()

    profs = rt_probe.query("professor", (None, None))
    print(f"  Total professors after full materialization: {len(profs)}")

    if not profs:
        print("ERROR: No professors found. Check LUBM data and rules.")
        sys.exit(1)

    # Pick the first professor entity for our BF query
    query_entity = profs[0][0]
    print(f"  Query entity: {query_entity}")
    del rt_probe

    # Split into 20 batches
    n_batches = 20
    batches = make_batches(facts, n_batches)
    print(f"  {len(batches)} batches, sizes: {[len(b) for b in batches]}")

    # BF query pattern: professor(entity, ?)
    query_pred = "professor"
    query_pattern = (query_entity, None)
    print(f"\nQuery: {query_pred}({query_entity}, _)")
    print("=" * 72)

    all_results = {}

    # --- 1. Semi-naive incremental ---
    print("\n[1/3] Semi-naive incremental...")
    t0 = time.perf_counter_ns()
    semi_rows = bench_semi_naive_incremental(OWL2RL, batches, query_pred, query_pattern)
    total_ms = (time.perf_counter_ns() - t0) / 1e6
    all_results["semi_naive"] = semi_rows
    print(f"  Done in {total_ms:.1f} ms total")
    print(f"  Final: {semi_rows[-1]['result_count']} results, last batch {semi_rows[-1]['time_us']:.0f} us")

    # --- 2. MST IncrementalQueryView ---
    print("\n[2/3] MST IncrementalQueryView...")
    t0 = time.perf_counter_ns()
    mst_rows = bench_incremental_view(OWL2RL, batches, query_pred, query_pattern, "MST")
    total_ms = (time.perf_counter_ns() - t0) / 1e6
    all_results["mst"] = mst_rows
    print(f"  Done in {total_ms:.1f} ms total")
    print(f"  Final: {mst_rows[-1]['result_count']} results, last batch {mst_rows[-1]['time_us']:.0f} us")

    # --- 3. SDT IncrementalQueryView ---
    print("\n[3/3] SDT IncrementalQueryView...")
    t0 = time.perf_counter_ns()
    sdt_rows = bench_incremental_view(OWL2RL, batches, query_pred, query_pattern, "SDT")
    total_ms = (time.perf_counter_ns() - t0) / 1e6
    all_results["sdt"] = sdt_rows
    print(f"  Done in {total_ms:.1f} ms total")
    print(f"  Final: {sdt_rows[-1]['result_count']} results, last batch {sdt_rows[-1]['time_us']:.0f} us")

    # ================================================================
    # Save results
    # ================================================================
    output_path = "/tmp/owl2rl_incremental_results.json"
    with open(output_path, "w") as f:
        json.dump({
            "metadata": {
                "dataset": "lubm1",
                "total_facts": len(facts),
                "n_batches": len(batches),
                "query_pred": query_pred,
                "query_entity": query_entity,
                "n_rules": len(OWL2RL),
            },
            "results": all_results,
        }, f, indent=2)
    print(f"\nResults saved to {output_path}")

    # ================================================================
    # Summary table
    # ================================================================
    print("\n" + "=" * 72)
    print("SUMMARY: OWL2RL Incremental Benchmark on LUBM1")
    print(f"Query: {query_pred}({query_entity}, _)  |  {len(OWL2RL)} rules  |  {len(facts)} facts  |  {len(batches)} batches")
    print("=" * 72)
    print(f"{'Batch':>5} {'Facts':>8} {'Semi-naive (us)':>16} {'MST (us)':>12} {'SDT (us)':>12} {'SN results':>11} {'MST results':>12} {'SDT results':>12}")
    print("-" * 95)

    for i in range(len(batches)):
        sn = semi_rows[i]
        mst = mst_rows[i]
        sdt = sdt_rows[i]
        print(
            f"{sn['batch_idx']:>5} "
            f"{sn['cumulative_facts']:>8} "
            f"{sn['time_us']:>16.0f} "
            f"{mst['time_us']:>12.0f} "
            f"{sdt['time_us']:>12.0f} "
            f"{sn['result_count']:>11} "
            f"{mst['result_count']:>12} "
            f"{sdt['result_count']:>12}"
        )

    print("-" * 95)

    # Totals
    sn_total = sum(r["time_us"] for r in semi_rows)
    mst_total = sum(r["time_us"] for r in mst_rows)
    sdt_total = sum(r["time_us"] for r in sdt_rows)
    print(f"{'Total':>5} {'':>8} {sn_total:>16.0f} {mst_total:>12.0f} {sdt_total:>12.0f}")

    if sn_total > 0:
        print(f"\nSpeedup vs semi-naive:  MST {sn_total / mst_total:.2f}x  |  SDT {sn_total / sdt_total:.2f}x")


if __name__ == "__main__":
    main()
