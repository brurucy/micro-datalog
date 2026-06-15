"""Graph and data generators for all benchmarks."""

import math
import os
import random

LUBM_NS = "http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#"
RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
LUBM_DIR = os.path.join(os.path.dirname(__file__), "lubm")


# ============================================================================
# LUBM data loading
# ============================================================================


def load_lubm_triples(dataset: str = "lubm1") -> list[tuple[str, str, str]]:
    """Load raw (s, p, o) triples from LUBM .nt file."""
    path = os.path.join(LUBM_DIR, dataset, "Universities-1.nt")
    triples = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            line = line.rstrip(" .").rstrip(".")
            parts = line.split(" ", 2)
            if len(parts) < 3:
                continue
            s = parts[0].strip("<>")
            p = parts[1].strip("<>")
            o_raw = parts[2].strip()
            o = o_raw.strip("<>") if o_raw.startswith("<") else o_raw
            triples.append((s, p, o))
    return triples


def lubm_to_ternary_facts(
    dataset: str = "lubm1",
) -> list[tuple[str, tuple[int, int, int]]]:
    """Convert LUBM triples to ternary facts for RDFS program.

    Returns (relation="T", (s_id, p_id, o_id)) tuples.
    Uses integer IDs via a shared interning dict.
    """
    triples = load_lubm_triples(dataset)
    intern: dict[str, int] = {}
    next_id = [0]

    def get_id(uri: str) -> int:
        if uri not in intern:
            intern[uri] = next_id[0]
            next_id[0] += 1
        return intern[uri]

    facts = []
    seen: set[tuple[int, int, int]] = set()
    for s, p, o in triples:
        sid, pid, oid = get_id(s), get_id(p), get_id(o)
        key = (sid, pid, oid)
        if key not in seen:
            seen.add(key)
            facts.append(("T", key))
    return facts


def lubm_to_binary_facts(
    dataset: str = "lubm1",
) -> list[tuple[str, tuple[str, str]]]:
    """Convert LUBM triples to binary facts for OWL2RL program.

    Unary classes become (pred, (uri, uri)). Binary properties become (pred, (s_uri, o_uri)).
    No Python-side interning — DYRE hashes strings internally.
    """
    path = os.path.join(LUBM_DIR, dataset, "Universities-1.nt")
    facts = []
    seen: set[tuple] = set()
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            line = line.rstrip(" .").rstrip(".")
            parts = line.split(" ", 2)
            if len(parts) < 3:
                continue
            s = parts[0].strip("<>")
            p = parts[1].strip("<>")
            o_raw = parts[2].strip()
            o = o_raw.strip("<>") if o_raw.startswith("<") else o_raw

            if p == RDF_TYPE and o.startswith(LUBM_NS):
                cls = "src_" + o[len(LUBM_NS):].lower()
                key = (cls, s)
                if key not in seen:
                    seen.add(key)
                    facts.append((cls, (s, s)))
            elif p.startswith(LUBM_NS):
                pred = "src_" + p[len(LUBM_NS):].lower()
                key = (pred, s, o)
                if key not in seen:
                    seen.add(key)
                    facts.append((pred, (s, o)))
    return facts


# ============================================================================
# Graph generators for TC benchmarks
# ============================================================================


def rand1k(seed: int = 42) -> list[tuple[int, int]]:
    """RAND1K: Dense random graph, ~1000 edges, ~1% connectivity.

    Paper: "a dense graph of one thousand edges. Each edge has around
    1% chance of being connected to each other."

    Interpretation: ~316 nodes (sqrt(1000/0.01) ≈ 316), 1000 edges.
    Each pair of nodes has ~1% chance of an edge.
    """
    rng = random.Random(seed)
    n = 316  # ~1% connectivity with 1000 edges: n*(n-1)*0.01 ≈ 1000
    edges: set[tuple[int, int]] = set()
    for i in range(n):
        for j in range(n):
            if i != j and rng.random() < 0.01:
                edges.add((i, j))
    return list(edges)


def rmat1k(seed: int = 42) -> list[tuple[int, int]]:
    """RMAT1K: Sparse RMAT graph, 10000 edges, 1000 nodes.

    Paper: "ten thousand edges and one thousand nodes. It is a sparse graph
    that follows an inverse power-law distribution."

    Uses the Recursive MATrix (R-MAT) algorithm with standard parameters
    (a=0.57, b=0.19, c=0.19, d=0.05) for power-law degree distribution.
    """
    rng = random.Random(seed)
    n = 1000
    target_edges = 10000
    a, b, c = 0.57, 0.19, 0.19
    # d = 1 - a - b - c = 0.05

    log2n = int(math.ceil(math.log2(n)))

    edges: set[tuple[int, int]] = set()
    while len(edges) < target_edges:
        u, v = 0, 0
        for depth in range(log2n):
            step = 1 << (log2n - 1 - depth)
            r = rng.random()
            if r < a:
                pass  # top-left quadrant
            elif r < a + b:
                v += step  # top-right
            elif r < a + b + c:
                u += step  # bottom-left
            else:
                u += step  # bottom-right
                v += step
            # Add noise
            a_n = a * (0.95 + 0.1 * rng.random())
            b_n = b * (0.95 + 0.1 * rng.random())
            c_n = c * (0.95 + 0.1 * rng.random())
            s = a_n + b_n + c_n + (1 - a - b - c) * (0.95 + 0.1 * rng.random())
            a, b, c = a_n / s, b_n / s, c_n / s
            a, b, c = 0.57, 0.19, 0.19  # reset for next depth

        u, v = u % n, v % n
        if u != v:
            edges.add((u, v))

    return list(edges)


def graph_to_facts(edges: list[tuple[int, int]]) -> list[tuple[str, tuple[int, int]]]:
    """Convert edge list to PyDYRE facts."""
    return [("E", (u, v)) for u, v in edges]


# ============================================================================
# Data splitting for incremental benchmarks
# ============================================================================


def split_facts(
    facts: list, percentage: float, seed: int = 42
) -> tuple[list, list]:
    """Split facts into (initial, remaining) at the given percentage.

    Returns (initial_facts, remaining_facts) where initial is `percentage`%
    of the total, and remaining is the rest.
    """
    rng = random.Random(seed)
    shuffled = list(facts)
    rng.shuffle(shuffled)
    split_idx = int(len(shuffled) * percentage / 100)
    return shuffled[:split_idx], shuffled[split_idx:]
