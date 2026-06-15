import pytest
from pymycrodatalog import IncrementalQueryView, MicroRuntime, Variable

X = Variable("X")
Y = Variable("Y")
Z = Variable("Z")


def linear_tc_rules() -> list[tuple]:
    return [
        (("tc", (X, Y)), ("e", (X, Y))),
        (("tc", (X, Z)), ("e", (X, Y)), ("tc", (Y, Z))),
    ]


def chain_facts(pairs: list[tuple[str, str]]) -> list[tuple[str, tuple[str, str]]]:
    return [("e", (s, d)) for s, d in pairs]


def insert_facts(rt: MicroRuntime, facts: list[tuple]) -> None:
    for f in facts:
        rt.insert(f)


def query_sorted(rt: MicroRuntime, predicate: str, pattern: tuple) -> list[tuple[str, ...]]:
    return sorted(rt.query(predicate, pattern))


# ============================================================================
# Basic operations
# ============================================================================


def test_insert_poll_query() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "d")]))
    rt.poll()

    assert query_sorted(rt, "tc", ("a", None)) == [("a", "b"), ("a", "c"), ("a", "d")]


def test_contains() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c")]))
    rt.poll()

    assert rt.contains(("tc", ("a", "c")))
    assert not rt.contains(("tc", ("c", "a")))


def test_safe() -> None:
    rt = MicroRuntime(linear_tc_rules())
    rt.insert(("e", ("a", "b")))
    assert not rt.safe()
    rt.poll()
    assert rt.safe()


def test_len() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "d")]))
    rt.poll()
    # 3 edges + 6 tc facts = 9
    assert len(rt) == 9


def test_incremental_update() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c")]))
    rt.poll()
    assert query_sorted(rt, "tc", ("a", None)) == [("a", "b"), ("a", "c")]

    rt.insert(("e", ("c", "d")))
    rt.poll()
    assert query_sorted(rt, "tc", ("a", None)) == [("a", "b"), ("a", "c"), ("a", "d")]


# ============================================================================
# Engine selection
# ============================================================================


def test_free_join_engine() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c")]))
    rt.poll()
    assert query_sorted(rt, "tc", ("a", None)) == [("a", "b"), ("a", "c")]


# ============================================================================
# Query patterns: bf, fb, bb, ff
# ============================================================================


def test_query_bf() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "a")]))  # cycle
    rt.poll()
    assert len(rt.query("tc", ("a", None))) == 3


def test_query_fb() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "a")]))
    rt.poll()
    assert len(rt.query("tc", (None, "a"))) == 3


def test_query_bb() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "d")]))
    rt.poll()
    assert rt.query("tc", ("a", "d")) == [("a", "d")]
    assert rt.query("tc", ("d", "a")) == []


def test_query_ff() -> None:
    rt = MicroRuntime(linear_tc_rules())
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "a")]))
    rt.poll()
    # Full cycle: 3 nodes, each reaches all 3 = 9 facts
    assert len(rt.query("tc", (None, None))) == 9


# ============================================================================
# query_program: MST and SDT strategies
# ============================================================================


def test_query_program_mst() -> None:
    rules = linear_tc_rules()
    rt = MicroRuntime(rules)
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "d")]))

    results = sorted(rt.query_program("tc", ("a", None), rules, "Bottom-up"))
    assert results == [("a", "b"), ("a", "c"), ("a", "d")]


def test_query_program_sdt() -> None:
    rules = linear_tc_rules()
    rt = MicroRuntime(rules)
    insert_facts(rt, chain_facts([("a", "b"), ("b", "c"), ("c", "d")]))

    results = sorted(rt.query_program("tc", ("a", None), rules, "SDT"))
    assert results == [("a", "b"), ("a", "c"), ("a", "d")]


def test_query_program_mst_sdt_agree() -> None:
    rules = linear_tc_rules()
    rt = MicroRuntime(rules)
    insert_facts(
        rt,
        chain_facts([("a", "b"), ("b", "c"), ("c", "d"), ("d", "e")]),
    )

    mst = sorted(rt.query_program("tc", ("a", None), rules, "Bottom-up"))
    sdt = sorted(rt.query_program("tc", ("a", None), rules, "SDT"))
    assert mst == sdt


# ============================================================================
# Negation
# ============================================================================


@pytest.mark.xfail(
    strict=True,
    reason="Negation unimplemented: negated atoms are dropped, degrading this to "
    "result(X,Y):-e(X,Y). Remove marker if it XPASSes.",
)
def test_negation() -> None:
    rules = [
        (("result", (X, Y)), ("e", (X, Y)), ("!blocked", (X, Y))),
    ]
    rt = MicroRuntime(rules)
    rt.insert(("e", ("a", "b")))
    rt.insert(("e", ("b", "c")))
    rt.insert(("e", ("c", "d")))
    rt.insert(("blocked", ("b", "c")))
    rt.poll()

    assert query_sorted(rt, "result", (None, None)) == [("a", "b"), ("c", "d")]


# ============================================================================
# Same-generation (complex program)
# ============================================================================


def test_same_generation() -> None:
    rules = [
        (("sg", (X, Y)), ("flat", (X, Y))),
        (("sg", (Y, X)), ("sg", (X, Y))),
        (("sg", (X, Y)), ("up", (X, Z)), ("down", (Z, Y))),
        (("sg", (X, Y)), ("up", (X, Z)), ("sg", (Z, Variable("W"))), ("down", (Variable("W"), Y))),
    ]
    rt = MicroRuntime(rules)
    rt.insert(("flat", ("r1", "r2")))
    for child, parent in [("m1", "r1"), ("m2", "r1"), ("m3", "r2"), ("m4", "r2")]:
        rt.insert(("up", (child, parent)))
        rt.insert(("down", (parent, child)))
    rt.poll()

    results = query_sorted(rt, "sg", ("m1", None))
    assert ("m1", "m3") in results
    assert ("m1", "m4") in results


# ============================================================================
# Integer facts
# ============================================================================


def test_integer_facts() -> None:
    rules = [
        (("tc", (X, Y)), ("e", (X, Y))),
        (("tc", (X, Z)), ("e", (X, Y)), ("tc", (Y, Z))),
    ]
    rt = MicroRuntime(rules)
    rt.insert(("e", (0, 1)))
    rt.insert(("e", (1, 2)))
    rt.insert(("e", (2, 3)))
    rt.poll()

    results = rt.query("tc", (0, None))
    assert sorted(results) == [(0, 1), (0, 2), (0, 3)]


# ============================================================================
# Variable repr
# ============================================================================


def test_variable_repr() -> None:
    v = Variable("X")
    assert v.name == "X"
    assert repr(v) == 'Variable("X")'


# ============================================================================
# IncrementalQueryView
# ============================================================================


def test_incremental_mst_basic() -> None:
    rules = linear_tc_rules()
    view = IncrementalQueryView(rules, "tc", ("a", None), strategy="MST")
    view.insert(("e", ("a", "b")))
    view.insert(("e", ("b", "c")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c")]


def test_incremental_mst_batches() -> None:
    rules = linear_tc_rules()
    view = IncrementalQueryView(rules, "tc", ("a", None), strategy="MST")

    view.insert(("e", ("a", "b")))
    view.insert(("e", ("b", "c")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c")]

    view.insert(("e", ("c", "d")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c"), ("a", "d")]

    view.insert(("e", ("d", "e")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c"), ("a", "d"), ("a", "e")]


def test_incremental_sdt_batches() -> None:
    rules = linear_tc_rules()
    view = IncrementalQueryView(rules, "tc", ("a", None), strategy="SDT")

    view.insert(("e", ("a", "b")))
    view.insert(("e", ("b", "c")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c")]

    view.insert(("e", ("c", "d")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c"), ("a", "d")]


def test_incremental_free_join_engine() -> None:
    rules = linear_tc_rules()
    view = IncrementalQueryView(rules, "tc", ("a", None), strategy="MST")

    view.insert(("e", ("a", "b")))
    view.insert(("e", ("b", "c")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c")]

    view.insert(("e", ("c", "d")))
    view.poll()
    assert sorted(view.query()) == [("a", "b"), ("a", "c"), ("a", "d")]


def test_incremental_mst_sdt_agree() -> None:
    rules = linear_tc_rules()
    mst = IncrementalQueryView(rules, "tc", ("a", None), strategy="MST")
    sdt = IncrementalQueryView(rules, "tc", ("a", None), strategy="SDT")

    for s, d in [("a", "b"), ("b", "c"), ("c", "d")]:
        mst.insert(("e", (s, d)))
        sdt.insert(("e", (s, d)))
    mst.poll()
    sdt.poll()

    assert sorted(mst.query()) == sorted(sdt.query())


def test_incremental_safe() -> None:
    rules = linear_tc_rules()
    view = IncrementalQueryView(rules, "tc", ("a", None))
    view.insert(("e", ("a", "b")))
    assert not view.safe()
    view.poll()
    assert view.safe()
