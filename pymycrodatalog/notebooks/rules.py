"""Datalog program definitions for all benchmarks.

All rules use PyDBSP syntax: str = variable, int = constant.
DYRE encodes unary as binary with repeated arg.
"""

V = str  # variables are strings

# ============================================================================
# RDFS entailment (6 rules, ternary)
# ============================================================================
# T(y, "rdf:type", x) <- T(a, "rdfs:domain", x), T(y, a, z)
# T(z, "rdf:type", x) <- T(a, "rdfs:range", x), T(y, a, z)
# T(x, "rdfs:subPropertyOf", z) <- T(x, "rdfs:subPropertyOf", y), T(y, "rdfs:subPropertyOf", z)
# T(x, "rdfs:subClassOf", z) <- T(x, "rdfs:subClassOf", y), T(y, "rdfs:subClassOf", z)
# T(z, "rdf:type", y) <- T(x, "rdfs:subClassOf", y), T(z, "rdf:type", x)
# T(x, b, y) <- T(a, "rdfs:subPropertyOf", b), T(x, a, y)
#
# We intern the RDF/RDFS predicate URIs as integer constants.

# Predicate ID constants (must match the interning used when loading facts)
# These will be set by the benchmark after loading data, since they depend
# on the intern dict. For now, use placeholder strings that the benchmark
# will map to IDs.

RDFS_PREDICATE_NAMES = {
    "rdf_type": "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
    "rdfs_domain": "http://www.w3.org/2000/01/rdf-schema#domain",
    "rdfs_range": "http://www.w3.org/2000/01/rdf-schema#range",
    "rdfs_subPropertyOf": "http://www.w3.org/2000/01/rdf-schema#subPropertyOf",
    "rdfs_subClassOf": "http://www.w3.org/2000/01/rdf-schema#subClassOf",
}


def rdfs_rules(pred_ids: dict[str, int]) -> list[tuple]:
    """RDFS rules with concrete predicate IDs.

    pred_ids maps: "rdf_type" -> int, "rdfs_domain" -> int, etc.
    """
    rdf_type = pred_ids["rdf_type"]
    rdfs_domain = pred_ids["rdfs_domain"]
    rdfs_range = pred_ids["rdfs_range"]
    rdfs_subPropertyOf = pred_ids["rdfs_subPropertyOf"]
    rdfs_subClassOf = pred_ids["rdfs_subClassOf"]

    return [
        # Copy rule: T(s,p,o) <- Triple(s,p,o)
        # Mirrors DDLog/Souffle where input goes into a separate EDB relation
        # and a copy rule populates T, so that IDB count includes the base data.
        (("T", (V("S"), V("P"), V("O"))), ("Triple", (V("S"), V("P"), V("O")))),
        # T(y, rdf:type, x) <- T(a, rdfs:domain, x), T(y, a, z)
        (("T", (V("Y"), rdf_type, V("X"))), ("T", (V("A"), rdfs_domain, V("X"))), ("T", (V("Y"), V("A"), V("Z")))),
        # T(z, rdf:type, x) <- T(a, rdfs:range, x), T(y, a, z)
        (("T", (V("Z"), rdf_type, V("X"))), ("T", (V("A"), rdfs_range, V("X"))), ("T", (V("Y"), V("A"), V("Z")))),
        # T(x, rdfs:subPropertyOf, z) <- T(x, rdfs:subPropertyOf, y), T(y, rdfs:subPropertyOf, z)
        (("T", (V("X"), rdfs_subPropertyOf, V("Z"))), ("T", (V("X"), rdfs_subPropertyOf, V("Y"))), ("T", (V("Y"), rdfs_subPropertyOf, V("Z")))),
        # T(x, rdfs:subClassOf, z) <- T(x, rdfs:subClassOf, y), T(y, rdfs:subClassOf, z)
        (("T", (V("X"), rdfs_subClassOf, V("Z"))), ("T", (V("X"), rdfs_subClassOf, V("Y"))), ("T", (V("Y"), rdfs_subClassOf, V("Z")))),
        # T(z, rdf:type, y) <- T(x, rdfs:subClassOf, y), T(z, rdf:type, x)
        (("T", (V("Z"), rdf_type, V("Y"))), ("T", (V("X"), rdfs_subClassOf, V("Y"))), ("T", (V("Z"), rdf_type, V("X")))),
        # T(x, b, y) <- T(a, rdfs:subPropertyOf, b), T(x, a, y)
        (("T", (V("X"), V("B"), V("Y"))), ("T", (V("A"), rdfs_subPropertyOf, V("B"))), ("T", (V("X"), V("A"), V("Y")))),
    ]


# ============================================================================
# Transitive Closure (2 rules, binary)
# ============================================================================

TC_RULES = [
    # T(x, y) <- E(x, y)
    (("T", (V("X"), V("Y"))), ("E", (V("X"), V("Y")))),
    # T(x, z) <- E(x, y), T(y, z)
    (("T", (V("X"), V("Z"))), ("E", (V("X"), V("Y"))), ("T", (V("Y"), V("Z")))),
]

# ============================================================================
# OWL2RL (128 rules, binary — unary encoded as repeated arg)
# Imported from the existing benchmark infrastructure.
# ============================================================================

# 105 common rules
OWL2RL_COMMON_RULES = [
    # 27 copy rules
    (("advisor", (V("X"), V("Y"))), ("src_advisor", (V("X"), V("Y")))),
    (("assistantprofessor", (V("X"), V("X"))), ("src_assistantprofessor", (V("X"), V("X")))),
    (("associateprofessor", (V("X"), V("X"))), ("src_associateprofessor", (V("X"), V("X")))),
    (("course", (V("X"), V("X"))), ("src_course", (V("X"), V("X")))),
    (("department", (V("X"), V("X"))), ("src_department", (V("X"), V("X")))),
    (("doctoraldegreefrom", (V("X"), V("Y"))), ("src_doctoraldegreefrom", (V("X"), V("Y")))),
    (("emailaddress", (V("X"), V("Y"))), ("src_emailaddress", (V("X"), V("Y")))),
    (("fullprofessor", (V("X"), V("X"))), ("src_fullprofessor", (V("X"), V("X")))),
    (("graduatecourse", (V("X"), V("X"))), ("src_graduatecourse", (V("X"), V("X")))),
    (("graduatestudent", (V("X"), V("X"))), ("src_graduatestudent", (V("X"), V("X")))),
    (("headof", (V("X"), V("Y"))), ("src_headof", (V("X"), V("Y")))),
    (("lecturer", (V("X"), V("X"))), ("src_lecturer", (V("X"), V("X")))),
    (("mastersdegreefrom", (V("X"), V("Y"))), ("src_mastersdegreefrom", (V("X"), V("Y")))),
    (("memberof", (V("X"), V("Y"))), ("src_memberof", (V("X"), V("Y")))),
    (("publicationauthor", (V("X"), V("Y"))), ("src_publicationauthor", (V("X"), V("Y")))),
    (("researchassistant", (V("X"), V("X"))), ("src_researchassistant", (V("X"), V("X")))),
    (("researchgroup", (V("X"), V("X"))), ("src_researchgroup", (V("X"), V("X")))),
    (("suborganizationof", (V("X"), V("Y"))), ("src_suborganizationof", (V("X"), V("Y")))),
    (("takescourse", (V("X"), V("Y"))), ("src_takescourse", (V("X"), V("Y")))),
    (("teacherof", (V("X"), V("Y"))), ("src_teacherof", (V("X"), V("Y")))),
    (("teachingassistant", (V("X"), V("X"))), ("src_teachingassistant", (V("X"), V("X")))),
    (("teachingassistantof", (V("X"), V("Y"))), ("src_teachingassistantof", (V("X"), V("Y")))),
    (("telephone", (V("X"), V("Y"))), ("src_telephone", (V("X"), V("Y")))),
    (("undergraduatedegreefrom", (V("X"), V("Y"))), ("src_undergraduatedegreefrom", (V("X"), V("Y")))),
    (("undergraduatestudent", (V("X"), V("X"))), ("src_undergraduatestudent", (V("X"), V("X")))),
    (("university", (V("X"), V("X"))), ("src_university", (V("X"), V("X")))),
    (("worksfor", (V("X"), V("Y"))), ("src_worksfor", (V("X"), V("Y")))),
    # class hierarchy
    (("employee", (V("X"), V("X"))), ("administrativestaff", (V("X"), V("X")))),
    (("professor", (V("X"), V("X"))), ("assistantprofessor", (V("X"), V("X")))),
    (("professor", (V("X"), V("X"))), ("associateprofessor", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("chair", (V("X"), V("X")))),
    (("professor", (V("X"), V("X"))), ("chair", (V("X"), V("X")))),
    (("administrativestaff", (V("X"), V("X"))), ("clericalstaff", (V("X"), V("X")))),
    (("organization", (V("X"), V("X"))), ("college", (V("X"), V("X")))),
    (("article", (V("X"), V("X"))), ("conferencepaper", (V("X"), V("X")))),
    (("professor", (V("X"), V("X"))), ("dean", (V("X"), V("X")))),
    (("organization", (V("X"), V("X"))), ("department", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("director", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("employee", (V("X"), V("X")))),
    (("employee", (V("X"), V("X"))), ("faculty", (V("X"), V("X")))),
    (("professor", (V("X"), V("X"))), ("fullprofessor", (V("X"), V("X")))),
    (("course", (V("X"), V("X"))), ("graduatecourse", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("graduatestudent", (V("X"), V("X")))),
    (("organization", (V("X"), V("X"))), ("institute", (V("X"), V("X")))),
    (("article", (V("X"), V("X"))), ("journalarticle", (V("X"), V("X")))),
    (("faculty", (V("X"), V("X"))), ("lecturer", (V("X"), V("X")))),
    (("faculty", (V("X"), V("X"))), ("postdoc", (V("X"), V("X")))),
    (("faculty", (V("X"), V("X"))), ("professor", (V("X"), V("X")))),
    (("organization", (V("X"), V("X"))), ("program", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("researchassistant", (V("X"), V("X")))),
    (("organization", (V("X"), V("X"))), ("researchgroup", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("student", (V("X"), V("X")))),
    (("administrativestaff", (V("X"), V("X"))), ("systemsstaff", (V("X"), V("X")))),
    (("article", (V("X"), V("X"))), ("technicalreport", (V("X"), V("X")))),
    (("person", (V("X"), V("X"))), ("teachingassistant", (V("X"), V("X")))),
    # projection
    (("person", (V("X"), V("X"))), ("advisor", (V("X"), V("Y")))),
    (("professor", (V("Y"), V("Y"))), ("advisor", (V("X"), V("Y")))),
    (("organization", (V("X"), V("X"))), ("affiliatedorganizationof", (V("X"), V("Y")))),
    (("organization", (V("Y"), V("Y"))), ("affiliatedorganizationof", (V("X"), V("Y")))),
    (("organization", (V("X"), V("X"))), ("affiliateof", (V("X"), V("Y")))),
    (("person", (V("Y"), V("Y"))), ("affiliateof", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("age", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("degreefrom", (V("X"), V("Y")))),
    (("university", (V("Y"), V("Y"))), ("degreefrom", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("doctoraldegreefrom", (V("X"), V("Y")))),
    (("university", (V("Y"), V("Y"))), ("doctoraldegreefrom", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("emailaddress", (V("X"), V("Y")))),
    (("person", (V("Y"), V("Y"))), ("hasalumnus", (V("X"), V("Y")))),
    (("university", (V("X"), V("X"))), ("hasalumnus", (V("X"), V("Y")))),
    (("course", (V("Y"), V("Y"))), ("listedcourse", (V("X"), V("Y")))),
    (("schedule", (V("X"), V("X"))), ("listedcourse", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("mastersdegreefrom", (V("X"), V("Y")))),
    (("university", (V("Y"), V("Y"))), ("mastersdegreefrom", (V("X"), V("Y")))),
    (("organization", (V("X"), V("X"))), ("member", (V("X"), V("Y")))),
    (("person", (V("Y"), V("Y"))), ("member", (V("X"), V("Y")))),
    (("organization", (V("X"), V("X"))), ("orgpublication", (V("X"), V("Y")))),
    (("person", (V("Y"), V("Y"))), ("publicationauthor", (V("X"), V("Y")))),
    (("research", (V("Y"), V("Y"))), ("publicationresearch", (V("X"), V("Y")))),
    (("research", (V("Y"), V("Y"))), ("researchproject", (V("X"), V("Y")))),
    (("researchgroup", (V("X"), V("X"))), ("researchproject", (V("X"), V("Y")))),
    (("software", (V("X"), V("X"))), ("softwaredocumentation", (V("X"), V("Y")))),
    (("software", (V("X"), V("X"))), ("softwareversion", (V("X"), V("Y")))),
    (("organization", (V("X"), V("X"))), ("suborganizationof", (V("X"), V("Y")))),
    (("organization", (V("Y"), V("Y"))), ("suborganizationof", (V("X"), V("Y")))),
    (("course", (V("Y"), V("Y"))), ("teacherof", (V("X"), V("Y")))),
    (("faculty", (V("X"), V("X"))), ("teacherof", (V("X"), V("Y")))),
    (("course", (V("Y"), V("Y"))), ("teachingassistantof", (V("X"), V("Y")))),
    (("teachingassistant", (V("X"), V("X"))), ("teachingassistantof", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("telephone", (V("X"), V("Y")))),
    (("professor", (V("X"), V("X"))), ("tenured", (V("X"), V("Y")))),
    (("person", (V("X"), V("X"))), ("title", (V("X"), V("Y")))),
    # binary copy/rename/inverse
    (("hasalumnus", (V("Y"), V("X"))), ("degreefrom", (V("X"), V("Y")))),
    (("degreefrom", (V("X"), V("Y"))), ("doctoraldegreefrom", (V("X"), V("Y")))),
    (("degreefrom", (V("Y"), V("X"))), ("hasalumnus", (V("X"), V("Y")))),
    (("worksfor", (V("X"), V("Y"))), ("headof", (V("X"), V("Y")))),
    (("degreefrom", (V("X"), V("Y"))), ("mastersdegreefrom", (V("X"), V("Y")))),
    (("memberof", (V("Y"), V("X"))), ("member", (V("X"), V("Y")))),
    (("member", (V("Y"), V("X"))), ("memberof", (V("X"), V("Y")))),
    # joins
    (("dean", (V("X"), V("X"))), ("headof", (V("X"), V("Y"))), ("college", (V("Y"), V("Y")))),
    (("chair", (V("X"), V("X"))), ("person", (V("X"), V("X"))), ("headof", (V("X"), V("Y"))), ("department", (V("Y"), V("Y")))),
    (("director", (V("X"), V("X"))), ("person", (V("X"), V("X"))), ("headof", (V("X"), V("Y"))), ("program", (V("Y"), V("Y")))),
    (("student", (V("X"), V("X"))), ("person", (V("X"), V("X"))), ("takescourse", (V("X"), V("Y"))), ("course", (V("Y"), V("Y")))),
    (("teachingassistant", (V("X"), V("X"))), ("person", (V("X"), V("X"))), ("teachingassistantof", (V("X"), V("Y"))), ("course", (V("Y"), V("Y")))),
    (("employee", (V("X"), V("X"))), ("person", (V("X"), V("X"))), ("worksfor", (V("X"), V("Y"))), ("organization", (V("Y"), V("Y")))),
    # transitive
    (("suborganizationof", (V("X"), V("Z"))), ("suborganizationof", (V("X"), V("Y"))), ("suborganizationof", (V("Y"), V("Z")))),
]

OWL2RL_STAR_ONLY_RULES = [
    (("person", (V("X"), V("X"))), ("undergraduatedegreefrom", (V("X"), V("Y")))),
    (("university", (V("Y"), V("Y"))), ("undergraduatedegreefrom", (V("X"), V("Y")))),
    (("degreefrom", (V("X"), V("Y"))), ("undergraduatedegreefrom", (V("X"), V("Y")))),
    (("student", (V("X"), V("X"))), ("undergraduatestudent", (V("X"), V("X")))),
    (("organization", (V("X"), V("X"))), ("university", (V("X"), V("X")))),
    (("professor", (V("X"), V("X"))), ("visitingprofessor", (V("X"), V("X")))),
    (("memberof", (V("X"), V("Y"))), ("worksfor", (V("X"), V("Y")))),
]

OWL2RL_HASH_ONLY_RULES = [
    (("name", (V("X"), V("Y"))), ("src_name", (V("X"), V("Y")))),
    (("publication", (V("X"), V("X"))), ("src_publication", (V("X"), V("X")))),
    (("researchinterest", (V("X"), V("Y"))), ("src_researchinterest", (V("X"), V("Y")))),
    (("publication", (V("X"), V("X"))), ("article", (V("X"), V("X")))),
    (("publication", (V("X"), V("X"))), ("book", (V("X"), V("X")))),
    (("work", (V("X"), V("X"))), ("course", (V("X"), V("X")))),
    (("publication", (V("X"), V("X"))), ("manual", (V("X"), V("X")))),
    (("publication", (V("Y"), V("Y"))), ("orgpublication", (V("X"), V("Y")))),
    (("publication", (V("X"), V("X"))), ("publicationauthor", (V("X"), V("Y")))),
    (("publication", (V("X"), V("X"))), ("publicationdate", (V("X"), V("Y")))),
    (("publication", (V("X"), V("X"))), ("publicationresearch", (V("X"), V("Y")))),
    (("work", (V("X"), V("X"))), ("research", (V("X"), V("X")))),
    (("publication", (V("X"), V("X"))), ("software", (V("X"), V("X")))),
    (("publication", (V("Y"), V("Y"))), ("softwaredocumentation", (V("X"), V("Y")))),
    (("publication", (V("X"), V("X"))), ("specification", (V("X"), V("X")))),
]

OWL2RL_STAR_AND_HASH_RULES = [
    (("publication", (V("X"), V("X"))), ("unofficialpublication", (V("X"), V("X")))),
]

OWL2RL_ALL_RULES = (
    OWL2RL_COMMON_RULES
    + OWL2RL_STAR_ONLY_RULES
    + OWL2RL_HASH_ONLY_RULES
    + OWL2RL_STAR_AND_HASH_RULES
)
