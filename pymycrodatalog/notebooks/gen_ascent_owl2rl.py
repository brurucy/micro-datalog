import sys; sys.path.insert(0, '.')
from rules import OWL2RL_ALL_RULES

preds = set()
for rule in OWL2RL_ALL_RULES:
    for atom in rule:
        preds.add(atom[0])

lines = []
lines.append("ascent! {")
lines.append("    struct AscentOWL2RL;")

for pred in sorted(preds):
    rust_name = pred.replace("-", "_")
    lines.append(f"    relation {rust_name}(usize, usize);")

lines.append("")

fresh_counter = 0

for rule in OWL2RL_ALL_RULES:
    head = rule[0]
    body = rule[1:]
    h_pred = head[0].replace("-", "_")
    h_terms = head[1]

    var_map = {}
    def get_var(v):
        if isinstance(v, int):
            return str(v)
        if v not in var_map:
            var_map[v] = v.lower()
        return var_map[v]

    h_args = ", ".join(get_var(t) for t in h_terms)

    body_parts = []
    filters = []
    for atom in body:
        b_pred = atom[0].replace("-", "_")
        b_terms = list(atom[1])
        b_args_out = []
        seen_in_atom = {}
        for t in b_terms:
            v = get_var(t)
            if v in seen_in_atom:
                fresh_counter += 1
                fresh = f"_fv{fresh_counter}"
                b_args_out.append(fresh)
                filters.append(f"if *{seen_in_atom[v]} == *{fresh}")
            else:
                seen_in_atom[v] = v
                b_args_out.append(v)
        body_parts.append(f"{b_pred}({', '.join(b_args_out)})")

    head_str = f"{h_pred}({h_args})"
    body_str = ", ".join(body_parts)
    if filters:
        body_str += ", " + ", ".join(filters)
    lines.append(f"    {head_str} <-- {body_str};")

lines.append("}")
print("\n".join(lines))
