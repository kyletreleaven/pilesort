

def compile(pile_types: str):
    n = len(pile_types)
    on_a = [
        min(k if pile_types[k] == "Q" else (k + 1), n)
        for k in range(n)
    ]
    on_a.append(n)

    on_d = [
        min(k if pile_types[k] == "S" else (k + 1), n)
        for k in range(n)
    ]
    on_d.append(n)

    return {"a": on_a, "d": on_d}


def apply_word(machine, state: int, word: str):
    cur = state
    for action in word:
        cur = machine[action][cur]
    return cur
