from itertools import combinations
from random import randint
import re
import sys

def declare_edges_constants(n):
    """Dichiara tutte le variabili che rappresentano i grattacieli"""
    return ["(declare-const {}{} Int)".format(side, i)
            for side in ["r", "u", "l", "d"] for i in range(n)]

def declare_grid_constants(n):
    """Dichiara tutte le variabili che rappresentano i grattacieli"""
    return ["(declare-const r{}c{} Int)".format(r, c) for r in range(n) for c in range(n)]

def declare_constants_conditions(n):
    """Dichiara le seguenti condizioni sulle variabili dei grattacieli:
    1) siano tra 1 e n (compresi)
    2) non ci siano ripetizioni su righe
    3) non ci siano ripetizioni su colonne
    """
    # siano compresi tra 1 e n
    lst = []
    lst.append("; Grattacieli compresi tra 1 e n")
    for r in range(n):
        for c in range(n):
            lst.append("(assert (and (< 0 r{r}c{c}) (< r{r}c{c} {m})))".format(r=r, c=c, m=(n+1)))


    # non ci siano ripetizioni sulle righe
    lst.append("; Niente ripetizioni sulle righe")
    for i in range(n):
        cons = " ".join(["r{i}c{c}".format(i=i, c=c) for c in range(n)])
        lst.append("(assert (distinct {}))".format(cons))

    # non ci siano ripetizioni sulle colonne
    lst.append("; Niente ripetizioni sulle colonne")
    for i in range(n):
        cons = " ".join(["r{r}c{i}".format(r=r, i=i) for r in range(n)])
        lst.append("(assert (distinct {}))".format(cons))

    return lst

def print_maxer(n):
    """
    Funzione helper per generare stringhe del tipo
    `(max a4 (max a3 (max a2 (max a1 a0))))`
    """
    if n == 0:
        return "a0"
    else:
        return "(max a{} {})".format(n, print_maxer(n-1))

def fun_max():
    """Costruisce la funzione `max` che restituisce il massimo tra due interi"""
    return ["(define-fun max ((a Int) (b Int)) Int (ite (> a b) a b))"]

def fun_counter(n):
    """Costruisce la funzione `counter` che conta quanti grattacieli sono
    visibili"""
    args = " ".join(["(a{} Int)".format(i) for i in range(n)])
    declaration = "(define-fun counter ({}) Int".format(args)

    lines = []
    lines.append(declaration)
    lines.append("  (+ 1")

    for i in range(1, n):
        lines.append("     (ite (> a{} {}) 1 0)".format(i, print_maxer(i-1)))

    lines[-1] = lines[-1] + "))"
    return lines

def fun_checker(n):
    """Costruisce la funzione che controlla che la griglia sia consistente"""
    args = " ".join(["(a{} Int)".format(i) for i in range(n)])
    declaration = "(define-fun counter ({} (tot Int)) Int".format(args)

    # Check right side
    right = []
    for i in range(n):
        counter_arg = " ".join(["r{}c{}".format(i, c) for c in range(n-1, -1, -1)])
        right.append("(assert (= r{} (counter {arg})))".format(i, arg=counter_arg))

    # Check up side
    up = []
    for i in range(n):
        counter_arg = " ".join(["r{}c{}".format(r, i) for r in range(n)])
        up.append("(assert (= u{} (counter {arg})))".format(i, arg=counter_arg))

    # Check left side
    left = []
    for i in range(n):
        counter_arg = " ".join(["r{}c{}".format(i, c) for c in range(n)])
        left.append("(assert (= l{} (counter {arg})))".format(i, arg=counter_arg))

    # Check down side
    down = []
    for i in range(n):
        counter_arg = " ".join(["r{}c{}".format(r, i) for r in range(n-1, -1, -1)])
        down.append("(assert (= d{} (counter {arg})))".format(i, arg=counter_arg))


    # lines[-1] = lines[-1] + "))"
    return (["; Check right side"] + right
            + ["; Check up side"] + up
            + ["; Check left side"] + left
            + ["; Check down side"] + down)

def assert_hints(n, edges_hints, grid_hints):
    """Costruisce le condizioni per l'intera griglia"""
    lst = []
    lst.append("; Condizioni sui lati")
    for e in edges_hints:
        lst.append("(assert (= {}{} {}))".format(*e))
    lst.append("; Condizioni sui grattacieli")
    for g in grid_hints:
        lst.append("(assert (= r{}c{} {}))".format(*g))
    return lst

def main(n, edges_hints, grid_hints):
    print("; Lati")
    print("\n".join(declare_edges_constants(n)))
    print("")
    print("; Grattacieli")
    print("\n".join(declare_grid_constants(n)))
    print("")
    print("\n".join(declare_constants_conditions(n)))
    print("")
    print("; Functions")
    print("\n".join(fun_max()))
    print("")
    print("\n".join(fun_counter(n)))
    print("")
    print("; Controlla che la griglia sia consistente")
    print("\n".join(fun_checker(n)))
    print("")
    print("; Condizioni per la griglia")
    print("\n".join(assert_hints(n, edges_hints, grid_hints)))
    print("")
    print("(check-sat)")
    print("; (get-model)")

# main(n)
if __name__ == '__main__':
    n = 0
    edges_hints = []
    grid_hints = []
    try:
        n = int(sys.argv[1])
        for arg in sys.argv[2:]:
            e = re.match(r"([ruld])([0-9]+)=([0-9]+)", arg)
            if e is not None:
                assert(int(e.group(2)) >= 0)
                assert(int(e.group(2)) < n)
                assert(int(e.group(3)) > 0)
                assert(int(e.group(3)) <= n)
                edges_hints.append(e.groups())
            g = re.match(r"r([0-9]+)c([0-9]+)=([0-9]+)", arg)
            if g is not None:
                assert(int(g.group(1)) >= 0)
                assert(int(g.group(1)) < n)
                assert(int(g.group(2)) >= 0)
                assert(int(g.group(2)) < n)
                assert(int(g.group(3)) > 0)
                assert(int(g.group(3)) <= n)
                grid_hints.append(g.groups())
        main(n, edges_hints, grid_hints)
    except Exception as e:
        print("Errore durante il parsing degli argomenti: ")
        print(e)
