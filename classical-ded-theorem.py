from typing import List, Tuple, Set

IMP = "->"

class Fm:
    """
    Represents an implicative formula.
    """
    def __init__(self, comps: List = None, head : str = IMP):
        self.head = head
        self.comps = comps
        if head == IMP:
            self.is_prop = False
        else:
            self.is_prop = True

    def print(self, trans):
        if self.is_prop:
            return trans.get(self.head, self.head)
        else:
            return "(%s %s %s)" % (self.comps[0].print(trans), trans.get(self.head, self.head), self.comps[1].print(trans))

class DerivLine:
    def __init__(self, fmla, reason):
        self.fmla = fmla
        self.reason = reason

class Derivation:

    def __init__(self, stmt : Tuple[Set[Fm], Fm], lines: List[DerivLine]):
        self.stmt = stmt
        self.lines = lines

    def _make_axiom_1(self, fm1, fm2):
        return Fm([fm1, Fm([fm2, fm1])])

    def _make_axiom_2(self, fm1, fm2, fm3):
        return Fm([Fm([fm1, Fm([fm2, fm3])]), Fm([Fm([fm1, fm2]), Fm([fm1, fm3])])])
    
    def deduction_theorem_derivation(self, X : Fm):
        new_lines = list()
        S = self.stmt[0] - {X}
        idx = 0
        old = 0
        old_new_map = dict()
        for original_line in self.lines:
            new_fmla = Fm([X, original_line.fmla])
            if (original_line.reason == "S" and original_line.fmla in S) or original_line.reason in {"A1", "A2"} or original_line.reason == "Theorem":
                new_lines.append(original_line)
                new_lines.append(DerivLine(self._make_axiom_1(original_line.fmla, X), "A1"))
                idx += 2
                new_lines.append(DerivLine(new_fmla, "MP %d %d" % (idx-1,idx-2)))
                old_new_map[old] = idx
                idx += 1
            elif X == original_line.fmla:
                new_lines.append(DerivLine(Fm([original_line.fmla, original_line.fmla]), "Theorem"))
                old_new_map[old] = idx
                idx += 1
            else:
                rule, fm1, fm2 = original_line.reason.split(' ')
                Zk = self.lines[int(fm1)].fmla
                Zj = self.lines[int(fm2)].fmla
                Zi = original_line.fmla
                new_lines.append(DerivLine(self._make_axiom_2(X, Zj, Zi), "A2"))
                idx += 1
                new_lines.append(DerivLine(Fm([Fm([X, Zj]), Fm([X, Zi])]), "MP %d %d" % (idx-1, old_new_map[int(fm1)])))
                idx += 1
                new_lines.append(DerivLine(new_fmla, "MP %d %d" % (idx-1, old_new_map[int(fm2)])))
                old_new_map[old] = idx
                idx += 1
            old += 1
        return Derivation(stmt=(S, Fm([X, self.stmt[1]])), lines=new_lines)

    def print(self, trans):
        print("%s |-- %s" % ([f.print(trans={}) for f in self.stmt[0]], self.stmt[1].print(trans={})))
        idx = 0
        width_fmla = max(map(lambda l : len(l.fmla.print(trans)), self.lines))+1
        width_reason = max(map(lambda l : len(l.reason), self.lines))+1
        for l in self.lines:
            print(("%"+str(len(str(len(self.lines))))+"s %"+str(width_fmla)+"s %"+str(width_reason)+"s") % (idx, l.fmla.print(trans), l.reason))
            idx += 1

P = Fm(head="P")
Q = Fm(head="Q")
R = Fm(head="R")
QiR = Fm([Q, R])
PiQiR = Fm([P, QiR])

initial = \
    Derivation(
        stmt = ({PiQiR, Q, P}, R),
        lines = [
            DerivLine(PiQiR, "S"),
            DerivLine(P, "S"),
            DerivLine(QiR, "MP 0 1"),
            DerivLine(Q, "S"),
            DerivLine(R, "MP 2 3"),
        ]
    )

initial.print(trans={})
print()
D1 = initial.deduction_theorem_derivation(P)
D1.print(trans={})
print()
D2 = D1.deduction_theorem_derivation(Q)
D2.print(trans={})
print()
D3 = D2.deduction_theorem_derivation(PiQiR)
D3.print(trans={})
