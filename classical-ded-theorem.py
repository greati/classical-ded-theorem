from typing import List, Tuple, Set

CONNECTIVES = ["imp"]

class Fm:
    def __init__(self, head : str, comps: List = None):
        self.head = head
        self.comps = comps
        if head in CONNECTIVES:
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
    
    def deduction_theorem_derivation(self, X : Fm):
        new_lines = list()
        S = self.stmt[0] - {X}
        idx = 0
        old = 0
        old_new_map = dict()
        for original_line in self.lines:
            new_fmla = Fm("imp", [X, original_line.fmla])
            if (original_line.reason == "S" and original_line.fmla in S) or original_line.reason == "A" or original_line.reason == "Theorem":
                new_lines.append(original_line)
                new_lines.append(DerivLine(Fm("imp", [original_line.fmla, Fm("imp", [X, original_line.fmla])]), "A"))
                idx += 2
                new_lines.append(DerivLine(new_fmla, "MP %d %d" % (idx-1,idx-2)))
                old_new_map[old] = idx
                idx += 1
            elif X == original_line.fmla:
                new_lines.append(DerivLine(Fm("imp", [original_line.fmla, original_line.fmla]), "Theorem"))
                old_new_map[old] = idx
                idx += 1
            else:
                rule, fm1, fm2 = original_line.reason.split(' ')
                Zk = self.lines[int(fm1)].fmla
                Zj = self.lines[int(fm2)].fmla
                Zi = original_line.fmla
                new_lines.append(DerivLine(Fm("imp", 
                                    [
                                        Fm("imp", [X, Fm("imp", [Zj, Zi])]), 
                                        Fm("imp", [Fm("imp", [X, Zj]), Fm("imp", [X, Zi])])
                                    ])
                                           , "A"))
                idx += 1
                new_lines.append(DerivLine(Fm("imp", [Fm("imp", [X, Zj]), Fm("imp", [X, Zi])]), "MP %d %d" % (idx-1, old_new_map[int(fm1)])))
                idx += 1
                new_lines.append(DerivLine(new_fmla, "MP %d %d" % (idx-1, old_new_map[int(fm2)])))
                old_new_map[old] = idx
                idx += 1
            old += 1
        return Derivation(stmt=(S, Fm("imp", [X, self.stmt[1]])), lines=new_lines)


    def print(self, trans):
        idx = 0
        width_fmla = max(map(lambda l : len(l.fmla.print(trans)), self.lines))+1
        width_reason = max(map(lambda l : len(l.reason), self.lines))+1
        for l in self.lines:
            print(("%"+str(len(str(len(self.lines))))+"s %"+str(width_fmla)+"s %"+str(width_reason)+"s") % (idx, l.fmla.print(trans), l.reason))
            idx += 1

P = Fm(head="P")
Q = Fm(head="Q")
R = Fm(head="R")
QiR = Fm(head="imp", comps = [Q, R])
PiQiR = Fm(head="imp", comps = [P, QiR])

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
print("From: %s |-- %s" % ([f.print(trans={}) for f in initial.stmt[0]], initial.stmt[1].print(trans={})))
initial.print(trans={})

D1 = initial.deduction_theorem_derivation(P)
D2 = D1.deduction_theorem_derivation(Q)
D3 = D2.deduction_theorem_derivation(PiQiR)
print("To: %s |-- %s" % ([f.print(trans={}) for f in D3.stmt[0]], D3.stmt[1].print(trans={})))
D3.print(trans={})
