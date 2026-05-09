# Implementation roughly following Willsey et al.'s
# "egg: Fast and Extensible Equality Saturation"

class UnionFind:
    def __init__(self):
        self.uf = []

    def print_tree(self, idr, last, prefix=""):
        if last:
            output = prefix + "└── " + str(idr) + "\n"
        else:
            output = prefix + "├── " + str(idr) + "\n"
        children = tuple(n for n in range(len(self.uf))
                         if self.uf[n] == idr and n != idr)
        for i, child in enumerate(children):
            if i == len(children) - 1:
                output += self.print_tree(child, True,
                                          prefix + ("    " if last else "│   "))
            else:
                output += self.print_tree(child, False,
                                          prefix + ("    " if last else "│   "))
        return output

    def __str__(self):
        roots = tuple(r for r in range(len(self.uf)) if self.uf[r] == r)
        output = "\n"
        for i, root in enumerate(roots):
            if i == len(roots) - 1:
                output += self.print_tree(root, True, "    ")
            else:
                output += self.print_tree(root, False, "    ")
        return output[:-1]

    def new_id(self):
        self.uf.append(len(self.uf))
        return len(self.uf) - 1

    def find(self, id0):
        while self.uf[id0] != id0:
            id0 = self.uf[id0]
        return id0

    def union(self, id1, id2):
        self.uf[self.find(id1)] = self.find(id2)
        return self.find(id2)


class nd:
    def __init__(self, f, bs = tuple()):
        self.f = f
        self.bs = bs

    def __str__(self):
        if len(self.bs):
            return f"[{self.f}]{self.bs}"
        else:
            return f"'{self.f}'"

    # This is debatable but makes for nice debugging. See
    # https://stackoverflow.com/questions/1436703/what-is-the-difference-between-str-and-repr
    # – especially the part about container's __str__ uses contained objects' __repr__
    def __repr__(self):
        if len(self.bs):
            return f"[{self.f}]{self.bs}"
        else:
            return f"'{self.f}'"

    def __eq__(self, other):
        return (self.f, self.bs) == (other.f, other.bs)

    def __hash__(self):
        return hash((self.f, self.bs))

    def canonicalize(self, uf):
        return nd(self.f, tuple(uf.find(a) for a in self.bs))

    def is_canonical(self, uf):
        return self == self.canonicalize(uf)


class EGGraph:
    def __init__(self):
        self.U = UnionFind()
        # self.M = {}
        self.H = {}
        self.wl = []

    def str_H(self):
        output = ""
        for i, (key, value) in enumerate(self.H.items()):
            output += ("    " if output else "") + f"{key} ↦ {value}\n"
        return output[:-1] if output else "{}"

    def synthesize_M(self):
        roots = tuple(r for r in range(len(self.U.uf)) if self.U.uf[r] == r)
        output = ""
        for idr in roots:
            member = {idr}
            while True:
                new_children = {n for n in range(len(self.U.uf))
                                if self.U.uf[n] in member and n not in member}
                if not new_children:
                    break
                member |= new_children
            nodes = {key for key, value in self.H.items() if value in member}
            member = ','.join({str(mem) for mem in member})
            output += ("    " if output else "") + f"{member} ↦ {nodes}\n"
        return output[:-1] if output else "{}"

    def __str__(self):
        return (f" U: {self.U}\n"
              + f" M: {self.synthesize_M()}\n"
              + f" H: {self.str_H()}\n"
              + f"wl: {self.wl}\n")

    def lookup(self, n):
        return self.H[n.canonicalize(self.U)]

    def add(self, n):
        try:
            return self.lookup(n)
        except KeyError:
            idn = self.U.new_id()
            self.H[n.canonicalize(self.U)] = idn
            return idn

    def merge(self, id1, id2):
        if self.U.find(id1) == self.U.find(id2):
            return self.U.find(id1)
        new_id = self.U.union(id1, id2)
        self.wl.append(new_id)
        return new_id

    def parents(self, idn):
        return tuple((n for n in self.H
                      if self.U.find(idn) in [self.U.find(b) for b in n.bs]))

    def repair(self, idr):
        # update the hashcons so it always points canonical enodes to canonical eclasses
        # print(f"Repair id {idr}")
        for parent in self.parents(idr):
            # print(f"Parent: {parent}")
            idp = self.U.find(self.H[parent])
            del self.H[parent]
            # print(f"self.H[{parent.canonicalize(self.U)}] = {idp}")
            if parent.canonicalize(self.U) in self.H:
                # print(f"self.merge({idp}, {self.H[parent.canonicalize(self.U)]})")
                idp = self.merge(idp, self.H[parent.canonicalize(self.U)])
            self.H[parent.canonicalize(self.U)] = idp

    def rebuild(self):
        # i = 0
        while self.wl:
            # print(f"counter: {i}, wl: {self.wl}")
            # i+=1
            todo = self.wl.copy()
            self.wl = []

            todo = { self.U.find(eclass) for eclass in todo }
            # print(f"Todo: {todo}")
            for eclass in todo:
                self.repair(eclass)


if __name__ == "__main__":
    egg = EGGraph()

    ### Add 7 individual classes

    for i in range(7):
        egg.U.new_id()
    print(egg.U)

    ### Perform some unions and inspect ufa

    unions = [(0,4), (1,2), (0,3), (4,2)]
    for (id1, id2) in unions:
        print(f"\negg.U.union({id1},{id2})")
        egg.U.union(id1,id2)
        print(egg.U)

    ### Create nodes and test customn __eq__ method

    n1 = nd("f", (0,4))
    print(n1)

    n2 = nd("f", (0,4))
    print(n1 == n2)

    ### Test nd.is_canonical and nd.canonicalize

    print(n2.is_canonical(egg.U))
    print(n2.canonicalize(egg.U).is_canonical(egg.U))

    ### Test EGGraph.lookup

    # Inconsistent manipulation since 0 is not a leader id
    egg.H[nd("f", (2,2))] = 0
    n3 = n2.canonicalize(egg.U)
    print(f"n3 = n2.canonicalize(egg.U) = {n3}")
    print(f"Lookup n3: {egg.lookup(n3)}")
    print(egg)

    ### Test EGGraph.add

    print(egg.add(nd("f", (0,0))))
    print(egg)

    print(egg.add(nd("g", (5,))))
    print(egg)

    ### Test EGGraph.merge

    print(f"egg.merge(0,1) = {egg.merge(0,1)}")
    print(egg)

    print(f"egg.merge(0,7) = {egg.merge(0,7)}")
    print(egg)

    ### Test EGGraph.parents

    print(f"egg.parents(0) = {egg.parents(0)}")
    print(f"egg.parents(6) = {egg.parents(6)}")

    ### Test EGGraph.rebuild

    print(f"egg.rebuild()")
    egg.rebuild()
    print(egg)
