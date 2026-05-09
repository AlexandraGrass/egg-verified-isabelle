# Example adapted from "Proof-Producing Congruence Closure"
# by Nieuwenhuis and Oliveras (Example 1)

from minimal_egg import *

egg = EGGraph()
print(egg)

print(f"egg.add(nd('a')) = {egg.add(nd('a'))}") # 0: a
print(egg)
print(f"egg.add(nd('b')) = {egg.add(nd('b'))}") # 1: b
print(egg)
print(f"egg.add(nd('d')) = {egg.add(nd('d'))}") # 2: d
print(egg)
print(f"egg.add(nd('f', (1,))) = {egg.add(nd('f', (1,)))}") # 3: f(b)
print(egg)
print(f"egg.add(nd('f', (2,))) = {egg.add(nd('f', (2,)))}") # 4: f(d)
print(egg)

# b = d
print(f"egg.merge(1,2) = {egg.merge(1,2)}")
print(egg)

# f(b) = d
print(f"egg.merge(3,2) = {egg.merge(3,2)}")
print(egg)

# f(d) = a
print(f"egg.merge(4,0) = {egg.merge(4,0)}")
print(egg)

# rebuild
print(f"egg.rebuild() = {egg.rebuild()}")
print(egg)
