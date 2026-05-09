from minimal_egg import *

egg = EGGraph()

# g(f(x))
print(f"egg.add(nd('x')) = {egg.add(nd('x'))}")
print(egg)
print(f"egg.add(nd('f', (0,))) = {egg.add(nd('f', (0,)))}")
print(egg)
print(f"egg.add(nd('g', (1,))) = {egg.add(nd('g', (1,)))}")
print(egg)

# g(f(y))
print(f"egg.add(nd('y')) = {egg.add(nd('y'))}")
print(egg)
print(f"egg.add(nd('f', (3,))) = {egg.add(nd('f', (3,)))}")
print(egg)
print(f"egg.add(nd('g', (4,))) = {egg.add(nd('g', (4,)))}")
print(egg)

# merge('x', y')
print(f"egg.merge(0,3) = {egg.merge(0,3)}")
print(egg)

# rebuild
print(f"egg.rebuild() = {egg.rebuild()}")
print(egg)
