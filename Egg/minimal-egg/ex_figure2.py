# Example adapted from "egg: Fast and Extensible Equality Saturation"
# by Willsey et al. (Figure 2)

from minimal_egg import *

egg = EGGraph()

# Initial e-graph contains (a × 2)/2
print(f"egg.add(nd('a')) = {egg.add(nd('a'))}")
print(egg)
print(f"egg.add(nd('2')) = {egg.add(nd('2'))}")
print(egg)
print(f"egg.add(nd('*', (0,1))) = {egg.add(nd('*', (0,1)))}")
print(egg)
print(f"egg.add(nd('/', (2,1))) = {egg.add(nd('/', (2,1)))}")
print(egg)

# Test redundant add
print(f"egg.add(nd('a')) = {egg.add(nd('a'))}")
print(egg)      # Nothing happens :)

# Applying rewrite x × 2 → x ≪ 1
print(f"egg.add(nd('1')) = {egg.add(nd('1'))}")
print(f"egg.add(nd('<<', (0,4))) = {egg.add(nd('<<', (0,4)))}")
print(egg)
print(f"egg.merge(2,5) = {egg.merge(2,5)}")
print(egg)
print(f"egg.rebuild() = {egg.rebuild()}") # only canonicalizes entries in H
print(egg)
print(f"egg.parents(1) = {egg.parents(1)}\n")

# Applying rewrite (x × y)/z → x × (y/z)
print(f"egg.add(nd('/', (1,1))) = {egg.add(nd('/', (1,1)))}")
print(f"egg.add(nd('*', (0,6))) = {egg.add(nd('*', (0,6)))}")
print(egg)
print(f"egg.merge(3,7) = {egg.merge(3,7)}")
print(egg)
print(f"egg.rebuild() = {egg.rebuild()}") # does nothing
print(egg)

# Applying rewrites x/x → 1 and 1 × x → x (should be x*1 !!!)
print(f"egg.merge(6,4) = {egg.merge(6,4)}")
print(egg)
print(f"egg.merge(7,0) = {egg.merge(7,0)}")
print(egg)
print(f"egg.rebuild() = {egg.rebuild()}")
# [/](5, 1): 3 could be [/](5, 1): 0
# [/](1, 1): 6 could be [/](1, 1): 4
# PROBLEM: Rebuilding only ever canonicalizes parents, never siblings
print(egg)
