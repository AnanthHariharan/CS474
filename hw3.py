from z3 import *

# Problem 1 (a) Formulas
# 1. \( \exists y. (y * y = 1 + 1) \)
y = Real('y')
problem_1a1 = Exists(y, y * y == 2)

# 2. \( \forall x. \exists y. (x + y = 0) \)
x = Real('x')
y = Real('y')
problem_1a2 = ForAll(x, Exists(y, x + y == 0))

# 3. \( \forall x. \forall y. (\neg(y = 0) \Rightarrow (\exists z. x * y = x + z)) \)
z = Real('z')
problem_1a3 = ForAll([x, y], Implies(y != 0, Exists(z, x * y == x + z)))

# 4. \( \exists x. \exists y. (x + 1 = 0 \wedge y \cdot y = x) \)
x = Real('x')
y = Real('y')
problem_1a4 = Exists([x, y], And(x + 1 == 0, y * y == x))

# Problem 1 (b) Greater-than relation
# Naturals
gt_N = ForAll([x, y], Exists(z, And(z > 0, y + z == x)))

# Reals
gt_R = ForAll([x, y], Exists(z, y + z * z == x))

# Rationals
a = Real('a')
b = Real('b')
gt_Q = ForAll([x, y], Exists([a, b], And(b != 0, y + (a / b) * (a / b) == x)))

# Problem 2 (a) Quantifier elimination
l1, u1, l2, u2, z, w = Reals('l1 u1 l2 u2 z w')
phi = ForAll(z, Or(
    Or(z <= l1, z >= u1, z <= l2, z >= u2),
    Exists(w, And(l1 < w, w < u1, l2 < w, w < u2, w != z))
))

# Problem 2 (b) Interval graph representation
l = [Real(f'l_{i}') for i in range(1, 5)]
r = [Real(f'r_{i}') for i in range(1, 5)]
constraints = [
    l[i] < r[i] for i in range(4)  # l_i < r_i
]

# Edge constraints
constraints += [
    And(r[0] > l[1], r[1] > l[0]),  # Edge (v1, v2)
    And(r[0] > l[2], r[2] > l[0]),  # Edge (v1, v3)
    And(r[1] > l[3], r[3] > l[1]),  # Edge (v2, v4)
    And(r[2] > l[3], r[3] > l[2])   # Edge (v3, v4)
]

# Non-edge constraints
constraints += [
    Or(r[0] <= l[3], r[3] <= l[0]),  # Non-edge (v1, v4)
    Or(r[1] <= l[2], r[2] <= l[1])   # Non-edge (v2, v3)
]

interval_graph_formula = And(constraints)

# Problem 3 Quantifier elimination
x = Real('x')
y = Real('y')
psi = ForAll(x, Exists(y, And(2 * y > 3 * x, 4 * y < 8 * x + 10)))

solver = Solver()


solver.add(problem_1a4)
print("Problem 1 (a)", solver.check())
solver.reset()

solver.add(gt_N)
print("Greater-than relation (Naturals):", solver.check())
solver.reset()

solver.add(gt_R)
print("Greater-than relation (Reals):", solver.check())
solver.reset()

solver.add(phi)
print("Problem 2 (a):", solver.check())
solver.reset()

solver.add(interval_graph_formula)
print("Problem 2 (b):", solver.check())
solver.reset()

solver.add(psi)
print("Problem 3:", solver.check())
