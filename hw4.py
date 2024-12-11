from z3 import *
# TASK I
e = Int('e')  # Identity 
c = Int('c')  # Candidate
x = Int('x')  # Variable for group elements

f = Function('f', IntSort(), IntSort(), IntSort())

identity_axiom = And(f(e, c) == c, f(c, e) == c)

neg_phi = And(
    ForAll([x], And(f(x, c) == x, f(c, x) == x)), 
    e != c  
)

solver = Solver()

solver.add(identity_axiom)
solver.add(neg_phi)
print(solver.check())

e = Int('e') 
c = Int('c') 
d = Int('d') 

f = Function('f', IntSort(), IntSort(), IntSort())


axiom_1 = f(c, d) == e

axiom_2 = f(d, c) == e

negation_formula = And(
    axiom_1,       
    axiom_2,       
    (c==d),
    Not(d == c)    
)

solver = Solver()

solver.add(negation_formula)
print(solver.check())
