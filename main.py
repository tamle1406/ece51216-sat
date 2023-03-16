
from pysat.formula import CNF
from pysat.solvers import Solver
import random

# Create an empty CNF formula
cnf = CNF()
random.seed(3)

# Add 10 random clauses with up to 5 literals each
'''for i in range(10):
    literals = [v for v in range(1, 6)]  # Variables are named 1, 2, ..., 5
    clause = [random.sample(literals) * (-1 if random.random() > 0.5 else 1) for _ in range(random.randint(1, 5))]  # Randomly select literals to include
    cnf.append(clause)'''

num_vars = 5
num_clauses = 10
for i in range(num_clauses):
    clause = []
    while len(clause) == 0 or len(set(map(abs, clause))) < len(clause) or 0 in clause:
        # Generate random literals with no duplicates or 0
        clause = [random.choice([-1, 1]) * random.randint(1, num_vars) for j in range(random.randint(1, num_vars))]
        clause.sort(key=abs)
    cnf.append(clause)
print(cnf.clauses)

# Save the resulting formula in DIMACS format
# open("random.cnf", "w") as f:
#    f.write(cnf.to_file("random.cnf"))

solver = Solver()
solver.append_formula(cnf)
if solver.solve():
    # Print the satisfying assignment of variables
    print("Satisfying assignment:")
    print(solver.get_model())
else:
    # Print that the formula is unsatisfiable
    print("Unsatisfiable")

#print("printing cnf.clauses: ")
#print(cnf.clauses)
#print(cnf.nv)


"""
###############################
##### CODE FOR SAT SOLVER #####
###############################
"""

'''def evaluate_clause(clause, model):
    """
    Evaluate a clause in a given model.
    """
    for literal in clause:
        # Evaluate the literal in the model
        symbol = abs(literal)
        value = model.get(symbol)
        if value is None:
            # If the symbol is not in the model, the literal is undefined
            return None
        elif literal > 0 and value or literal < 0 and not value:
            # If the literal is positive and its value is True, or
            # if the literal is negative and its value is False, the clause is true
            return True
    # If none of the literals are true, the clause is false

    return False
print(evaluate_clause([4, 4, -5], {1:False, 2:False, 3:True, 4:False, 5:False}))'''


'''def evaluate_cnf(cnf, model):
    for clause in cnf:
        if (not evaluate_clause(clause, model)):
            return False
    return True

#print(evaluate_cnf(cnf.clauses, {1:False, 2:False, 3:True, 4:False, 5:False}))

def search_tree(cnf):
    var = cnf.nv
    model = {1:False, 2:False, 3:False, 4:False, 5:False}

    if (not evaluate_cnf(cnf, model)):
        model[2] = True
        print(model)
    return None
#print(type({1:False, 2:True}))
search_tree(cnf)'''


def single_decision(cnf, decision):
    '''
    :param cnf:
    :param decision: a dictionary
    :return: a list without the satisfied clauses made by the single decision
    '''
    clauses_copy = cnf.clauses
    sat_clauses = []
    for clauses in cnf.clauses:

        for literal in clauses:
            # Evaluate the literal in the model
            symbol = abs(literal)
            value = decision.get(symbol)
            if value is not None and (literal > 0 and value or literal < 0 and not value):
                # If the literal is positive and its value is True, or
                # if the literal is negative and its value is False, the clause is true
                sat_clauses.append(clauses)
                break
    for clauses in sat_clauses:
        clauses_copy.remove(clauses)
    return clauses_copy

def unit_clause(clauses):
    '''
    :param clauses: all clauses
    :return: dictionary containing the decisions for the unit clauses
    '''
    implied = {}
    for each_clause in clauses:
        if len(each_clause) == 1:
            symbol = abs(each_clause[0])
            if each_clause[0] > 0:
                implied.update({symbol: True})
            else:
                implied.update({symbol: False})
    return implied

def implied_clause(clause, decision):
    '''
    :param clause:
    :param decision: all the decisions made
    :return: return len 1 dictionary of the implied unit clause
    '''
    implied = {}
    unassigned_lit = len(clause)
    for literal in clause:
        symbol = abs(literal)
        value = decision.get(symbol)
        if (value is None):
            if literal > 0:
                implied.update({symbol: True})
            else:
                implied.update({symbol: False})
    if len(implied) == 1:
        return implied
    return {}
#print("test implied_clause:")
#print(implied_clause([1,2,5], {1:False}))

i = 0
def dpll(cnf):
    global i
    decision = {}

    return

#dpll(cnf)
#print(single_decision(cnf, {1:True}))
#print(remove_sat_clauses(cnf, sat_clauses_one_decision(cnf, {1:True})))
#test = {1:False}
#test.update({2:False})
#print(test)