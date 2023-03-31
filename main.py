
from pysat.formula import CNF
from pysat.solvers import Solver
from itertools import product
import random
### TEST CASE ###
# Create an empty CNF formula
cnf = CNF()
### Change the seed for another cnf formula
random.seed(4)

# Add 10 random clauses with up to 5 literals each
'''for i in range(10):
    literals = [v for v in range(1, 6)]  # Variables are named 1, 2, ..., 5
    clause = [random.sample(literals) * (-1 if random.random() > 0.5 else 1) for _ in range(random.randint(1, 5))]  # Randomly select literals to include
    cnf.append(clause)'''
#Adjust the number of variable and number of clauses for the test case
num_vars = 5
num_clauses = 6
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

# implementing pysat's sat solver
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

print("====NOT TEST CASES====")

class Node:
    def __init__(self,clauses,parent,decisions,variable):
        self.right = None
        self.left = None
        self.parent = parent
        self.clauses = clauses
        self.decisions = decisions
        self.var = variable
    
    def createNode(self,decision,variable):
        new_decisions = self.decisions.copy()
        new_decisions.update({self.var:decision})
        if decision:
            self.right = Node(self.clauses,self,new_decisions,variable)
        else:
            self.left = Node(self.clauses,self,new_decisions,variable)
    
    def removeNode(Node):
        del Node
    
    def printTree(root):
        if root.left != None:
            Node.printTree(root.left)
        print(root.var)
        if root.right != None:
            Node.printTree(root.right)
    


def single_decision(clauses, decision):
    '''
    :param cnf:
    :param decision: a dictionary
    :return: a list without the satisfied clauses made by the single decision
    '''
    sat_clauses = []
    for each_clause in clauses:

        for literal in each_clause:
            # Evaluate the literal in the model
            symbol = abs(literal)
            value = decision.get(symbol)
            if value is not None and (literal > 0 and value or literal < 0 and not value):
                # If the literal is positive and its value is True, or
                # if the literal is negative and its value is False, the clause is true
                sat_clauses.append(each_clause)
                break
    #for clauses in sat_clauses:
        #clauses_copy.remove(clauses)
    return sat_clauses


def remove_sat_clauses(clauses, decisions):
    for key, value in decisions.items():
        sat_clauses = single_decision(clauses, {key:value})
        for each_sat_clause in sat_clauses:
            clauses.remove(each_sat_clause)
    return clauses

#print(remove_sat_clauses([[-3, 5], [-4], [-2, 4, 5]], {4:True, 3:False}))

def unit_clause(clauses):
    '''
    :param clauses: all clauses
    :return: dictionary containing the decisions for the unit clauses containing 1 literal
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
#print(implied_clause([1,2,5], {1:True, 2:True}))

def check_conflict(clauses, decisions):
    '''
    :param clauses: clauses in the cnf (with sat clauses removed)
    :param decisions: dict of all decisions
    :return: boolean if there is a conflict in any clauses
    '''
    conflict = False
    implied_dict = {}
    for each_clause in clauses:
        # Skip if there is no implied unit clauses
        if len(implied_clause(each_clause, decisions)) == 0:
            continue

        implied = implied_clause(each_clause, decisions)
        implied_key = list(implied.keys())[0]
        if (implied_key in implied_dict):
            value_in_dict = implied_dict[implied_key]
            if value_in_dict != implied[implied_key]:

                conflict = True
                break
            else:
                continue
        if (implied_key not in implied_dict):
            implied_dict.update(implied)
    return conflict
#print("test conflict")
#print(check_conflict([[2, 4, 5], [1, 2]], {1:True, 4:True, 5:True}))

#TOdO Add logic to declare unsat if conflicting unit clauses exist

def dpll(cnf):
    sat = False
    # Get all clauses and the # of literals in the original cnf
    all_clauses = cnf.clauses
    max_lit_num = cnf.nv
    # Make assignment to clauses containing 1 literal in the original cnf
    forced_decision = unit_clause(cnf.clauses)
    # Creating dict containing no forced decisions
    free_decision = {}
    for i in range(1, max_lit_num):
        if i not in forced_decision:
            free_decision.update({i: False})
    # Creating a dict containing all decisions
    all_decisions = {}
    all_decisions.update(forced_decision)
    all_decisions.update(free_decision)
    # Remove all clauses that are satisfied  by this assignment
    all_clauses = remove_sat_clauses(all_clauses, forced_decision)

    keys = sorted(list(free_decision.keys()))

    #creating an assignment pattern of FFF, FFT, FTF, FTT,... (given the len is 3)
    for pattern in product([False, True], repeat=len(free_decision)):
        free_decision = dict(zip(keys, pattern))
        #if (check_conflict(all_clauses, all_decisions)):
            #continue
        all_clauses = remove_sat_clauses(all_clauses, free_decision)
        all_decisions.update(free_decision)


        if len(all_clauses) == 0:
            print("Satisfiable")
            print(all_decisions)
            break
    if (len(all_clauses) != 0):
        print("not satisfiable")
    return
dpll(cnf)
