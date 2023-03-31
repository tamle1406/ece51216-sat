
from pysat.formula import CNF
from pysat.solvers import Solver
from itertools import product
import random
### TEST CASE ###
# Create an empty CNF formula
cnf = CNF()
### Change the seed for another cnf formula
##Unsatisfiable test case : seed 25, nv 40, clauses 70
random.seed(23)

# Add 10 random clauses with up to 5 literals each
'''for i in range(10):
    literals = [v for v in range(1, 6)]  # Variables are named 1, 2, ..., 5
    clause = [random.sample(literals) * (-1 if random.random() > 0.5 else 1) for _ in range(random.randint(1, 5))]  # Randomly select literals to include
    cnf.append(clause)'''
#Adjust the number of variable and number of clauses for the test case
num_vars = 6
num_clauses = 7
for i in range(num_clauses):
    clause = []
    while len(clause) == 0 or len(set(map(abs, clause))) < len(clause) or 0 in clause:
        # Generate random literals with no duplicates or 0
        clause = [random.choice([-1, 1]) * random.randint(1, num_vars) for j in range(random.randint(1, num_vars))]
        clause.sort(key=abs)
    cnf.append(clause)
# for i in [[1, 4], [-1, -4], [-4], [4], [-1, -2, 3, -4], [-2, 3, -4]]:
#     cnf.append(i)
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
            return self.right
        else:
            self.left = Node(self.clauses,self,new_decisions,variable)
            return self.left
    
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

# def count_literals(clauses):
#     count=[]
#     for i in range(0,num_vars):
#         count.append(0)
#     for each_clause in clauses:
#         for literal in each_clause:
#             if literal>0:
#                 count[literal-1]+=1
#             else:
#                 count[abs(literal)+num_vars-1]+=1
#     return count

def get_next_literal(counts):
    m=max(counts)
    for index in range(0,len(counts)):
        if counts[index] == m: break
    counts[index] = 0
    if index>num_vars-1: 
        return (index-num_vars+1)*(-1)
    else: 
        return index+1


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
                if symbol in implied and implied.get(symbol) == False: return -1
                implied.update({symbol: True})
            else:
                if symbol in implied and implied.get(symbol) == True: return -1
                implied.update({symbol: False})
    return implied
# print("test unit_clause:")
# print(unit_clause([[1,2,5],[4],[-4]]))


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
        if (value is not None):
            if literal > 0 and value or literal < 0 and not value:
                break
            else:
                unassigned_lit -=1
        elif (value is None and unassigned_lit == 1):
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

def check_sat(clauses):
    if len(clauses) == 0:
        print("Satisfiable")
    return



def dpll(cnf):
    sat = False
        # Get all clauses and the # of literals in the original cnf
    all_clauses = cnf.clauses
    max_lit_num = cnf.nv
    # Make assignment to clauses containing 1 literal in the original cnf
    forced_decision = unit_clause(cnf.clauses)
    if forced_decision == -1:
        print ("Not Satisfiable")
        return
    # Creating dict containing no forced decisions
    free_var = []
    for i in range(1, max_lit_num+1):
        if i not in forced_decision:
            free_var.append(i)
    # Creating a dict containing all decisions
    all_decisions = {}
    all_decisions.update(forced_decision)
    # Remove all clauses that are satisfied  by this assignment
    all_clauses = remove_sat_clauses(all_clauses, forced_decision)

    # count = count_literals(all_clauses)
    # var = get_next_literal(count)
    # var_list = []

    root = Node(all_clauses,None,forced_decision,free_var[0])
    # decision = True if var>0 else False
    # var_list.append(abs(var))
    curr_node = root
    var_index = 0
    # while abs(var) in var_list:
    #     var = get_next_literal(count) # find better way to do var list
    #Add variable selection and decision selection heuristic here
    while True:
        if curr_node.left==None:
            var_index+=1
            if var_index < len(free_var):
                var = free_var[var_index]
                decision = False
                curr_node = Node.createNode(curr_node,decision,var)
                for clause in curr_node.clauses:
                    curr_node.decisions.update(implied_clause(clause,curr_node.decisions))
                remove_sat_clauses(curr_node.clauses, curr_node.decisions)
                if len(curr_node.clauses) == 0:
                    print("Satisfiable")
                    print(curr_node.decisions)
                    # Node.printTree(root)
                    return
            else:
                clauses_copy = curr_node.clauses
                curr_node.decisions.update({curr_node.var:False})
                remove_sat_clauses(clauses_copy,curr_node.decisions)
                if len(clauses_copy) == 0:
                    print("Satisfiable")
                    print(curr_node.decisions)
                    # Node.printTree(root)
                    return
                curr_node.decisions.update({curr_node.var:True})
                remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                if len(curr_node.clauses) == 0:
                    print("Satisfiable")
                    print(curr_node.decisions)
                    # Node.printTree(root)
                    return
                if (curr_node==root):
                    print("Not Satisfiable")
                    return
                curr_node = curr_node.parent
                var_index-=1
                continue
        if curr_node.right==None:
            var_index+=1
            if var_index < len(free_var):
                var = free_var[var_index]
                decision = True
                curr_node = Node.createNode(curr_node,decision,var)
                for clause in curr_node.clauses:
                    curr_node.decisions.update(implied_clause(clause,curr_node.decisions))
                remove_sat_clauses(curr_node.clauses, curr_node.decisions)
                if len(curr_node.clauses) == 0:
                    print("Satisfiable")
                    print(curr_node.decisions)
                    # Node.printTree(root)
                    return
            else:
                clauses_copy = curr_node.clauses
                curr_node.decisions.update({curr_node.var:False})
                remove_sat_clauses(clauses_copy,curr_node.decisions)
                if len(clauses_copy) == 0:
                    print("Satisfiable")
                    print(curr_node.decisions)
                    # Node.printTree(root)
                    return
                curr_node.decisions.update({curr_node.var:True})
                remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                if len(curr_node.clauses) == 0:
                    print("Satisfiable")
                    print(curr_node.decisions)
                    # Node.printTree(root)
                    return
                if (curr_node==root):
                    print("Not Satisfiable")
                    return
                var_index-=1
                curr_node = curr_node.parent
                continue
        if curr_node == root:
            print("Not Satisfiable")
            return
        var_index-=1
        curr_node=curr_node.parent

            
            


        


    #creating an assignment pattern of FFF, FFT, FTF, FTT,... (given the len is 3)
    # for pattern in product([False, True], repeat=len(free_decision)):
    #     free_decision = dict(zip(keys, pattern))
    #     #if (check_conflict(all_clauses, all_decisions)):
    #         #continue
    #     all_clauses = remove_sat_clauses(all_clauses, free_decision)
    #     all_decisions.update(free_decision)


    #     if len(all_clauses) == 0:
    #         print("Satisfiable")
    #         print(all_decisions)
    #         break
    if (len(all_clauses) != 0):
        print("not satisfiable")
    return
dpll(cnf)
