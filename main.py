
from pysat.formula import CNF
from pysat.solvers import Solver
from itertools import product
import random
import time

##Config variables
PRINT_SOLN = False
PRINT_DEBUG = False
INPUT_TYPE = "file" ##Either file or Random - Need to set VALIDATOR_MODE to 0
INPUT_FILE = "random.cnf" ##if Input is from a file

##Random testcase
NUM_VARS = 5
NUM_CLAUSES = 5
RAND_SEED = 93

##Validator inputs
VALIDATOR_SEED = 27
VALIDATOR_MAX_CLAUSES = 300
VALIDATOR_MAX_VARS = 400
VALIDATOR_MODE = 1
TIMED_MODE = 1

### TEST CASE ###
# Create an empty CNF formula
### Change the seed for another cnf formula
##Unsatisfiable test case : seed 25, nv 40, clauses 70

# Add 10 random clauses with up to 5 literals each
'''for i in range(10):
    literals = [v for v in range(1, 6)]  # Variables are named 1, 2, ..., 5
    clause = [random.sample(literals) * (-1 if random.random() > 0.5 else 1) for _ in range(random.randint(1, 5))]  # Randomly select literals to include
    cnf.append(clause)'''
#Adjust the number of variable and number of clauses for the test case


def init_clauses(rand_seed,num_clauses,num_vars):
    cnf = CNF()
    random.seed(rand_seed)
    for i in range(num_clauses):
        clause = []
        while len(clause) == 0 or len(set(map(abs, clause))) < len(clause) or 0 in clause:
            # Generate random literals with no duplicates or 0
            clause = [random.choice([-1, 1]) * random.randint(1, num_vars) for j in range(random.randint(1, num_vars))]
            clause.sort(key=abs)
        cnf.append(clause)
    if (PRINT_SOLN): print(cnf.clauses)
    return cnf
# for i in [[1, 4], [-1, -4], [-4], [4], [-1, -2, 3, -4], [-2, 3, -4]]:
#     cnf.append(i)
#print(cnf.clauses)

def write_cnf_clauses(rand_seed,num_clauses,num_vars):
    cnf=CNF()
    cnf=init_clauses(rand_seed, num_clauses, num_vars)
    cnf.to_file("random.cnf")
    return

def read_cnf_formula(file_name):
    f1 = CNF(from_file=file_name)
    return f1
# Save the resulting formula in DIMACS format
# open("random.cnf", "w") as f:
#    f.write(cnf.to_file("random.cnf"))

# implementing pysat's sat solver
def use_solver(cnf_formula):
    if (TIMED_MODE): start = time.perf_counter()
    solver = Solver()
    solver.append_formula(cnf_formula)
    # start = time.perf_counter()
    if solver.solve():
        # Print the satisfying assignment of variables
        print("Satisfiable")
        if (PRINT_SOLN): print(solver.get_model())
        if (TIMED_MODE and not VALIDATOR_MODE):
            end = time.perf_counter()
            print("Solver took %.3f ms time" % ((end-start)*1000))
        return 1
    else:
        # Print that the formula is unsatisfiable
        print("Unsatisfiable")
        if (TIMED_MODE and not VALIDATOR_MODE):
            end = time.perf_counter()
            print("Solver took %.3f ms time" % ((end-start)*1000))
        return 0
#print("printing cnf.clauses: ")
#print(cnf.clauses)
#print(cnf.nv)

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
            #elif value is not None and (literal < 0 and value or literal > 0 and not value):
                #each_clause.remove(literal)
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

def count_literals(clauses,free_vars,num_vars):
    count=[]
    abs_count=[]
    for i in range(0,num_vars):
        count.append(0)
    for each_clause in clauses:
        for literal in each_clause:
            if literal>0:
                count[abs(literal)-1]+=1
            else:
                count[abs(literal)-1]-=1
    for i in range(0,len(count)):
        if i+1 in free_vars:
            abs_count.append(abs(count[i]))
        else:
            abs_count.append(-1)
    max_ = 0
    max_index = 0
    for i in range(0,len(abs_count)):
        if abs_count[i] > max_:
            max_ = abs_count[i]
            max_index = i
    if max_!=0:
        if int(max_/count[max_index])>0: 
            return True,max_index+1
        else: 
            return False,max_index+1
    else:
        for i in range(0,len(abs_count)):
            if abs_count[i]==0: break
        return True,i+1

def get_next_literal(counts,num_vars):
    m=max(counts)
    for index in range(0,len(counts)):
        if counts[index] == m: break
    counts[index] = 0
    if index>num_vars-1: 
        return (index-num_vars+1)*(-1)
    else: 
        return index+1


def unit_clause(clauses, decision_graph):
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
                decision_graph.update({symbol:[]})
            else:
                if symbol in implied and implied.get(symbol) == True: return -1
                implied.update({symbol: False})
                decision_graph.update({symbol:[]})
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
    unresolved_lits = []
    sat = 0
    if len(clause) == 1:
        if not (clause[0] in decision):
            if clause[0]>0:
                return [],{abs(clause[0]):True}
            else:
                return [],{abs(clause[0]):False}
        else:
            return [],{}
    unassigned_lit = len(clause) 
    for literal in clause:
        symbol = abs(literal)
        value = decision.get(symbol)
        if (value is not None):
            if literal > 0 and value or literal < 0 and not value:
                return [],{}
            else:
                unresolved_lits.append(abs(literal))
                unassigned_lit -=1
        elif (value is None):
            undecided_lit = literal
        # elif (value is None and unassigned_lit == 1):
        #     if literal > 0:
        #         implied.update({symbol: True})
        #     else:
        #         implied.update({symbol: False})
    if unassigned_lit==1:
        if undecided_lit > 0:
            # if (undecided_lit in all_decisions) and all_decisions.get(undecided_lit) == False:
            #     return [],{-1:True}
            implied.update({abs(undecided_lit):True})
        else:
            # if (undecided_lit in all_decisions) and all_decisions.get(undecided_lit) == True:
                # return [],{-1:True}
            implied.update({abs(undecided_lit):False})
    if unassigned_lit == 0:
        print("Detected Conflict!")
        return [],{-1:True}
    if len(implied) == 1:
        return unresolved_lits,implied
    return [],{}
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

def get_all_literals(clauses, decisions):
    literals=[]
    for each_clause in clauses:
        for each_literal in each_clause:
            if abs(each_literal) not in literals and abs(each_literal) not in decisions: 
                literals.append(abs(each_literal))
    return literals

def check_unsat(clauses):
    for each_clause in clauses:
        if each_clause == []:
            return 1
    return 0

def get_forced_decisions(curr_node,decision_graph):
    while(1):
        dummy_decisions = curr_node.decisions.copy()
        for clause in curr_node.clauses:
            unresolved,new_decisions = implied_clause(clause,curr_node.decisions)
            if -1 in new_decisions:
                return 1 #Conflict detected
            if (len(new_decisions)==1):
                curr_node.decisions.update(new_decisions)
                new_lit = [k for k,v in new_decisions.items()][0]
                decision_graph.update({new_lit:[]})
                for var in unresolved:
                    decision_graph[var].append(new_lit)
        if curr_node.decisions==dummy_decisions:
            break
    if (PRINT_DEBUG): print(decision_graph)
    remove_sat_clauses(curr_node.clauses, curr_node.decisions)
    return 0

def dpll(cnf,num_vars):
    all_clauses = cnf.clauses
    max_lit_num = cnf.nv
    decision_graph = {}
    # Make assignment to clauses containing 1 literal in the original cnf
    forced_decision = unit_clause(all_clauses, decision_graph)
    if forced_decision == -1:
        print ("Unsatisfiable")
        if (PRINT_DEBUG): print("Returning from point 1")
        return 0
    # Creating dict containing no forced decision
    all_clauses = remove_sat_clauses(all_clauses, forced_decision)
    if check_unsat(all_clauses):
        print("Unsatisfiable")
        if (PRINT_DEBUG): print("Returning from point 2")
        return 0
    free_var = get_all_literals(all_clauses, forced_decision) #remove unit clause literals
    var_index = 0
    next_decision,var = count_literals(all_clauses,free_var,num_vars)
    free_var.remove(var)
    root = Node(all_clauses,None,forced_decision,var)
    curr_node = root
    #Add variable selection and decision selection heuristic here
    while True:
        if (curr_node.left!=None)and(curr_node.right!=None):
            if curr_node == root:
                print("Unsatisfiable")
                if (PRINT_DEBUG): print("Returning from point 3")
                return 0
            #var_index-=1
            if curr_node.decisions.get(curr_node.parent.var):
                next_decision = False
            else:
                next_decision = True
            free_var.append(curr_node.var)
            curr_node=curr_node.parent
        if not next_decision:
            if curr_node.left==None:
                #var_index+=1
                if len(free_var)>0:
                    #var = free_var[var_index]
                    next_decision,var=count_literals(curr_node.clauses,free_var,num_vars)
                    decision = False
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    free_var.remove(var)
                    # get_forced_decisions(curr_node,decision_graph)
                    if (get_forced_decisions(curr_node,decision_graph)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        free_var.append(curr_node.var)
                        curr_node=curr_node.parent
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 1")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 2")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 3")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    if (curr_node==root):
                        print("Unsatisfiable")
                        if (PRINT_DEBUG): print("Returning from point 4")
                        return 0
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    free_var.append(curr_node.var)
                    curr_node=curr_node.parent
                    #var_index-=1
                    continue
            if curr_node.right==None:
                #var_index+=1
                if len(free_var)>0:
                    #var = free_var[var_index]
                    decision = True
                    next_decision,var=count_literals(curr_node.clauses,free_var,num_vars)
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    free_var.remove(var)
                    #get_forced_decisions(curr_node,decision_graph)
                    if (get_forced_decisions(curr_node,decision_graph)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        free_var.append(curr_node.var)
                        curr_node=curr_node.parent
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 4")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 5")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 6")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    if (curr_node==root):
                        print("Unsatisfiable")
                        if (PRINT_DEBUG): print("Returning from point 5")
                        return 0
                    #var_index-=1
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    free_var.append(curr_node.var)
                    curr_node=curr_node.parent
                    continue
        else:
            if curr_node.right==None:
                #var_index+=1
                if len(free_var)>0:
                    #var = free_var[var_index]
                    decision = True
                    next_decision,var=count_literals(curr_node.clauses,free_var,num_vars)
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    free_var.remove(var)
                    #get_forced_decisions(curr_node,decision_graph)
                    if (get_forced_decisions(curr_node,decision_graph)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        free_var.append(curr_node.var)
                        curr_node=curr_node.parent
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 7")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 8")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 9")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    if (curr_node==root):
                        print("Unsatisfiable")
                        if (PRINT_DEBUG): print("Returning from point 6")
                        return 0
                    #var_index-=1
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    free_var.append(curr_node.var)
                    curr_node=curr_node.parent
                    continue
            if curr_node.left==None:
                #var_index+=1
                if len(free_var)>0:
                    #var = free_var[var_index]
                    next_decision,var=count_literals(curr_node.clauses,free_var,num_vars)
                    decision = False
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    free_var.remove(var)
                    #get_forced_decisions(curr_node,decision_graph)
                    if (get_forced_decisions(curr_node,decision_graph)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        free_var.append(curr_node.var)
                        curr_node=curr_node.parent
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 10")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 11")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 12")
                        if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    if (curr_node==root):
                        print("Unsatisfiable")
                        if (PRINT_DEBUG): print("Returning from point 7")
                        return 0
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    free_var.append(curr_node.var)
                    curr_node=curr_node.parent
                    #var_index-=1
                    continue
            


def run_validator(num_cases):
    random.seed(VALIDATOR_SEED)
    cnf = CNF()
    fail = 0
    for i in range(0,num_cases):
        num_clauses = random.randint(10,VALIDATOR_MAX_CLAUSES)
        num_vars = random.randint(10, VALIDATOR_MAX_VARS)
        rand_seed = random.randint(0, 100)
        print("Random testcase #%d:%d/%d/%d"%(i,rand_seed,num_clauses,num_vars))
        cnf = init_clauses(rand_seed, num_clauses, num_vars)
        if use_solver(cnf) != dpll(cnf,num_vars):
            print("Test Case Failed")
            fail = 1
    if not fail:
        print("All Testcases Passed! :)")
    else:
        print("Some Testcases Failed! :(")
    return


if __name__ == '__main__':
    if not VALIDATOR_MODE:
        if INPUT_TYPE == "random":
            cnf = CNF()
            if PRINT_DEBUG: print("DPLL Config: \nRandom seed = %d\nNum clauses = %d\nNum variables = %d"% (RAND_SEED,NUM_CLAUSES,NUM_VARS))
            cnf = init_clauses(RAND_SEED,NUM_CLAUSES,NUM_VARS)
        elif INPUT_TYPE == "file":
            cnf = read_cnf_formula(INPUT_FILE)
            if PRINT_DEBUG: print("DPLL Config: \nRandom seed = %d\nNum clauses = %d\nNum variables = %d"% (RAND_SEED,NUM_CLAUSES,NUM_VARS))
            cnf = init_clauses(RAND_SEED,NUM_CLAUSES,NUM_VARS)
        print("PYSAT Solver: ",end='')
        use_solver(cnf)
        if TIMED_MODE: start = time.perf_counter()
        print("Our DPLL Solver: ",end='')
        dpll(cnf,NUM_VARS)
        if TIMED_MODE: 
            end = time.perf_counter()
            print("Our DPLL took %.3f ms time" % ((end-start)*1000))
    else:
        run_validator(500)

