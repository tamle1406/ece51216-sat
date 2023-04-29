
from pysat.formula import CNF
from pysat.solvers import Solver
from pysat.examples.genhard import PHP
from pysat.examples.genhard import CB
from pysat.examples.genhard import GT
from pysat.examples.genhard import PAR
from itertools import product
import random
import time
import cProfile

##Config variables
PRINT_SOLN = True
PRINT_DEBUG = True
INPUT_TYPE = "PHP" ##Either file or Random - Need to set VALIDATOR_MODE to 0
INPUT_FILE = "pigeon9.cnf" ##if Input is from a file
TESTCASE = 6

##Random testcase
NUM_VARS = 6
NUM_CLAUSES = 6
RAND_SEED = 216

##Validator inputs
VALIDATOR_SEED = 24
VALIDATOR_MAX_CLAUSES = 400
VALIDATOR_MAX_VARS = 400
VALIDATOR_MODE = 0
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
    #if (PRINT_SOLN): print(cnf.clauses)
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
        self.clauses = clauses.copy()
        self.decisions = decisions
        self.var = variable
        self.free_var = []
    
    def createNode(self,decision,variable):
        new_decisions = self.decisions.copy()
        new_decisions.update({self.var:decision})
        if decision:
            self.right = Node(self.clauses,self,new_decisions,variable)
            return self.right
        else:
            self.left = Node(self.clauses,self,new_decisions,variable)
            return self.left
    
    def createDummyNode(self,decision):
        if decision:
            self.right = Node([],self,None,None)
            return self.right
        else:
            self.left = Node([],self,None,None)
            return self.left
    
    def updateDummyNode(self):
        self.decisions={}
        self.clauses=[]
        return
    
    def removeNode(self):
        right=0
        if self==self.parent.right:
            right=1
        if right:
            Node.updateDummyNode(self)
        else:
            Node.updateDummyNode(self)
        return self.parent
    
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


def get_all_literals(clauses, decisions):
    literals=[]
    for each_clause in clauses:
        for each_literal in each_clause:
            if (not abs(each_literal) in literals) and (not abs(each_literal) in decisions): 
                literals.append(abs(each_literal))
    return literals

def count_literals(clauses,decisions,num_vars,var):
    #if var==78:
        #print("Here")
    free_vars=get_all_literals(clauses, decisions)
    if var!=None and var in free_vars: free_vars.remove(var)
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
    if (PRINT_DEBUG): print(decision_graph)
    return implied
# print("test unit_clause:")
# print(unit_clause([[1,2,5],[4],[-4]]))


def implied_clause(clause, decision, implied_decisions):
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
        # if value==None: value=implied_decisions.get(symbol)
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
            if (undecided_lit in implied_decisions) and implied_decisions.get(undecided_lit) == False:
                return [undecided_lit],{-1:True}
            implied.update({abs(undecided_lit):True})
        else:
            if (undecided_lit in implied_decisions) and implied_decisions.get(undecided_lit) == True:
                return [undecided_lit],{-1:True}
            implied.update({abs(undecided_lit):False})
    if unassigned_lit == 0:
        # print("Detected Conflict!")
        return [],{-2:True}
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
        if (not implied_key in implied_dict):
            implied_dict.update(implied)
    return conflict
#print("test conflict")
#print(check_conflict([[2, 4, 5], [1, 2]], {1:True, 4:True, 5:True}))

#TOdO Add logic to declare unsat if conflicting unit clauses exist

def check_sat(clauses):
    if len(clauses) == 0:
        print("Satisfiable")
    return


def check_unsat(clauses):
    for each_clause in clauses:
        if each_clause == []:
            return 1
    return 0

def get_forced_decisions(curr_node,decision_graph,free_var):
    # if not [8,55,-95] in curr_node.clauses:
    #     print(curr_node.var)
    while(1):
        #dummy_decisions = curr_node.decisions.copy()
        implied_decisions = {}
        implied_map = {}
        for clause in curr_node.clauses:
            unresolved,new_decisions = implied_clause(clause,curr_node.decisions,implied_decisions)
            if -1 in new_decisions:
                conflict_clause = implied_map.get(abs(unresolved[0])).copy()
                conflict_clause2 = clause.copy()
                conflict_clause2.remove(unresolved[0])
                for literal in conflict_clause2:
                    conflict_clause.append(literal)
                print("Conflict type 1 detected!",implied_map.get(abs(unresolved[0])),conflict_clause)
                return 1 #Conflict detected
            if -2 in new_decisions:
                #print("Conflict type 2 detected")
                return 1
            if (len(new_decisions)==1):
                #curr_node.decisions.update(new_decisions)
                implied_decisions.update(new_decisions)
                new_lit = [k for k,v in new_decisions.items()][0]
                implied_map.update({new_lit:unresolved})
                decision_graph.update({new_lit:[]})
                for var in unresolved:
                    decision_graph[var].append(new_lit)
        if implied_decisions=={}:
            break
        # for k in implied_decisions:
        #     if k in free_var: free_var.remove(k)
        #     if not k in curr_node.implied_var: curr_node.implied_var.append(k)
        curr_node.decisions.update(implied_decisions)
    # if len(curr_node.decisions)+len(free_var)!=99:
    #     #print("Vars missing")
    #     for k in free_var:
    #         if k in curr_node.decisions:
    #             print("")
    #if (PRINT_DEBUG): print(decision_graph)
    remove_sat_clauses(curr_node.clauses, curr_node.decisions)
    return 0

def dpll(cnf):
    all_clauses = cnf.clauses
    max_lit_num = cnf.nv
    num_vars = cnf.nv
    conflict_clauses=0
    conflict_clause_limit=int(0.2*len(all_clauses))
    conflict_clause_len_limit=4
    decision_graph = {}
    # Make assignment to clauses containing 1 literal in the original cnf
    forced_decision = unit_clause(all_clauses, decision_graph)
    if forced_decision == -1:
        print ("Unsatisfiable")
        if (PRINT_DEBUG): print("Returning from point 1")
        return 0
    # Creating dict containing no forced decision
    all_clauses = remove_sat_clauses(all_clauses, forced_decision)
    if len(all_clauses)==0:
        print("Satisfiable")
        if (PRINT_DEBUG): print("Returning from point 1")
        if (PRINT_SOLN): print(forced_decision)
        return 1
    if check_unsat(all_clauses):
        print("Unsatisfiable")
        if (PRINT_DEBUG): print("Returning from point 2")
        return 0
    free_var = get_all_literals(all_clauses, forced_decision) #remove unit clause literals
    if len(free_var)==0 and len(all_clauses)>0:
        print("Unsatisfiable")
        if (PRINT_DEBUG): print("Returning from point 2")
        return 0
    # if len(forced_decision)+len(free_var)!=5:
    #     print("vars missing")
    var_index = 0
    next_decision,var = count_literals(all_clauses,forced_decision,num_vars,None)
    # #free_var.remove(var)
    root = Node(all_clauses,None,forced_decision,var)
    curr_node = root
    get_forced_decisions(curr_node,decision_graph,free_var)
    remove_sat_clauses(curr_node.clauses, curr_node.decisions)
    # if len(curr_node.clauses)==0:
    #     print("Satisfiable")
    #     if (PRINT_DEBUG): print("Returning from point 1")
    #     if (PRINT_SOLN): print(forced_decision)
    #     return 1
    #Add variable selection and decision selection heuristic here
    while True:
        # if (not ([-1,-2] in curr_node.clauses)):
        #     print(var)
        #if curr_node.var==95:
            #print("var is 95")
            # Node.printTree(root)
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
            # free_var.extend(curr_node.implied_var)
            # if not curr_node.var in free_var: free_var.append(curr_node.var)
            #print("backtracking",curr_node.var)
            curr_node=Node.removeNode(curr_node)
            continue
        # free_var = get_free_var(curr_node)
        if not next_decision:
            if curr_node.left==None:
                #var_index+=1
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    #var = free_var[var_index]
                    if (curr_node.decisions.get(curr_node.var)==True):
                        Node.createDummyNode(curr_node,False)
                        continue
                    next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                    decision = False
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    #free_var.remove(var)
                    # get_forced_decisions(curr_node,decision_graph,free_var)
                    if (get_forced_decisions(curr_node,decision_graph,free_var)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        #free_var.extend(curr_node.implied_var)
                        # if not curr_node.var in free_var: free_var.append(curr_node.var)
                        #print("backtracking",curr_node.var)
                        curr_node=Node.removeNode(curr_node)
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 1")
                        print(remove_sat_clauses(all_clauses, curr_node.decisions))
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
                    # free_var.extend(curr_node.implied_var)
                    # if not curr_node.var in free_var: free_var.append(curr_node.var)
                    #print("backtracking",curr_node.var)
                    curr_node=Node.removeNode(curr_node)
                    #var_index-=1
                    continue
            if curr_node.right==None:
                #var_index+=1
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    #var = free_var[var_index]
                    if (curr_node.decisions.get(curr_node.var)==False):
                        Node.createDummyNode(curr_node,True)
                        continue
                    decision = True
                    next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    #free_var.remove(var)
                    #get_forced_decisions(curr_node,decision_graph,free_var)
                    if (get_forced_decisions(curr_node,decision_graph,free_var)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        # free_var.extend(curr_node.implied_var)
                        # if not curr_node.var in free_var: free_var.append(curr_node.var)
                        #print("backtracking",curr_node.var)
                        curr_node=Node.removeNode(curr_node)
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
                    # free_var.extend(curr_node.implied_var)
                    # if not curr_node.var in free_var: free_var.append(curr_node.var)
                    #print("backtracking",curr_node.var)
                    curr_node=Node.removeNode(curr_node)
                    continue
        else:
            if curr_node.right==None:
                #var_index+=1
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    #var = free_var[var_index]
                    if (curr_node.decisions.get(curr_node.var)==False):
                        Node.createDummyNode(curr_node,True)
                        continue
                    decision = True
                    next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    #free_var.remove(var)
                    #get_forced_decisions(curr_node,decision_graph,free_var)
                    if (get_forced_decisions(curr_node,decision_graph,free_var)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        # free_var.extend(curr_node.implied_var)
                        # if not curr_node.var in free_var: free_var.append(curr_node.var)
                        #print("backtracking",curr_node.var)
                        curr_node=Node.removeNode(curr_node)
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        print("Satisfiable")
                        if (PRINT_DEBUG): print("Returning from point 7")
                        print(remove_sat_clauses(all_clauses, curr_node.decisions))
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
                    # free_var.extend(curr_node.implied_var)
                    # if not curr_node.var in free_var: free_var.append(curr_node.var)
                    #print("backtracking",curr_node.var)
                    curr_node=Node.removeNode(curr_node)
                    continue
            if curr_node.left==None:
                #var_index+=1
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    #var = free_var[var_index]
                    if (curr_node.decisions.get(curr_node.var)==True):
                        Node.createDummyNode(curr_node,False)
                        continue
                    next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                    decision = False
                    decision_var = curr_node.var
                    decision_graph.update({decision_var:[]})
                    curr_node = Node.createNode(curr_node,decision,var)
                    #free_var.remove(var)
                    #get_forced_decisions(curr_node,decision_graph,free_var)
                    if (get_forced_decisions(curr_node,decision_graph,free_var)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        # free_var.extend(curr_node.implied_var)
                        # if not curr_node.var in free_var: free_var.append(curr_node.var)
                        #print("backtracking",curr_node.var)
                        curr_node=Node.removeNode(curr_node)
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
                    # free_var.extend(curr_node.implied_var)
                    # if not curr_node.var in free_var: free_var.append(curr_node.var)
                    #print("backtracking",curr_node.var)
                    curr_node=Node.removeNode(curr_node)
                    #var_index-=1
                    continue
            


def run_validator(num_cases):
    random.seed(VALIDATOR_SEED)
    cnf = CNF()
    fail = 0
    for i in range(0,num_cases):
        num_clauses = random.randint(5,VALIDATOR_MAX_CLAUSES)
        num_vars = random.randint(5, VALIDATOR_MAX_VARS)
        rand_seed = random.randint(0, 500)
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
            print("DPLL Config: \nRandom seed = %d\nNum clauses = %d\nNum variables = %d"% (RAND_SEED,NUM_CLAUSES,NUM_VARS))
            cnf = init_clauses(RAND_SEED,NUM_CLAUSES,NUM_VARS)
        elif INPUT_TYPE == "file":
            cnf = read_cnf_formula(INPUT_FILE)
            print("DPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_FILE,len(cnf.clauses),cnf.nv))
            #cnf = init_clauses(RAND_SEED,NUM_CLAUSES,NUM_VARS)
        elif INPUT_TYPE == "PHP":
            cnf = PHP(TESTCASE)
            print("DPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "GT":
            cnf = GT(TESTCASE)
            print("DPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "CB":
            cnf = CB(TESTCASE)
            print("DPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "PAR":
            cnf = PAR(TESTCASE)
            print("DPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        print("PYSAT Solver: ",end='')
        # cnf = CNF()
        # cnf.append([1,2,3])
        # cnf.append([1,-3])
        # cnf.append([2,4])
        # cnf.append([3,4,5])
        # cnf.append([-1,5])
        use_solver(cnf)
        #print(cnf.clauses)
        if TIMED_MODE: start = time.perf_counter()
        print("Our DPLL Solver: ",end='')
        dpll(cnf)
        if TIMED_MODE: 
            end = time.perf_counter()
            print("Our DPLL took %.3f ms time" % ((end-start)*1000))
    else:
        run_validator(500)

