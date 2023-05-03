
from pysat.formula import CNF
import random
import time
import os
import sys

#For submission - remove examples, psutil, add shebang and sys.argv

##Config variables
PRINT_SOLN = False
PRINT_DEBUG = False
INPUT_TYPE = "file" ##Either file or Random - Need to set VALIDATOR_MODE to 0
INPUT_FILE = sys.argv[1] ##if Input is from a file
TESTCASE = 4

##Random testcase
NUM_VARS = 400
NUM_CLAUSES = 800
RAND_SEED = 409

##Validator inputs#23 has backtracking
VALIDATOR_SEED = 21
VALIDATOR_MAX_CLAUSES = 800
VALIDATOR_MAX_VARS = 500
VALIDATOR_MODE = 0
TIMED_MODE = 1

CHAFF=0 #Turn on Chaff (CDL needs to be off)
CDL=1 # Turn on CDL (Chaff needs to be off)


#Initiates a random CNF formula of num_clauses clauses with num_vars variables. The random number generator uses
#rand_seed as the seed - Used for testing
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

##Initiates a random cnf formula using init_clauses and writes it to a file named random.cnf(Used for testing)
def write_cnf_clauses(rand_seed,num_clauses,num_vars):
    cnf=CNF()
    cnf=init_clauses(rand_seed, num_clauses, num_vars)
    cnf.to_file("random.cnf")
    return

##Uses the Pysat library to read a dimacs file into a cnf formula
def read_cnf_formula(file_name):
    f1 = CNF(from_file=file_name)
    return f1


# Using the in-built solver from Pysat library to check and validate our answers
def use_solver(cnf_formula):
    if (TIMED_MODE): start = time.perf_counter()
    solver = Solver()
    solver.append_formula(cnf_formula)
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

#Function to pop from the front of a list
def popleft(l):
    if l==[]:
        return None
    else:
        temp=l[0]
        l.remove(l[0])
        return temp

#Function to push an item to the front of a list
def push(list_,item_):
    list_.insert(0,item_)
    return


#Class node used to define the nodes of the decision tree used in DPLL search and backtracking. 
#Each node has a variable, the decisions taken to reach until that point, the clauses left unsatisfied until that point, 
#the next variable that will be chosen and the next variable that will be chosen, and pointers to the children and the parent nodes
class Node:
    #Definition of the node object 
    def __init__(self,clauses,parent,decisions,variable):
        self.right = None
        self.left = None
        self.parent = parent
        self.clauses =[sublist[:] for sublist in clauses]
        self.decisions = decisions
        self.var = variable
        self.next_var = None
        self.next_decision = None
    
    #Function to create a new variable after taking a particular decision and choosing a particular variable 
    #as the next variable to decide
    def createNode(self,decision,variable):
        new_decisions = self.decisions.copy()
        new_decisions.update({self.var:decision})
        if decision:
            self.right = Node(self.clauses,self,new_decisions,variable)
            return self.right
        else:
            self.left = Node(self.clauses,self,new_decisions,variable)
            return self.left
    
    #Creates a dummy node- used in the extreme corner case where we cannot take a free decision at a node
    #because it is a part of the implied decisions due to the previously taken decision. 
    def createDummyNode(self,decision):
        if decision:
            self.right = Node([],self,None,None)
            return self.right
        else:
            self.left = Node([],self,None,None)
            return self.left
    
    #Used while backtracking to erase the clauses list and the decisions list of the backtracking node
    #to minimize memory usage
    def updateDummyNode(self):
        self.decisions={}
        self.clauses=[]
        return
    
    #Frees up memory from the backtracking node by cleaning up the clauses and the decisions taken- calls updateDummyNode
    def removeNode(self):
        right=0
        if self==self.parent.right:
            right=1
        if right:
            Node.updateDummyNode(self)
        else:
            Node.updateDummyNode(self)
        return self.parent
    
    #Prints a tree starting at the Root - used only for debug
    def printTree(root):
        if root.left != None:
            Node.printTree(root.left)
        print(root.var)
        if root.right != None:
            Node.printTree(root.right)
    

#Takes a decision hash table and a list of clauses and returns of list of clauses that are satisfied by
#the list of decisions
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
    return sat_clauses

#Removes the satisfied clauses from a list of clauses by using single_decision
def remove_sat_clauses(clauses, decisions):
    sat_clauses = single_decision(clauses, decisions)
    for each_sat_clause in sat_clauses:
        clauses.remove(each_sat_clause)
    return clauses

#Gets a list of all the symbols/variabls in a cnf formula clauses that still aren't decided upon
#Returns a list of symbols which can be used for a free decision
def get_all_literals(clauses, decisions):
    literals=[]
    for each_clause in clauses:
        for each_literal in each_clause:
            if (not abs(each_literal) in literals) and (not abs(each_literal) in decisions): 
                literals.append(abs(each_literal))
    return literals

##Used to iterate through all the literals in all the clauses and decide the next literal which will satisfy the 
#Most number of clauses in the formula. This feature has been turned off and returns a random variable and a decision
#Because the time taken was too high and this had to be done at each node.
def count_literals(clauses,decisions,num_vars,var):
    free_vars=get_all_literals(clauses, decisions)
    if var!=None and var in free_vars: free_vars.remove(var)
    if len(free_vars)==0:return True,-1
    return True,free_vars[0]
    count=[]
    abs_count=[]
    for i in range(0,num_vars):
        count.append(0)
    for each_clause in clauses:
        for literal in each_clause[0:2]:
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

#Gets a list of all the variables sorted according to the ones which will satisfy the most clauses
#Returns a list of variables that in a decreasing order of the number of clauses they will satisfy and a list of the corresponding
#Decisions. This feature has been turned off because of runtime increase.
def get_variable_ordering(all_clauses, decisions, num_vars):
    free_vars=get_all_literals(all_clauses, decisions)
    free_var_map=[]
    count=[]
    abs_count=[]
    decisions=[]
    for i in range(0,num_vars):
        count.append(0)
        if i+1 in free_vars:
            free_var_map.append(abs(i+1))
            decisions.append(False)
        else:
            free_var_map.append(-1)
            decisions.append(False)
    for each_clause in all_clauses:
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
    old_abs_count=[]
    for i in range(0,len(abs_count)):
        old_abs_count=abs_count
        for i in range(0,len(abs_count)-1):
            if abs_count[i]<abs_count[i+1]:
                temp=abs_count[i]
                abs_count[i]=abs_count[i+1]
                abs_count[i+1]=temp
                temp=count[i]
                count[i]=count[i+1]
                count[i+1]=temp
                temp=free_var_map[i]
                free_var_map[i]=free_var_map[i+1]
                free_var_map[i+1]=temp
    for i in range(0,len(abs_count)):
        if count[i]!=0:
            if (abs_count[i]/count[i])>0 and free_var_map[i]>0:
                decisions[i]=True
            if abs_count[i]==-1: break
    free_var_map=free_var_map[0:i]
    decisions=decisions[0:i]
    return decisions,free_var_map

##Takes a list of decisions implemented to reach the current node in the tree, 
#Then takes the list of variables and decisions returned by get_variable_ordering
#to return the next best variable to choose and its correspnding decision
#Has been turned off because of high runtime
def get_next_literal(curr_node,var_list,decision_list):
    if curr_node==None:
        return decision_list[0],var_list[0]
    for i in range(0,len(var_list)):
        if not var_list[i] in curr_node.decisions:
            return decision_list[i],var_list[i]
    return None,-1
    

#Takes a list of clauses and returns a list of implied decisions resulting due to all the unit clauses
#in the formula
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


##This function takes a clause, a list of free decisions and a list of implied decisions.
##Then it implements CHAFF or Conflict_driven learning depending on the state of the CHAFF and
##CDL global variables

#CHAFF- In chaff, this function checks if a decision has been made regarding the first two literals of the clause
#If one of them has been satisfied, the clause is satisfied and its removed. If one of the literals gets a non-satisfying assignment
#with respect to the clause, the literal gets removed so that the next literal becomes the watched literal. If both watched literals get 
#a non-satisfying assignment, both are removed. If the clause is left empty, it is an un-sat assignment. .

##Conflict-driven-learning - In this the function will assign values to the literals in the clause one-by-one. If all but one get a non-satisfying
#assignment, then the un-assigned variable is assigned an implied decision based on its sign. 
#If a conflicting decision exists in the implied decisions list, a conflict is detected, a new conflict clause is generated (in get_forced_decisions)
#and non-chronological backtracking is done. If all variables get a un-sat assignment regular backtracking is done
def implied_clause(clause, decision, implied_decisions):
    '''
    :param clause:
    :param decision: all the decisions made
    :return: return len 1 dictionary of the implied unit clause
    '''
    implied = {}
    unresolved_lits = []
    sat = 0
    if clause==[]:
        return [],{-2:True}
    clause0=(abs(clause[0]) in decision)
    if clause0: value0=decision.get(abs(clause[0]))
    if len(clause) == 1:
        if not clause0:
            clause0=(abs(clause[0]) in implied_decisions)
            if clause0: 
                value0=implied_decisions.get(abs(clause[0]))
                if (value0 and clause[0]<0) or (not value0 and clause[0]>0):
                    return [],{-2,True}
                else:
                    return [],{}
            else:
                if clause[0]>0:
                    return [],{abs(clause[0]):True}
                else:
                    return [],{abs(clause[0]):False}
        else:
            if ((value0 and clause[0]>0) or ((not value0) and clause[0]<0)):
                return [],{-3:True}
            else:
                return [],{-2:True}
            return [],{}
    unassigned_lit = len(clause)
    if (CHAFF):
        clause1=(abs(clause[1]) in decision)
        if clause1: value1=decision.get(abs(clause[1]))
        if (not clause0) and (not clause1):
            return [],{}
        elif ((clause0) and (not clause1)) or ((not clause0) and (clause1)):
            if clause0:
                if clause[0]>0 and value0:
                    return [],{-3:True}
                elif clause[0]<0 and (not value0):
                    return [],{-3:True}
                else:
                    clause.remove(clause[0])
            elif clause1:
                if clause[1]>0 and value1:
                    return [],{-3:True}
                elif clause[1]<0 and (not value1):
                    return [],{-3:True}
                else:
                    clause.remove(clause[1])
        else:
            remove=0
            if clause[0]>0 and value0:
                return [],{-3:True}
            elif clause[0]<0 and not value0:
                return [],{-3:True}
            if clause[1]>0 and value1:
                return [],{-3:True}
            elif clause[1]<0 and not value1:
                return [],{-3:True}
            else:
                clause.remove(clause[0])
                clause.remove(clause[0])
        if len(clause)==0:
            return [],{-2,True}
        if len(clause) == 1:
            clause0=(abs(clause[0]) in decision)
            if not clause0:
                clause0=(abs(clause[0]) in implied_decisions)
                if clause0: 
                    value0=implied_decisions.get(abs(clause[0]))
                    if (value0 and clause[0]<0) or (not value0 and clause[0]>0):
                        return [],{-2,True}
                    else:
                        return [],{}
                else:
                    if clause[0]>0:
                        return [],{abs(clause[0]):True}
                    else:
                        return [],{abs(clause[0]):False}
            else:
                value0=decision.get(abs(clause[0]))
                if ((value0 and clause[0]>0) or ((not value0) and clause[0]<0)):
                    return [],{-3:True}
                else:
                    return [],{-2:True}
                return [],{}
    for literal in clause:
        symbol = abs(literal)
        value = decision.get(symbol)
        if (value is not None):
            if literal > 0 and value or literal < 0 and not value:
                return [],{-3:True}
            else:
                unresolved_lits.append(literal)
                unassigned_lit -=1
        elif (value is None):
            undecided_lit = literal
    if unassigned_lit==1:
        if undecided_lit > 0:
            if (abs(undecided_lit) in implied_decisions) and implied_decisions.get(abs(undecided_lit)) == False:
                return [undecided_lit],{-1:True}
            implied.update({abs(undecided_lit):True})
        else:
            if (abs(undecided_lit) in implied_decisions) and implied_decisions.get(abs(undecided_lit)) == True:
                return [undecided_lit],{-1:True}
            implied.update({abs(undecided_lit):False})
    if unassigned_lit == 0:
        return [],{-2:True}
    if len(implied) == 1:
        return unresolved_lits,implied
    return [],{}



###Deprecated function to detect a conflict - not used
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

#Function to check if the no more unsatisfied clauses exist - declares satisfiability
def check_sat(clauses):
    if len(clauses) == 0:
        print("Satisfiable")
    return

#If some clause is empty this is because all the literals were deleted because of unsat assignments (only in chaff)
#declare unsat and backtrack
def check_unsat(clauses):
    for each_clause in clauses:
        if each_clause == []:
            return 1
    return 0

##Used only in conflict driven learning - takes a list of conflict clauses and a list of current decisions and sees 
#if any of the conflict-causing decisions exist in the list of decisions. If it exists, returns a 1 and the clause which triggered the
#conflict
def eval_conflict_clauses(clauses,decisions):
    for clause in clauses:
        sat_lit=len(clause)
        for lit in clause:
            val=decisions.get(abs(lit))
            if val!=None:
                if (lit>0 and not val) or (lit<0 and val):
                    sat_lit-=1
        if sat_lit==0: 
            return 1,clause
    return 0,[]

#Uses eval_conflict_clauses and implied_decisions to take a list of clauses in the current node, get a list of implied decisions,
#check for conflict in those decisions, check if a new conflict driven learning clause is generated and decide to do non-chronological 
#backtracking. The list of implied ddecisions is gotten iteratively until there is no more implied decisions left. Any satisfied clauses are
#removed and the implied decisions are added to the list of decisions in the current node.
def get_forced_decisions(curr_node,free_var):#Dont come in on first trial if forced decision !={}
    sat_clauses=[]
    global conflict_clauses,conflict_clause_limit
    while(1):
        implied_decisions = {}
        implied_map = {}
        if (CDL):
            ret,ret_clause=eval_conflict_clauses(conflict_clauses,curr_node.decisions)
            if(ret): return 2,ret_clause
        for clause in curr_node.clauses:
            if clause in sat_clauses: continue
            unresolved,new_decisions = implied_clause(clause,curr_node.decisions,implied_decisions)
            if -1 in new_decisions:
                conflict_clause = implied_map.get(abs(unresolved[0]))
                conflict_clause2 = clause.copy()
                conflict_clause2.remove(unresolved[0])
                for literal in conflict_clause2:
                    if -1*literal in conflict_clause:
                        conflict_clause2.remove(literal)
                        conflict_clause.remove(-1*literal)
                    elif not literal in conflict_clause:
                        conflict_clause.append(literal)
                return 2,conflict_clause #Conflict detected - new conflict clause and non-chronological backtracking
            if -2 in new_decisions:
                return 1,[]#conflict detected - backtrack
            if -3 in new_decisions:
                sat_clauses.append(clause)#clause satisfied
                continue
            if (len(new_decisions)==1):
                implied_decisions.update(new_decisions)
                new_lit = [k for k,v in new_decisions.items()][0] #Can be directly put into sat
                implied_map.update({new_lit:unresolved})
                sat_clauses.append(clause)
        if implied_decisions=={}:
            break
        curr_node.decisions.update(implied_decisions)
    for clause in sat_clauses:
        curr_node.clauses.remove(clause)
    return 0,[]

#gets a list of all the literals in the formula - only used for debug
def get_literal_map(all_clauses,num_vars):
    var_map=[]
    for i in range(0,len(all_clauses)):
        for lit in all_clauses[i]:
            var_map.append(i)
    return var_map

#non-chronological backtracking - given a conflict clause, this function will backtrack from the current node
#until we can take a decision that affects one of the variables in the conflict clause
def non_chrono_backtrack(curr_node,clause):
    if PRINT_DEBUG: print("backtracked from node %d to"%(curr_node.var),end='')
    i=0
    while(1):
        i+=1
        if curr_node.parent==None: 
            if PRINT_DEBUG: print(" %d,%d levels"%(curr_node.var,i))
            return i,curr_node
        curr_node=Node.removeNode(curr_node)
        for literal in clause:
            if curr_node.decisions.get(abs(literal))==None:
                if PRINT_DEBUG: print(" %d,%d levels"%(curr_node.var,i))
                return i,curr_node

##Prints the output in the required format
def printOutput(out,decisions):
    if out:
        print("RESULT: SAT")
        print("ASSIGNMENT: ",end='')
        for k in decisions:
            print("%d=%d "%(k,decisions.get(k)),end='')
    else:
        print("RESULT: UNSAT")
    return

##Main DPLL algorithm
def dpll(cnf):
    all_clauses = [sublist[:] for sublist in cnf.clauses]
    orig_clauses=[sublist[:] for sublist in all_clauses]
    global conflict_clauses_num
    global conflict_clause_limit
    global conflict_clause_len_limit
    global conflict_clauses
    conflict_clauses=[]
    conflict_clauses_num=0
    conflict_clause_limit=int(0.8*len(cnf.clauses))
    conflict_clause_len_limit=5
    max_lit_num = cnf.nv
    num_vars = cnf.nv
    # Make assignment to clauses containing 1 literal in the original cnf
    forced_decision = unit_clause(all_clauses)
    if forced_decision == -1:
        # print ("Unsatisfiable")
        # if (PRINT_DEBUG): print("Returning from point 1")
        printOutput(0,{})
        return 0
    # Creating dict containing no forced decision
    all_clauses = remove_sat_clauses(all_clauses, forced_decision)
    v_map = get_literal_map(all_clauses,num_vars)
    #Check if the forced decisions from the unit clauses satisfied the formula
    if len(all_clauses)==0:
        # print("Satisfiable")
        # if (PRINT_DEBUG): print("Returning from point 1")
        # print("Checking solution......")
        if (remove_sat_clauses(all_clauses, forced_decision)!=[]): print('Wrong solution!')
        printOutput(1,forced_decision)
        # if (PRINT_SOLN): print(forced_decision)
        return 1
    #check if there is a conflict because of the unit clauses - can declare unsat without going into the decision tree
    if check_unsat(all_clauses):
        # print("Unsatisfiable")
        # if (PRINT_DEBUG): print("Returning from point 2")
        printOutput(0,{})
        return 0
    free_var = get_all_literals(all_clauses, forced_decision) #get a list of all the free variables
    decision_list,var_list = get_variable_ordering(all_clauses,forced_decision,num_vars) #get the first variable and its decision
    if len(var_list)==0 and len(all_clauses)>0: #If no free variable exists - declare unsat 
        # print("Unsatisfiable")
        # if (PRINT_DEBUG): print("Returning from point 2")
        printOutput(0,{})
        return 0
    var_index = 0
    next_decision,var = count_literals(all_clauses,forced_decision,num_vars,None)
    root = Node(all_clauses,None,forced_decision,var)
    curr_node = root
    #Get the implied decisions using the list of unit_clauses decisions and remove sat clauses
    ret,conflict_clause=get_forced_decisions(curr_node,free_var)
    #if conflict was detected - unsatisfiable since we are at root node
    if ret: 
        # print("Unsatisfiable")
        # if (PRINT_DEBUG): print("Returning from point 2")
        printOutput(0,{})
        return 0
    #if all clauses satisfied - satisfiable and print the satisfying assignment
    if len(curr_node.clauses)==0:
        # print("Satisfiable")
        # if (PRINT_DEBUG): print("Returning from point 1.4")
        # print("Checking solution......")
        printOutput(1,curr_node.decisions)
        if (remove_sat_clauses(all_clauses, forced_decision)!=[]): print('Wrong solution!')
        # if (PRINT_SOLN): print(forced_decision)
        return 1
    #Before entering this while loop we have a next_decision which tells us the decision we will take 
    #next and the variable curr_node tells us the node we are on right now. If the decision we want to take
    #has already been taken we will take the other decision. For eg: if curr_node is 2 and next_decision is 
    #True, but the right child of 2 exists already, we take 2=False decision and proceed down the tree
    ###################################3
    #Once we get to a node, we will get the new list of implied clauses, remove the satisfied clauses
    #check if the formula is satisfied. If a conflict is detected, add the conflict clause to the list
    #of conflict clauses and backtrack. If an unsat has been discovered, backtrack to the parent node. 
    #The loop continues until we get a sat or an unsat.
    while True:
        if (curr_node.left!=None)and(curr_node.right!=None):
            if curr_node == root:
                # print("Unsatisfiable")
                # if (PRINT_DEBUG): print("Returning from point 3")
                printOutput(0,{})
                return 0
            if curr_node.decisions.get(curr_node.parent.var):
                next_decision = False
            else:
                next_decision = True
            curr_node=Node.removeNode(curr_node)
            continue
        if not next_decision:
            if curr_node.left==None:
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    if (curr_node.decisions.get(curr_node.var)==True):
                        Node.createDummyNode(curr_node,False) ##If the variable we are on is already in implied decisions- make dummy node and backtrack
                        continue
                    if curr_node.next_var==None:
                        next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var) #get the next decision and variables
                        if var==-1: #if no free variables left - backtrack
                            if curr_node.decisions.get(curr_node.parent.var):
                                next_decision = False
                            else:
                                next_decision = True
                            curr_node=Node.removeNode(curr_node)
                            continue
                        curr_node.next_var=var
                        curr_node.next_decision=next_decision
                    else:
                        next_decision=curr_node.next_decision
                        var=curr_node.next_var
                    decision = False
                    decision_var = curr_node.var
                    curr_node = Node.createNode(curr_node,decision,var)
                    ret,conflict_clause=get_forced_decisions(curr_node,free_var)
                    if (ret==2 and CDL==1):
                        levels,curr_node=non_chrono_backtrack(curr_node,conflict_clause)
                        if  conflict_clauses_num<conflict_clause_limit:
                            if not conflict_clause in conflict_clauses: 
                                conflict_clauses.append(conflict_clause)
                                conflict_clauses_num+=1
                        continue
                    elif (ret==1): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        continue
                    if (check_unsat(curr_node.clauses)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        #var_index-=1
                        continue
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 1.5")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 2")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 3")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    if (curr_node==root):
                        # print("Unsatisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 4")
                        printOutput(0,{})
                        return 0
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    curr_node=Node.removeNode(curr_node)
                    continue
            if curr_node.right==None:
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    if (curr_node.decisions.get(curr_node.var)==False):
                        Node.createDummyNode(curr_node,True)
                        continue
                    decision = True
                    if curr_node.next_var==None:
                        next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                        if var==-1:
                            if curr_node.decisions.get(curr_node.parent.var):
                                next_decision = False
                            else:
                                next_decision = True
                            curr_node=Node.removeNode(curr_node)
                            continue
                        curr_node.next_var=var
                        curr_node.next_decision=next_decision
                    else:
                        next_decision=curr_node.next_decision
                        var=curr_node.next_var
                    decision_var = curr_node.var
                    curr_node = Node.createNode(curr_node,decision,var)
                    ret,conflict_clause=get_forced_decisions(curr_node,free_var)
                    if (ret==2 and CDL==1):
                        levels,curr_node=non_chrono_backtrack(curr_node,conflict_clause)
                        if  conflict_clauses_num<conflict_clause_limit:
                            if not conflict_clause in conflict_clauses: 
                                conflict_clauses.append(conflict_clause)
                                conflict_clauses_num+=1
                        continue
                    elif (ret==1): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        continue
                    if (check_unsat(curr_node.clauses)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        continue
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 4")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 5")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 6")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    if (curr_node==root):
                        # print("Unsatisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 5")
                        printOutput(0,{})
                        return 0
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    curr_node=Node.removeNode(curr_node)
                    continue
        else:
            if curr_node.right==None:
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    if (curr_node.decisions.get(curr_node.var)==False):
                        Node.createDummyNode(curr_node,True)
                        continue
                    decision = True
                    if curr_node.next_var==None:
                        next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                        if var==-1:
                            if curr_node.decisions.get(curr_node.parent.var):
                                next_decision = False
                            else:
                                next_decision = True
                            curr_node=Node.removeNode(curr_node)
                            continue
                        curr_node.next_var=var
                        curr_node.next_decision=next_decision
                    else:
                        next_decision=curr_node.next_decision
                        var=curr_node.next_var
                    decision_var = curr_node.var
                    curr_node = Node.createNode(curr_node,decision,var)
                    ret,conflict_clause=get_forced_decisions(curr_node,free_var)
                    if (ret==2 and CDL==1):
                        levels,curr_node=non_chrono_backtrack(curr_node,conflict_clause)
                        if  conflict_clauses_num<conflict_clause_limit:
                            if not conflict_clause in conflict_clauses: 
                                conflict_clauses.append(conflict_clause)
                                conflict_clauses_num+=1
                        continue
                    elif (ret==1): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        continue
                    if (check_unsat(curr_node.clauses)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        continue
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 7")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 8")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 9")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        return 1
                    if (curr_node==root):
                        # print("Unsatisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 6")
                        printOutput(0,{})
                        return 0
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    curr_node=Node.removeNode(curr_node)
                    continue
            if curr_node.left==None:
                if len(get_all_literals(curr_node.clauses, curr_node.decisions))>0:
                    if (curr_node.decisions.get(curr_node.var)==True):
                        Node.createDummyNode(curr_node,False)
                        continue
                    if curr_node.next_var==None:
                        next_decision,var=count_literals(curr_node.clauses,curr_node.decisions,num_vars,curr_node.var)
                        if var==-1:
                            if curr_node.decisions.get(curr_node.parent.var):
                                next_decision = False
                            else:
                                next_decision = True
                            curr_node=Node.removeNode(curr_node)
                            continue
                        curr_node.next_var=var
                        curr_node.next_decision=next_decision
                    else:
                        next_decision=curr_node.next_decision
                        var=curr_node.next_var
                    decision = False
                    decision_var = curr_node.var
                    curr_node = Node.createNode(curr_node,decision,var)
                    ret,conflict_clause=get_forced_decisions(curr_node,free_var)
                    if (ret==2 and CDL==1):
                        levels,curr_node=non_chrono_backtrack(curr_node,conflict_clause)
                        if  conflict_clauses_num<conflict_clause_limit:
                            if not conflict_clause in conflict_clauses: 
                                conflict_clauses.append(conflict_clause)
                                conflict_clauses_num+=1
                        continue
                    elif (ret==1): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        curr_node=Node.removeNode(curr_node)
                        #var_index-=1
                        continue
                    if (check_unsat(curr_node.clauses)): #Checks for conflict 
                        if curr_node.decisions.get(curr_node.parent.var):
                            next_decision = False
                        else:
                            next_decision = True
                        # free_var.append(curr_node.var)
                        curr_node=Node.removeNode(curr_node)
                        #var_index-=1
                        continue
                    #curr_node.decisions.update(unit_clause(curr_node.clauses))
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 10")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    continue
                else:
                    clauses_copy = [sublist[:] for sublist in curr_node.clauses]
                    curr_node.decisions.update({curr_node.var:False})
                    remove_sat_clauses(clauses_copy,curr_node.decisions)
                    if len(clauses_copy) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 11")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    curr_node.decisions.update({curr_node.var:True})
                    remove_sat_clauses(curr_node.clauses,curr_node.decisions)
                    if len(curr_node.clauses) == 0:
                        # print("Satisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 12")
                        # print("Checking solution......")
                        printOutput(1,curr_node.decisions)
                        if (remove_sat_clauses(all_clauses, curr_node.decisions)!=[]): print('Wrong solution!')
                        # if (PRINT_SOLN): print(curr_node.decisions)
                        # Node.printTree(root)
                        return 1
                    if (curr_node==root):
                        # print("Unsatisfiable")
                        # if (PRINT_DEBUG): print("Returning from point 7")
                        printOutput(0,{})
                        return 0
                    if curr_node.decisions.get(curr_node.parent.var):
                        next_decision = False
                    else:
                        next_decision = True
                    curr_node=Node.removeNode(curr_node)
                    #var_index-=1
                    continue
            

##Validator function to generate num_cases number of random CNF
#formulae and compare our answer with the cnf solver from Pysat
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
        if use_solver(cnf) != dpll(cnf):
            print("Test Case Failed")
            fail = 1
    if not fail:
        print("All Testcases Passed! :)")
    else:
        print("Some Testcases Failed! :(")
    return

#A function used to run a bunch of testcases - not used. 
def run_all_cases():
    with open('all_testcases.txt','w') as sys.stdout:
        for i in range(40,51):
            f='uf250-0'+str(i)+'.cnf'
            print('Reading file '+f)
            cnf=read_cnf_formula(f)
            start = time.perf_counter()
            dpll(cnf)
            end = time.perf_counter()
            print('Done file '+f+' in time %.3f ms'%(end-start)/1000)
        for i in range(40,51):
            f='uuf250-0'+str(i)+'.cnf'
            print('Reading file '+f)
            cnf=read_cnf_formula(f)
            start = time.perf_counter()
            dpll(cnf)
            end = time.perf_counter()
            print('Done file '+f+' in time %.3f ms'%(end-start)/1000)

if __name__ == '__main__':
    if not VALIDATOR_MODE: #A list of different input types
        if INPUT_TYPE == "random":
            cnf = CNF()
            if PRINT_DEBUG: print("\nDPLL Config: \nRandom seed = %d\nNum clauses = %d\nNum variables = %d"% (RAND_SEED,NUM_CLAUSES,NUM_VARS))
            cnf = init_clauses(RAND_SEED,NUM_CLAUSES,NUM_VARS)
        elif INPUT_TYPE == "file":
            cnf = read_cnf_formula(INPUT_FILE)
            if PRINT_DEBUG: print("\nDPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_FILE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "PHP":
            cnf = PHP(TESTCASE)
            if PRINT_DEBUG: print("\nDPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "GT":
            cnf = GT(TESTCASE)
            if PRINT_DEBUG: print("\nDPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "CB":
            cnf = CB(TESTCASE)
            if PRINT_DEBUG: print("\nDPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        elif INPUT_TYPE == "PAR":
            cnf = PAR(TESTCASE)
            if PRINT_DEBUG: print("\nDPLL Config: \nInput file = %s\nNum clauses = %d\nNum variables = %d"% (INPUT_TYPE,len(cnf.clauses),cnf.nv))
        dpll(cnf) #Solve and print our dpll answer with conflict driven learning on
    else:
        run_validator(500)

