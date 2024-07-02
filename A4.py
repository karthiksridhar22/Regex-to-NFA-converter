#Checking if a particular string is accepted by a regex by building an NFA
#Using Thompson construction for Regex to NFA conversion: https://swtch.com/~rsc/regexp/regexp1.html
#Using Shunting-Yard algorithm for infix to postfix 
import json

def add_concat(regex):
    operators = ['*', '.', '+', '(', ')']
    l = len(regex)
    res = ""
    for i in range(l - 1):
        res += regex[i]
        if regex[i] not in operators and (regex[i + 1] not in operators or regex[i + 1] == '('):
          res += '.'
        if regex[i] == ')' and regex[i + 1] == '(':
            res += '.'
        if regex[i] == '*' and regex[i + 1] == '(':
            res += '.'
        if regex[i] == '*' and regex[i + 1] not in operators:
            res += '.'
        if regex[i] == ')' and regex[i + 1] not in operators:
            res += '.'

    res += regex[l - 1]
    return res


#using shunting-yard algorithm: https://en.wikipedia.org/wiki/Shunting_yard_algorithm#The_algorithm_in_detail
def re2post(input):
  out_q = "" # postfix output 
  op_st = [] # operations stack

  precedence = {'*' : 3, '.': 2, '+': 1}

  for i in input:
    if (i == "0" or i =="1" or i =="e"): #if input is a terminal character
      out_q += (i)
    elif i == "(": #if we encounter open parenthesis
      op_st.append(i)
    elif i == ")": #if we encounter closed parenthesis 
      temp = op_st.pop()
      while temp != "(": #pop every element to the output queue until (
        out_q += (temp)
        temp = op_st.pop()
    elif i == "*" or i =="." or i == "+": 
        #as long as stack is non empty, top element is not ( and top element has greater precedence do:
        while(len(op_st) != 0 and op_st[-1] != "(" and precedence[op_st[-1]] > precedence[i]): 
          out_q += (op_st.pop())
        op_st.append(i)
    
  while(len(op_st) != 0):
    out_q += (op_st.pop())

  return out_q

# postfix = re2post("0.(1+0)*.1")

# print(postfix)
        

# concat = add_concat("0*1010*")
# print(re2post("0*.1.0.1.0*"))


#state class
class state(object): 
  name_counter = 0 #state names
  state_stack = [] #storing all states
  def __init__(self, is_start, is_accept):
    self.name = "Q" + str(state.name_counter)
    state.name_counter += 1
    self.is_start = is_start
    self.is_accept = is_accept
    #store transitions on each character
    self.transitions = {"0": [], "1": [], "e": []}
    
    self.state_stack.append(self)

  def add_transition(self, char, next_state):
    if next_state not in self.transitions[char]:
      self.transitions[char].append(next_state)

  def print_state(self):
    print(self.name, "\n")
    if self.is_start == True:
      print("It is the start state \n")
    else:
      print("It is not the start state \n")
    if self.is_accept == True:
      print("It is an accept state \n")
    else: 
      print("It is not an accept state \n")

    print(self.transitions)

# s = state(False, True)
# s1 = state(True, False)
# s1.add_transition("0", s)

# s1.print_state()
# s.print_state()

class fragment(object):
  def __init__(self, start_state, end_states):
    self.start_state = start_state
    self.end_states = end_states
  
  def join_frags(self, e2): 
    for end_state in self.end_states: 
      #use epsilon arrows to connect all end states from e1 to e2
      end_state.add_transition("e", e2.start_state) 


def post2nfa(postfix):
  nfa_stack = [] 

  for i in postfix:
    if i == "0" or i == "1" or i =="e": #case for literals. create frag with 2 states and push
      s = state(is_start=True, is_accept=False)
      s1 = state(False, True)
      s.add_transition(i, s1)
      f = fragment(s, [s1])
      nfa_stack.append(f)

    elif i == ".": #case for concat, pop two and push joined fragment
      e2 = nfa_stack.pop()
      e1 = nfa_stack.pop()
      e1.join_frags(e2)
      e = fragment(e1.start_state, e2.end_states)
      nfa_stack.append(e)


    elif i == "+": #pop two, create new state with epsilon transitions to both
      e2 = nfa_stack.pop()
      e1 = nfa_stack.pop()

      s = state(is_start=True, is_accept=False)
      s.add_transition("e", e1.start_state)
      s.add_transition("e", e2.start_state)

      f = fragment(s, e1.end_states + e2.end_states)
      nfa_stack.append(f)

    elif i == "*": 
      #kleene closure, new state that is an accept state- all final states from popped fragment point to s and s points to start state of fragment 
      e = nfa_stack.pop()
      s = state(is_start=True, is_accept= True)

      s.add_transition("e", e.start_state)

      for end_state in e.end_states: 
        end_state.add_transition("e", s)
      
      f = fragment(s, [s])
      nfa_stack.append(f)

  if nfa_stack and len(nfa_stack) > 1:
    print("NFA stack error, more than one fragment at the end. Please check if the postfix expression is valid")
    return 
  else: 
    final_state = state(False, True)
    f = nfa_stack[-1]
    # for end_state in f.end_states: 
    #   end_state.add_transition("e", final_state)

    return f

def ep_closure(active_states): 
  end = active_states
  for state in active_states:
    end += state.transitions["e"]
  return end
  
def nfa_transition(active_states, a): 
  next_states = []
  for state in active_states:
    if len(state.transitions[a]) != 0:
      next_states += state.transitions[a]   
  return next_states

def make_unique(my_list):
  unique_list = []
  [unique_list.append(i) for i in my_list if i not in unique_list]
  return unique_list

def nfa_simulate(nfa, w):
  active_states = [nfa.start_state] + ep_closure([nfa.start_state])

  for a in w: 
    next_states = ep_closure(nfa_transition(active_states, a))
    next_states = make_unique(next_states)
    active_states = next_states

  accept = False
  for state in active_states:
    if state in nfa.end_states:
      accept = True
      return w, "is a valid string in L"
  
  if accept == False:
    return "NOT A VALID STRING"
      
# def output_nfa(f):
def output_nfa(nfa, regex):
  with open('nfa.json', 'w') as f:
      operators = ['*', '.', '+', '(', ')']
      states = []
      a = []
      for state in nfa.start_state.state_stack:
        states.append(state.name)
      data = {"Q": states}
      data["S"] = nfa.start_state.name
      data["A"] = []
      for c in regex: 
        if c not in operators:
          a.append(c)
          a = make_unique(a)
          a.append("e")
          data["A"] = a
      data["F"] = []
      for state in nfa.end_states:
        data["F"].append(state.name)
      data["T"] = {}
      for state in nfa.start_state.state_stack:
        data["T"][str(state.name)] = {}
        for c in a: 
          x = state.transitions[c]
          if len(x) == 0:
            data["T"][str(state.name)][c] = []
          else:
            y = []
            for s in x:
              y.append(s.name)
            data["T"][str(state.name)][c] = y

      json.dump(data, f, indent=3)

def main():
  regex = input("Enter a regex (+: union, *: kleene closure): \n")
  regex = regex.strip()
  b = add_concat(regex)
  postfix = re2post(b)
  nfa = post2nfa(postfix)
  output_nfa(nfa, b)
  print("NFA has been outputted to nfa.json")
  w = input("Enter a string to check if it is accepted by the regex: ")
  print(nfa_simulate(nfa, w))

main()
