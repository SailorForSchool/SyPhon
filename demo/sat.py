import z3
from demo.flag import *

def infer_rule(data, change_rule, feature_sizes):
  if (S_INFERR):
    print("In sat.infer_rule\n")
  triples_changed = []
  if (S_INFERR):
    print("For each triple, apply_change is called.\n")
  for (l, c, r), new_c in data:
    changed_c = apply_change(c, change_rule)
    if changed_c !=  c:
      triples_changed.append(((l, c, r), c != new_c))

  # DEBUG OUTPUT: in features not phoneme
  if (S_INFER_V):
    print("changed triples: \n")
    for (le, t, ri), b in triples_changed:
      if (b):
        print("features list - triple: ", le, t, ri)
  # DEBUG END

  rule = query_z3(triples_changed, feature_sizes)
  return rule

POSITIONS = ['left', 'center', 'right']

def to_ident(feature, position):
  return f'|{feature} {position}|'

def shared_features(triples):
  shared = None
  for triple in triples:
    features = set()
    for i, phone in enumerate(triple):
      features |= {((feature, POSITIONS[i]), value) for feature, value in phone.items() if value != '0'}
    if shared == None:
      shared = features
    else:
      shared &= features
  return dict(shared)

def apply_change(features, rule):

  new_features = dict(features)
  new_features.update(rule)

  # DEBUG OUTPUT: TODO could output the feature changed?
  if (S_APCH):
    print("In sat.apply_change\n")
  if (S_APCH_V):
    print("rule", rule, "\n")
  # END DBEUG

  return new_features

def infer_change(pairs):

  # DEBuG STATEMENT
  if(S_INFER):
    print("In sat.infer_change\n")
  # END DEBUG

  solver = z3.Optimize()
  included_features = {}
  positive_features = {}
  for old, new in pairs:
    conjunction = []
    for feature, value in old.items():
      feature_included = z3.Bool(f'|{feature} included|')
      feature_positive = z3.Bool(f'|{feature} positive|')
      included_features[feature_included] = feature
      positive_features[feature] = feature_positive
      conjunction.append(z3.If(
        z3.And(feature_included, value != '0'),
        feature_positive == (new[feature] == '+'),
        new[feature] == value
      ))
    solver.add(z3.And(*conjunction))

  for var in included_features.keys():
    solver.add_soft(z3.Not(var))

  if solver.check() == z3.sat:
    rule = {}
    model = solver.model()
    for ident, feature in included_features.items():
      if model[ident]:
        positive_feature = positive_features[feature]
        rule[feature] = '+' if model[positive_feature] else '-'
    return rule
  else:
    print('unsat')
    
    
def query_z3(triples_changed, feature_sizes):
  shared = shared_features([triple for triple, changed in triples_changed if changed])
  idents_to_features = {to_ident(feature, position): (feature, position) for feature, position in shared.keys()}
  
  solver = z3.Optimize()

  soft_assertions = []
  position_weights = {
    'left': 1000,
    'center': 0,
    'right': 1000
  }
  for ident, (feature, position) in idents_to_features.items():
    # hmmm?
    solver.add_soft(z3.Not(z3.Bool(ident)), weight=10000 + position_weights[position] + feature_sizes[(feature, shared[(feature, position)])])
  
  debug = []
  # for every triple...
  for triple, changed in triples_changed:
    conjunction = []


    # for every phone in triple...
    for i, phone in enumerate(triple):
      # for every feature in phone...
      for feature in phone.keys():


        # record position of phone in triple
        position = POSITIONS[i]
        # if the feature, position is sharded among triples
        if (feature, position) in shared:


          # format for solver
          ident = to_ident(feature, position)


          # mark if included (+ or -) BOOL
          included = phone[feature] != '0'
          # mark if the feature has matches the value in the shared changed triples
          matches = phone[feature] == shared[(feature, position)]



          # (feature_position_pair AND included) => matches
          conjunction.append(z3.Implies(z3.And(z3.Bool(ident), included), matches))

          # TODO DEBUG
          if (S_QUERY):
            if ((not matches) and (not changed) and included):
              if ident + " (no rule)" not in debug:
                print (ident, " may be included (no rule application)")
                debug.append(ident + " (no rule)")
            if ((not matches) and changed and included):
              if ident + " (rule)" not in debug:
                print (ident, " must NOT be included (rule application)")
                debug.append(ident + " (rule)")
          # END DEBUG

    # per triple, check if there was a change
    if conjunction != []:
      
      # if change -> add all conjunction as constraint
      if changed:
        solver.add(z3.And(*conjunction))

      # if not changed -> add conjunction as NOT constraint
      else:
        # encoding counter examples - explicitly the implicational relationship must be false because
        # the context of the "rule" if the feature position pair is included is present and so
        # the lack of change implies that it is explicitly NOT in the rule
        solver.add(z3.Not(z3.And(*conjunction)))


  if solver.check() == z3.sat:
    rule = (dict(), dict(), dict())
    model = solver.model()
    for ident in model:
      if z3.is_true(model[ident]):
        feature, position = idents_to_features[str(ident)]
        rule[POSITIONS.index(position)][feature] = shared[(feature, position)]
        print ("rule: ", rule)
    return rule
  else:
    print('unsat')

