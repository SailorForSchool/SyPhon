import csv, itertools, unicodedata
from demo import sat
from demo.flag import *

SYMBOL_NORMALIZATION = {
  'g': 'ɡ'
}

SYMBOL_MODIFIERS = {
  ':': {'long': '+'},
  'ʰ': {'s.g.': '+'},
  'ʻ': {'c.g.': '+'},
  '̈': {'front': '-', 'back': '-'},
  '̧': {}
}

def read_features(filename):
  symbols_to_features = {
    '#': {
      'word boundary': '+'
    }
  }
  
  with open(filename, 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
      symbol = unicodedata.normalize('NFD', row.pop('symbol'))
      symbol = SYMBOL_NORMALIZATION.get(symbol, symbol)
      row['word boundary'] = '-'
      row['long'] = '-'
      symbols_to_features[symbol] = dict(row)

  return symbols_to_features

def get_sizes(symbols):
  feature_sizes = {}
  total_features = 0
  for symbol in symbols:
    total_features += 1
    for feature, value in symbol.items():
      feature_sizes[(feature, value)] = feature_sizes.get((feature, value), 0) + 1
  return {f: total_features - size for f, size in feature_sizes.items()}

SYMBOL_TO_FEATURES = read_features('../datasets/riggle.csv')
FEATURES_TO_SYMBOL = {frozenset(features.items()): symbol for symbol, features in SYMBOL_TO_FEATURES.items()}
FEATURE_SIZES = get_sizes(SYMBOL_TO_FEATURES.values())

def triples(it):
  left, center = itertools.tee(it)
  next(center)
  center, right = itertools.tee(center)
  next(right)
  return zip(left, center, right)

def parse_grapheme(grapheme):
  symbol = ''
  features = None
  for char in list(grapheme):
    grapheme.pop(0)
    symbol += char
    normalized_symbol = SYMBOL_NORMALIZATION.get(symbol, symbol)
    if normalized_symbol in SYMBOL_TO_FEATURES:
      symbol = normalized_symbol
      break
  for char in list(grapheme):
    normalized_symbol = SYMBOL_NORMALIZATION.get(symbol + char, symbol + char)
    if normalized_symbol not in SYMBOL_TO_FEATURES:
      break
    symbol = normalized_symbol
    grapheme.pop(0)
  # added by Shraddha
  # print(symbol)
  features = dict(SYMBOL_TO_FEATURES[symbol])
  for modifier in grapheme:
    features.update(SYMBOL_MODIFIERS[modifier])
  return features

def parse_word(word):
  graphemes = []
  for char in unicodedata.normalize('NFD', word):
    if char in SYMBOL_MODIFIERS.keys():
      graphemes[-1].append(char)
    else:
      graphemes.append([char])
  return [parse_grapheme(grapheme) for grapheme in graphemes]

def parse(words):

  # DEBUG STATEMENT
  if (PARSE):
    print ("In phonosynth.parse\n")
  # END DEBUG

  data = []
  for underlying_form, realization in words:
    underlying_features = parse_word('#' + underlying_form + '#')
    realized_features = parse_word(realization)
    for i, triple in enumerate(triples(underlying_features)):
      data.append((triple, realized_features[i]))

  # DEBUG OUTPUT
  if (PARSE_V):
    print("parsed triples:\n")
    for (l, t, r), _ in data:
      print("triple: ", FEATURES_TO_SYMBOL.get(frozenset(l.items())), " ", FEATURES_TO_SYMBOL.get(frozenset(t.items())), " ",  FEATURES_TO_SYMBOL.get(frozenset(r.items())))
    print ("\n")
  # END DEBUG

  return data

def infer_change(data):

  # DEBUG STATEMENT
  if (P_CHANGE):
    print ("In phonosynth.infer_change\n")
  # END DEBUG

  changed = [(old, new) for (_, old, _), new in data if old != new]

  # DEBUG OUTPUT
  if (P_CHANGE_V):
    print ("changed data:\n",)
    for (o, n) in changed:
      print("change: ", FEATURES_TO_SYMBOL.get(frozenset(o.items())), " -> ", FEATURES_TO_SYMBOL.get(frozenset(n.items())))
    print ("\n")
  # END DEBUG

  return sat.infer_change(changed)

def infer_rule(data, change_rule):
  return sat.infer_rule(data, change_rule, FEATURE_SIZES)
