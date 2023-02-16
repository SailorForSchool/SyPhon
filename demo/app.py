#!/usr/bin/env python3
from flask import Flask, abort, jsonify, request
from demo import phonosynth

from demo.flag import *

app = Flask(__name__, static_url_path='')

@app.route('/')
def handle_homepage():
  return app.send_static_file('index.html')

@app.route('/api/infer_rule', methods=['POST'])
def handle_infer_rule():
  if not request.json or not 'wordStems' in request.json:
    abort(400)

  if (H_INFER):
    print("In app.handle_infer_rule\n")
  words = []
  for stem in request.json['wordStems']:
    words.append((stem['underlyingForm'], stem['realization']))

  if (H_INFER_V):
    print ("calling infer_rule with the following:\n\n", words, "\n")
  return jsonify(infer_rule(words))

def format_features(features):
  symbol = phonosynth.FEATURES_TO_SYMBOL.get(frozenset(features.items()))
  if symbol:
    return symbol
  else:
    return [{'feature': feature, 'positive': value == '+'} for feature, value in features.items()]

def infer_rule(words):
  if (INFER):
    print("In app.infer_rule\n")
  data = phonosynth.parse(words)
  change = phonosynth.infer_change(data)
  left, phone, right = phonosynth.infer_rule(data, change)

  if(INFER_V):
    print("left: ", left)
    print("phone: ", phone)
    print("right: ", right, "\n")
  
  return {
    'phone': format_features(phone),
    'change': format_features(change),
    'context': {
      'left': format_features(left),
      'right': format_features(right)
    }
  }
