#region imports
from AlgorithmImports import *
#endregion
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from scipy.signal import argrelextrema
from collections import deque
from matplotlib.lines import Line2D
from datetime import timedelta

def getHigherLows(data: np.array, order, K):
  low_idx = argrelextrema(data, np.less, order=order)[0]
  lows = data[low_idx]
  extrema = []
  ex_deque = deque(maxlen=K)
  for i, idx in enumerate(low_idx):
    if i == 0:
      ex_deque.append(idx)
      continue
    if lows[i] < lows[i-1]:
      ex_deque.clear()
    ex_deque.append(idx)
    if len(ex_deque) == K:
      extrema.append(ex_deque.copy())
  return extrema

def getLowerHighs(data: np.array, order=5, K=2):
  high_idx = argrelextrema(data, np.greater, order=order)[0]
  highs = data[high_idx]
  extrema = []
  ex_deque = deque(maxlen=K)
  for i, idx in enumerate(high_idx):
    if i == 0:
      ex_deque.append(idx)
      continue
    if highs[i] > highs[i-1]:
      ex_deque.clear()
    ex_deque.append(idx)
    if len(ex_deque) == K:
      extrema.append(ex_deque.copy())
  return extrema

def getHigherHighs(data: np.array, order, K):
  high_idx = argrelextrema(data, np.greater, order = order)[0]
  highs = data[high_idx]
  extrema = []
  ex_deque = deque(maxlen=K)
  for i, idx in enumerate(high_idx):
    if i == 0:
      ex_deque.append(idx)
      continue
    if highs[i] < highs[i-1]:
      ex_deque.clear()
    ex_deque.append(idx)
    if len(ex_deque) == K:
      extrema.append(ex_deque.copy())
  return extrema

def getLowerLows(data: np.array, order, K):
  low_idx = argrelextrema(data, np.less, order=order)[0]
  lows = data[low_idx]
  extrema = []
  ex_deque = deque(maxlen=K)
  for i, idx in enumerate(low_idx):
    if i == 0:
      ex_deque.append(idx)
      continue
    if lows[i] > lows[i-1]:
      ex_deque.clear()
    ex_deque.append(idx)
    if len(ex_deque) == K:
      extrema.append(ex_deque.copy())
  return extrema

def get_trend(close_data, order, K):
    close_data = [x for x in close_data]
    close_data.reverse()
    data = pd.DataFrame()
    data['Close'] = close_data
    close = data['Close'].values
    hh = getHigherHighs(close, order, K)
    hl = getHigherLows(close, order, K)
    ll = getLowerLows(close, order, K)
    lh = getLowerHighs(close, order, K)
    patterns = []
    for pattern in hh:
        patterns.append(('hh', pattern[0], pattern[1], close[pattern[0]], close[pattern[1]]))
    for pattern in hl:
        patterns.append(('hl', pattern[0], pattern[1], close[pattern[0]], close[pattern[1]]))
    for pattern in ll:
        patterns.append(('ll', pattern[0], pattern[1], close[pattern[0]], close[pattern[1]]))
    for pattern in lh:
        patterns.append(('lh', pattern[0], pattern[1], close[pattern[0]], close[pattern[1]]))
    patterns.sort(key=lambda x: x[2], reverse=True)
    total_movements = patterns
    total_swing_up = 0
    total_swing_down = 0
    for x in total_movements:
        if x[0] == 'hh' or x[0] == 'hl':
            total_swing_up += (x[4] - x[3])
        else:
            total_swing_down += (x[4] - x[3])
    total_swing = total_swing_up + total_swing_down
    return total_swing
