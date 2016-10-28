#!/usr/bin/python3

import sys

labels = ("." + "0123456789" +
          "abcdefghijklmnopqrstuvwxyz"
          "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
for line in sys.stdin.readlines():
  print(''.join([labels[int(c)] for c in line.split()]))
