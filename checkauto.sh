#!/bin/bash
# DO NOT EDIT THIS FILE

grep -q "auto" a10.v

if [ $? -eq 0 ]
then
  cat <<EOF
===========================================================
WARNING

Your Coq solution contains the string "auto".  Automation
is prohibited on this assignment.  Your solution will
receive zero credit.  Please revise your solution, such
that "auto" does not appear in it.
===========================================================
EOF
fi