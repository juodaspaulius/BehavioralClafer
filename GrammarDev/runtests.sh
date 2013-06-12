#!/bin/bash
Cmd="./Testclafer"
TestGrammarCmd=${1:-$Cmd}  

for file in ./tests/*.cfr
do
  echo "=========================================="
  echo "Running $TestGrammarCmd < ${file}"
  echo "=========================================="
  $TestGrammarCmd < ${file}
  echo "=========================================="
  echo "Done with ${file}"
  echo "=========================================="
done
