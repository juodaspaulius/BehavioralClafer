#!/bin/bash
Cmd="./Testclafer"
TestGrammarCmd=${1:-$Cmd}  

for file in ./tests/*.cfr
do
  echo "=========================================="
  echo "Running $TestGrammarCmd -s ${file}"
  echo "------------------------------------------"
  $TestGrammarCmd -s ${file}
  echo "------------------------------------------"
  echo "Done with ${file}"
  echo "=========================================="
done
