#!/bin/bash


if [[ -z "$1" || ! $1 == *.spthy ]]; then
  echo "Usage: $0 TAMARIN_FILE DRY_RUN_OPTION"
  echo "Run $0 from the Rabbit root folder project"
  exit 0
else
  TAMARIN_FILE=$1
  DRY_RUN_OPT=$2


  lemma_names=()
  while IFS= read -r line; do 
    # Extract all lines that start with 'lemma'
    if [[ $line == lemma* ]]; then 
      set -- $line # split $line into words and assign them to $1, $2, $3, ...

      # We consider the second word to be a lemma name if it DOES NOT contain '[', ']' or ','
      if [[ ! "$2" == *,* && ! "$2" == *"]"* && ! "$2" == *"["* ]]; then
        lemma_names+=("$2") 
      fi
    fi
  done < $TAMARIN_FILE

  base=$(basename "$TAMARIN_FILE" .spthy) # basename of TAMARIN file with extension removed
  for lemma_name in "${lemma_names[@]}"; do
    cmd="tamarin-prover --prove=$lemma_name $TAMARIN_FILE > ./tamarin_logs/${base}_${lemma_name}.log"
    
    if [[ $DRY_RUN_OPT == "--dry-run" ]]; then
      echo "Would run: $cmd"
    else
      eval "$cmd" # Yes I know using eval is dangerous
    fi
  done
fi
