#!/bin/bash


# Compile Rabbit executable
dune build

# Check if the first argument is a file
if [ -f "$1" ]; then
  # Get filename of rabbit model including .rab extension
  rabbit_filename=$(basename $1)
  # Change extension to .spthy
  spthy_filename="${rabbit_filename%.*}.spthy"
  # Save in tamarin_models folder
  tamarin_spthy_path="./tamarin_models/${spthy_filename}"
  echo $tamarin_spthy_path
  _build/default/src/rabbit.exe --post-process --tag-transition $1 -o $tamarin_spthy_path
  
else  
  # Print explanation on how to use script and exit
  echo "Usage: $0 \".rab file to translate to TAMARIN\""
  exit 1 
fi
