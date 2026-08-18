#!/bin/sh

set -eu

source_dir=$1
output=$2
build_dir=proverif_build

cp -RL "$source_dir" "$build_dir"
chmod -R u+w "$build_dir"
(
  cd "$build_dir"
  ./build clean
  ./build dune
)
cp "$build_dir/proverif" "$output"
