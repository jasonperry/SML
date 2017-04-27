#!/bin/bash

# use FMC to compile all files in fmprogs that don't start with err,
#  report which ones fail
for f in fmprogs/*.fm; do
    echo --- $f
    ./fmc $f > /dev/null
done
