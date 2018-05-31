#!/usr/bin/env bash

echo "Configuring Coq..."
make clean
mkdir build
./configure -prefix build

