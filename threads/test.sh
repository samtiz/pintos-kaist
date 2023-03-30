#!/bin/sh
make
cd build
pintos -v -- -q run alarm-single