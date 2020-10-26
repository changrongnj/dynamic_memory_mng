#!/bin/sh
make
ls ./traces/trace* | xargs ./test_heap
