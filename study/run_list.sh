#!/bin/bash
java -Xss15M -jar -b ./study/benchmarks/list/ --only-exec -ws 8 -wu 128 -i 7 ./src/test/resources/quant-study/list.c0; shutdown -h now