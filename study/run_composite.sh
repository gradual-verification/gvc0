#!/bin/bash
java -Xss15M -jar -b ./study/benchmarks/composite/ --only-exec -ws 2 -wu 32 -i 7 ./src/test/resources/quant-study/composite.c0; shutdown -h now