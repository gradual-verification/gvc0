#!/bin/bash
java -Xss15M -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar -b ./study/benchmarks/bst/ --only-exec -ws 4 -wu 64 -i 7 ./src/test/resources/quant-study/bst.c0; shutdown -h now