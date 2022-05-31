#!/bin/bash
java -Xss15M -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar -b ./study/benchmarks/list/ --only-exec -ws 8 -wu 128 -i 7 ./src/test/resources/quant-study/list.c0; shutdown -h now