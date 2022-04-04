java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/bst.c0 --stress=./study/stress --w-step=2 --w-upper=128 --iter=3
java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/list.c0 --stress=./study/stress --w-step=2 --w-upper=128 --iter=3
java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/composite.c0 --stress./study/stress --w-step=2 --w-upper=128 --iter=3
java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/bst.c0 --benchmark=./study/bst --w-step=2 --w-upper=32 --iter=3 --paths=16
java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/list.c0 --benchmark=./study/list --w-step=2 --w-upper=32 --iter=3 --paths=16
java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/composite.c0 --benchmark=./study/composite --w-step=2 --w-upper=32 --iter=3 --paths=16
