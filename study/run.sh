swapoff -a
echo ""
echo "Spawning the following services to benchmark each quantitative study example:"
systemd-run -G --wait --send-sighup --working-directory="$(pwd)" --property=CPUAffinity=0,1 --nice=-20 --property=MemoryMax=4G --property=MemorySwapMax=0G java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/bst.c0 --benchmark=./study/benchmarks/bst --only-exec --w-step=2 --w-upper=128 --iter=7 &
systemd-run -G --wait --send-sighup --working-directory="$(pwd)" --property=CPUAffinity=2,3 --nice=-20 --property=MemoryMax=4G --property=MemorySwapMax=0G java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/composite.c0 --benchmark=./study/benchmarks/composite --only-exec --w-step=2 --w-upper=128 --iter=7 &
systemd-run -G --wait --send-sighup --working-directory="$(pwd)" --property=CPUAffinity=4,5 --nice=-20 --property=MemoryMax=4G --property=MemorySwapMax=0G java -Xss15m -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar ./src/test/resources/quant-study/list.c0 --benchmark=./study/benchmarks/list --only-exec --w-step=2 --w-upper=128 --iter=7 &
echo "    * Use 'journalctl -f -u [name].service' to view logs in realtime."
echo "    * This command will terminate once all benchmarks have completed."
wait