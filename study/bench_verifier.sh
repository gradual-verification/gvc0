for FILE in $1*; do
  echo Benchmarking $FILE...;
  java -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar $FILE
done