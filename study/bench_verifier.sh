FILE="$1"
NPATHS="$2"
JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"
CSV="./verify.csv"
LOG="./bench_verify.log"

echo "Generating permutations:"
java -jar $JAR $1 --perm=$NPATHS
echo "\nFinished generating permutations."

DIR="./perms/"

TARGETLIST=$(ls -m "$DIR")
TARGETS_NOSPACE=$(echo $TARGETLIST | tr -d '[:space:]')
IFS=',' read -ra INDIVIDUALS <<< "$TARGETS_NOSPACE"
FINAL_LIST=""
for i in "${INDIVIDUALS[@]}"; do
  if [[ "$FINAL_LIST" == "" ]]
    then
      FINAL_LIST="$DIR$i"
    else
      FINAL_LIST="$FINAL_LIST,$DIR$i"
  fi
done

rm -f $LOG
echo "Executing benchmarks..."
hyperfine --runs 1 -i -L files $FINAL_LIST "java -jar $JAR {files} >> $LOG 2>&1" --export-csv $CSV >> $LOG 2>&1
echo "Benchmarks completed."
FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $LOG | wc -l)
echo "There were $FAILS failing benchmarks."
echo "Cleaning CSV file..."
REWRITTEN=""
while read line; do
  IFS=',' read -ra COLUMNS <<< "$line";
  FILE=$(echo ${COLUMNS[0]} | awk '{print $NF}');
  ID=$(basename $FILE | sed 's/\.[^.]*$//');
  LINE=$ID
  for i in "${COLUMNS[@]:1:${#COLUMNS[@]}-1}"; do
    LINE="$LINE,$i"
  done
  REWRITTEN="$REWRITTEN\n$LINE"
done < $CSV
echo $REWRITTEN > $CSV
echo "CSV file cleaned."