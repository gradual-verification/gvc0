FILE="$1"
NPATHS="$2"
JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"
CSV="./verify.csv"
LOG="./bench_verify.log"
PERMS="./perms/"
EXE="./compiled/"
rm -rf $EXE
mkdir $EXE

echo "Generating permutations:"
java -jar $JAR $1 --perm=$NPATHS
echo "\nFinished generating permutations."

TARGETLIST=$(ls -m "$PERMS")
echo $TARGETLIST
TARGETS_NOSPACE=$(echo $TARGETLIST | tr -d '[:space:]')
IFS=',' read -ra INDIVIDUALS <<< "$TARGETS_NOSPACE"
FINAL_LIST=""
for i in "${INDIVIDUALS[@]}"; do
  if [[ "$FINAL_LIST" == "" ]]
    then
      FINAL_LIST="$i"
    else
      FINAL_LIST="$FINAL_LIST,$i"
  fi
done
echo $TARGETLIST


rm -f $LOG
echo "Compiling baseline..."
cc0 ./perms/baseline.c0 -o ./compiled/baseline.out -L ./src/main/resources/
echo "Compiled baseline."

echo "Executing verifier..."
hyperfine --runs 1 -i -L files $FINAL_LIST "java -jar $JAR $PERMS/{files} --output=$EXE/{files}.out --save-files >> $LOG 2>&1" --export-csv $CSV >> $LOG 2>&1
rm -rf $EXE*.dSYM
echo "Verification completed."

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $LOG | wc -l)
echo "There were $FAILS failing benchmarks."
echo "Cleaning CSV file..."
REWRITTEN=""
while read line; do
  IFS=',' read -ra COLUMNS <<< "$line";
  ID=$(basename ${COLUMNS[8]} | sed 's/\.[^/]*$//');
  if [[ "$ID" != "parameter_files" ]]
    then
      LINE=$ID
      for i in "${COLUMNS[@]:1:${#COLUMNS[@]}-1}"; do
        LINE="$LINE,$i"
      done
      REWRITTEN="$REWRITTEN\n$LINE"
  fi

done < $CSV
echo $REWRITTEN > $CSV
echo "CSV file cleaned."


