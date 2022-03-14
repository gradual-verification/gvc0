
# shellcheck disable=SC1019
SUCCESS="[\033[0;32m✓\033[0m] -"
START="[\033[0;35m*\033[0m] -"
ERR="[\033[0;31mx\033[0m] -"

if [ -z $1 ] || [ -z $2 ]
then
  echo "$ERR Usage: ./benchmark.sh [file] [n]"
  exit 1
fi


FILE="$1"
NPATHS="$2"
JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"

PERM_DIR="./perms"
PERM_META="./perms.csv"
PERM_LEVELS="./levels.csv"

VERIFY_LOG="./verify.log"
VERIFY_CSV="./verify.csv"

EXEC_DIR="./compiled"
EXEC_CSV="./exec.csv"
EXEC_LOG="./bench_exec.log"
STAT_COLS="id,mean,stddev,median,user,system,min,max"

rm -rf $EXEC_DIR
mkdir $EXEC_DIR
rm -rf $PERM_DIR
mkdir $PERM_DIR

rm -f $VERIFY_LOG
rm -f $EXEC_LOG
rm -f $EXEC_CSV
rm -f $VERIFY_CSV

clean_csv () {
  REWRITTEN=""
  while read line; do
    IFS=',' read -ra COLUMNS <<< "$line";
    ID=$(basename ${COLUMNS[8]} | sed 's/\.[^/]*$//');
    if [[ "$ID" != "parameter_files" ]]
      then
        LINE=$ID
        unset 'COLUMNS[${#COLUMNS[@]}-1]'
        for i in "${COLUMNS[@]:1}"; do
          LINE="$LINE,$i"
        done
        REWRITTEN="$REWRITTEN\n$LINE"
      else
        REWRITTEN="$STAT_COLS"
    fi
  done < $1
  echo $REWRITTEN > $1
}

collect_files(){
 TARGETLIST=$(ls -m "$1")
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
 echo $FINAL_LIST
}

echo "$START Generating permutations to $PERM_DIR...\n"
java -jar $JAR $1 --perm=$NPATHS
echo "\n\n$SUCCESS Finished generating permutations."
echo "$SUCCESS Metadata stored in $PERM_META and $PERM_LEVELS.\n"

echo "$START Compiling baseline..."
cc0 ./perms/baseline.c0 -o ./compiled/baseline.out -L ./src/main/resources/
echo "$SUCCESS Compiled baseline.\n"

PERM_C0_LIST=$(collect_files $PERM_DIR)
echo "$START Executing verifier, compiling to $EXEC_DIR..."
hyperfine --runs 1 -i -L files $PERM_C0_LIST "java -jar $JAR $PERM_DIR/{files} --output=$EXEC_DIR/{files}.out --save-files >> $VERIFY_LOG 2>&1" --export-csv $VERIFY_CSV >> $VERIFY_LOG 2>&1
echo "$SUCCESS Verification completed."

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $VERIFY_LOG | wc -l)
FAILS_NOSP=$(echo $FAILS | sed 's/ *$//g')
echo "$ERR There were $FAILS_NOSP failing benchmarks.\n"
echo "$START Cleaning Verification CSV file..."
clean_csv $VERIFY_CSV
echo "$SUCCESS Verification CSV file cleaned, output to $VERIFY_CSV.\n"

rm -rf $EXEC_DIR/*.dSYM
EXEC_FILE_LIST=$(collect_files $EXEC_DIR)
echo "$START Beginning executions..."
hyperfine -N --runs 1 -i -L files $EXEC_FILE_LIST "$EXEC_DIR/{files} >> $EXEC_LOG 2>&1" --export-csv $EXEC_CSV >> $EXEC_LOG 2>&1
echo "$SUCCESS Executions completed.\n"

echo "$START Cleaning Execution CSV file..."
clean_csv $EXEC_CSV
echo "$SUCCESS Execution CSV file cleaned, output to $EXEC_CSV."

echo "$SUCCESS finished."