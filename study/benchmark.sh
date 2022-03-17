
# shellcheck disable=SC1019
SUCCESS="[\033[0;32m✓\033[0m] -"
START="[\033[0;35m*\033[0m] -"
ERR="[\033[0;31mx\033[0m] -"

if [ -z $1 ] || [ -z $2 ] || [ -z $3 ]
then
  echo "$ERR Usage: ./benchmark.sh [file] [n paths] [n iterations]"
  exit 1
fi

NPATHS="$2"
NITER="$3"
JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"

ROOT="./study/data"
LOGS="$ROOT/logs"
PERM_DIR="$ROOT/perms"
PERM_META="$ROOT/perms.csv"
PERM_LEVELS="$ROOT/levels.csv"

VERIFY_LOG="$LOGS/verify.log"
VERIFY_CSV="$ROOT/verify.csv"

EXEC_DIR="$ROOT/compiled"
EXEC_CSV="$ROOT/exec.csv"
EXEC_LOG="$LOGS/exec.log"

PROF_DIR="$ROOT/prof"

BASE_GEN_LOG="$LOGS/baseline_gen.log"
BASE_EXEC_LOG="$LOGS/baseline_exec.log"
BASE_PERM_DIR="$ROOT/baseline_perms"
BASE_EXEC_DIR="$ROOT/baseline_compiled"
BASE_GEN_CSV="$ROOT/baseline_gen.csv"
BASE_EXEC_CSV="$ROOT/baseline_exec.csv"
BASE_PROF_DIR="$ROOT/baseline_prof"

STAT_COLS="id,mean,stddev,median,user,system,min,max"

rm -rf $ROOT
mkdir $ROOT
mkdir $LOGS
mkdir $PERM_DIR
mkdir $BASE_PERM_DIR
mkdir $EXEC_DIR
mkdir $PROF_DIR
mkdir $BASE_EXEC_DIR
mkdir $BASE_PROF_DIR

clean_param_csv () {
  REWRITTEN=""
  while read line; do
    IFS=',' read -ra COLUMNS <<< "$line";
    ID=$(basename ${COLUMNS[8]} | sed 's/\.[^/]*$//');
    if [[ "$ID" != "parameter_$2" ]]
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
   if [ "$i" != "$2" ]
   then
      if [[ "$FINAL_LIST" == "" ]]
      then
          FINAL_LIST="$i"
      else
          FINAL_LIST="$FINAL_LIST,$i"
      fi
   fi
 done
 echo $FINAL_LIST
}

echo "$START Generating permutations to $PERM_DIR...\n"
java -jar $JAR $1 --perm=$NPATHS --output=$PERM_DIR
echo "\n\n$SUCCESS Finished generating permutations."
echo "$SUCCESS Metadata stored in $PERM_META and $PERM_LEVELS.\n"

PERM_C0_LIST=$(collect_files $PERM_DIR)
echo "$START Generating the baseline for each permutation to $BASE_PERM_DIR...\n"
hyperfine --runs $NITER -i -L files "$PERM_C0_LIST" "java -jar $JAR $PERM_DIR/{files} --baseline=$BASE_PERM_DIR/{files} --output=$BASE_EXEC_DIR/{files}.out --profile=$BASE_PROF_DIR/{files}.out >> $BASE_GEN_LOG 2>&1" --export-csv $BASE_GEN_CSV >> $BASE_GEN_LOG 2>&1
rm -rf $BASE_EXEC_DIR/*.dSYM
echo "\n\n$SUCCESS Finished generating the baseline for each permutation."
echo "$SUCCESS Generation time data stored in $BASE_GEN_CSV.\n"

echo "$START Cleaning baseline CSV file $BASE_GEN_CSV..."
clean_param_csv $BASE_GEN_CSV "files"
echo "$SUCCESS Baseline CSV file cleaned.\n"

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $BASE_GEN_LOG | wc -l)
FAILS_NOSP=$(echo $FAILS | sed 's/ *$//g')
if [ "$FAILS_NOSP" != "0" ]
then
echo "$ERR There were $FAILS_NOSP baseline permutations that failed to compile.\n"
fi

echo "$START Executing verifier, compiling to $EXEC_DIR..."
hyperfine --runs $NITER -i -L files $PERM_C0_LIST "java -Xss15m -jar $JAR $PERM_DIR/{files} --output=$EXEC_DIR/{files}.out --save-files --profile=$PROF_DIR/{files}.out >> $VERIFY_LOG 2>&1" --export-csv $VERIFY_CSV >> $VERIFY_LOG 2>&1
rm -rf $EXEC_DIR/*.dSYM
echo "$SUCCESS Verification completed, logs at $VERIFY_LOG"

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $VERIFY_LOG | wc -l)
FAILS_NOSP=$(echo $FAILS | sed 's/ *$//g')
if [ "$FAILS_NOSP" != "0" ]
then
echo "$ERR There were $FAILS_NOSP permutations that failed to verify.\n"
fi

echo "$START Cleaning verification CSV file $VERIFY_CSV..."
clean_param_csv $VERIFY_CSV "files"
echo "$SUCCESS Verification CSV file cleaned.\n"

EXEC_FILE_LIST=$(collect_files $EXEC_DIR)
echo "$START Beginning executions..."
hyperfine -N --runs $NITER -i -L files $EXEC_FILE_LIST "$EXEC_DIR/{files} >> $EXEC_LOG 2>&1" --export-csv $EXEC_CSV >> $EXEC_LOG 2>&1
echo "$SUCCESS Executions completed, logs at $EXEC_LOG\n"

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $EXEC_LOG | wc -l)
FAILS_NOSP=$(echo $FAILS | sed 's/ *$//g')
if [ "$FAILS_NOSP" != "0" ]
then
echo "$ERR There were $FAILS_NOSP permutations that failed to execute.\n"
fi


echo "$START Cleaning execution CSV file $EXEC_CSV..."
clean_param_csv $EXEC_CSV "files"
echo "$SUCCESS Execution CSV file cleaned."

BASE_EXEC_FILE_LIST=$(collect_files $BASE_EXEC_DIR)
echo "$START Beginning executions..."
hyperfine -N --runs $NITER -i -L files $BASE_EXEC_FILE_LIST "$BASE_EXEC_DIR/{files} >> $BASE_EXEC_LOG 2>&1" --export-csv $BASE_EXEC_CSV >> $BASE_EXEC_LOG 2>&1
echo "$SUCCESS Executions completed, logs at $BASE_EXEC_LOG\n"

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $BASE_EXEC_LOG | wc -l)
FAILS_NOSP=$(echo $FAILS | sed 's/ *$//g')
if [ "$FAILS_NOSP" != "0" ]
then
echo "$ERR There were $FAILS_NOSP baseline permutations that failed to execute.\n"
fi

echo "$START Cleaning execution CSV file $BASE_EXEC_CSV..."
clean_param_csv $BASE_EXEC_CSV "files"
echo "$SUCCESS Execution CSV file cleaned."

echo "$SUCCESS Finished."