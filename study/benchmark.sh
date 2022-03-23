
# shellcheck disable=SC1019
JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"
SUCCESS="[\033[0;32m✓\033[0m] -"
START="[\033[0;35m*\033[0m] -"
ERR="[\033[0;31mx\033[0m] -"

NITER=1
NPATHS=1
PROFILE=""
DISABLE_BASELINE=""
HELP=0
TIMEOUT="15m"
SIMPLIFY=0
ROOT="./study/data"
UPPER_BOUND=1000
STEP=100

for i in "$@"; do
  case $i in
   -i=*|--iter=*)
     NITER="${i#*=}"
     shift # past argument=value
     ;;
    -p=*|--paths=*)
      NPATHS="${i#*=}"
      shift # past argument=value
      ;;
    --profiling)
      PROFILE="--profile"
      shift # past argument=value
      ;;
    -t=*|--timeout=*)
      TIMEOUT="${i#*=}"
      shift
      ;;
    --disable-baseline)
      DISABLE_BASELINE="--disable-baseline"
      shift
      ;;
    --disable-simplify)
      SIMPLIFY=1
      shift
      ;;
    -h|--help)
      HELP=1
      shift
      ;;
    -d=*|--dest=*)
      ROOT="${i#*=}"
      shift
      ;;
    -s=*|--step=*)
      STEP="${i#*=}"
      shift
      ;;
    -u=*|--upper=*)
      UPPER_BOUND="${i#*=}"
      shift # past argument=value
      ;;
    -*)
      echo "Unknown option $i"
      exit 1
      ;;
    *)
      FILE="${i#*=}"
      shift
      ;;
  esac
done
if [ -z "$FILE" ] || [ "$HELP" -ne 0 ]
then
  echo "Usage: ./study/benchmark.sh [OPTION] SOURCEFILE"
  echo "where OPTIONS is"
  echo "  -i=<n>     --iter=<n>             The number of iterations for timing execution.                     (Default: 1)"
  echo "  -p=<n>     --paths=<n>            The number of paths to sample.                                     (Default: 1)"
  echo "  -h         --help                 Print the options."
  echo "             --disable-simplify     Disable simplification of runtime check conditions."
  echo "  -u=<n>     --upper=<n>            The upper bound on the stress factor.                              (Default: 1000)"
  echo "  -s=<n>     --step=100             The step size from 1 to the upper bound.                           (Default: 100)"
  echo "  -d=<dir>   --dest=<dir>           Specify the destination directory for benchmarking output.         (Default: ./study/data)"
  echo "             --disable-baseline     Disable the baseline.                                              (Default: enabled)"
  exit 0
fi

echo "$START Generating $NPATHS paths with $NITER iterations for $FILE, timeout $TIMEOUT".
if [ "$DISABLE_BASELINE" != "" ]
then
    echo "$START Baseline \033[0;32menabled\033[0m."
else
    echo "$START Baseline \033[0;31mdisabled\033[0m."
fi
if [ "$PROFILE" != "" ]
then
    echo "$START Profiling \033[0;32menabled\033[0m."
else
    echo "$START Profiling \033[0;31mdisabled\033[0m."
fi
export DISABLE_SIMPLIFICATION=$SIMPLIFY


PERM_META="$ROOT/perms.csv"
PERM_LEVELS="$ROOT/levels.csv"

STAT_COLS="id,mean,stddev,median,user,system,min,max"

COMPILED="$ROOT/compiled"
BASELINE_COMPILED="$ROOT/baseline_compiled"
LOGS="$ROOT/logs"
LOG_EXEC="$LOGS/exec.log"
LOG_EXEC_BASELINE="$LOGS/exec_baseline.log"
CSV_EXEC="$ROOT/exec.csv"
CSV_EXEC_BASELINE="$ROOT/exec_baseline.csv"

PROF_EXEC="$ROOT/prof"
PROF_EXEC_BASELINE="$ROOT/prof_baseline"

rm -rf $ROOT
if [ "$PROFILE" != "" ]
then
  mkdir $PROF_EXEC
  mkdir $PROF_EXEC_BASELINE
fi

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
echo "$START Compiling benchmark..."
java -jar -Xss1g $JAR "$FILE" --benchmark="$ROOT" --paths="$NPATHS" $DISABLE_BASELINE $PROFILE
printf '\n%s Finished compiling benchmark.' "$SUCCESS"
rm -rf `find $ROOT -name '*.dSYM'`
echo "$SUCCESS Metadata stored in $PERM_META and $PERM_LEVELS."

EXEC_PERMS=$(collect_files $COMPILED)
EXEC_BASELINE=$(collect_files $BASELINE_COMPILED)

echo "$START Benchmarking execution of permutations, logs saved to $LOG_EXEC ..."
hyperfine -N --runs "$NITER" -i -L files "$EXEC_PERMS" "$COMPILED/{files} >> $LOG_EXEC 2>&1" --export-csv "$CSV_EXEC" >> "$LOG_EXEC" 2>&1
clean_param_csv "$CSV_EXEC" "files"
echo "$SUCCESS Finished benchmarking execution of permutations."

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $LOG_EXEC | wc -l)
FAILS_NOSP=$(echo "$FAILS" | sed 's/ //g')
if [ "$FAILS_NOSP" != "0" ]
then
echo "$ERR There were $FAILS_NOSP permutations that errored during execution."
fi

echo "$START Benchmarking execution of baseline, logs saved to $LOG_EXEC_BASELINE ..."
hyperfine -N --runs "$NITER" -i -L files "$EXEC_BASELINE" "$BASELINE_COMPILED/{files} >> $LOG_EXEC_BASELINE 2>&1" --export-csv "$CSV_EXEC_BASELINE" >> "$LOG_EXEC_BASELINE" 2>&1
clean_param_csv "$CSV_EXEC_BASELINE" "files"
echo "$START Benchmarking execution of baseline."

FAILS=$(grep -o 'Warning: Ignoring non-zero exit code.' $LOG_EXEC_BASELINE | wc -l)
FAILS_NOSP=$(echo "$FAILS" | sed 's/ //g')
if [ "$FAILS_NOSP" != "0" ]
then
echo "$ERR There were $FAILS_NOSP baselines that errored during execution."
fi

#echo "$SUCCESS Finished benchmarking execution of baseline."
echo "$SUCCESS Finished."