# shellcheck disable=SC1019
source ./study/shared.sh
NITER=1
NPATHS=1
PROFILE=""
DISABLE_BASELINE=""
HELP=0
TIMEOUT="15m"
SIMPLIFY=0
ROOT="./study/data"
UPPER_BOUND=10
STEP=10

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

info "Generating $NPATHS paths with $NITER iterations for $FILE, timeout $TIMEOUT".
if [ "$DISABLE_BASELINE" != "" ]
then
    info "Baseline \033[0;32menabled\033[0m."
else
    info "Baseline \033[0;31mdisabled\033[0m."
fi
if [ "$PROFILE" != "" ]
then
    info "Profiling \033[0;32menabled\033[0m."
else
    info "Profiling \033[0;31mdisabled\033[0m."
fi
export DISABLE_SIMPLIFICATION=$SIMPLIFY
rm -rf $ROOT
info "Running benchmark..."
java -jar -Xss1g "$JAR" "$FILE" --benchmark="$ROOT" --paths="$NPATHS" --upper="$UPPER_BOUND" --step="$STEP" $DISABLE_BASELINE $PROFILE
success "\n Finished."
rm -rf `find $ROOT -name '*.dSYM'`