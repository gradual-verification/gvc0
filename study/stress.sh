source ./study/shared.sh

FILE=""
UPPER_BOUND=1000
NITER=3
STEP=10
PARAM="stress"
STAT_COLS="stress$HYPERFINE_COLS"
HELP=0

for i in "$@"; do
    case $i in
     -u=*|--upper=*)
       UPPER_BOUND="${i#*=}"
       shift # past argument=value
       ;;
     -i=*|--iter=*)
      NITER="${i#*=}"
      shift
      ;;
     -s=*|--step=*)
      STEP="${i#*=}"
      shift
      ;;
     -d=*|--dest=*)
      DEST="${i#*=}"
      shift
      ;;
      -h|--h)
      HELP=1
      shift
      ;;
      *)
        FILE="${i#*=}"
        shift
        ;;
    esac
done
if [ "$FILE" == "" ] || [ "$HELP" != "0" ]
then
  echo "Usage: ./study/scaling.sh SOURCEFILE "
  echo "where OPTIONS is"
  echo "  -u=<n>     --upper=<n>            The upper bound on the stress factor.       (Default: 1000)"
  echo "  -i=<n>     --iter=<n>             The number of iterations to measure over.   (Default: 1)"
  echo "  -s=<n>     --step=<n>             The step size from 1 to the upper bound.    (Default: 10)"
  echo "  -d=<file>  --dest=<file>          The destination .CSV file.                  (Default: SOURCEFILE.csv)"
  exit 0
fi
if [ "$DEST" == "" ]
then DEST="$FILE.csv"
fi

hyperfine -w 1 --show-output --parameter-scan "$PARAM" 0 "$UPPER_BOUND" -D "$STEP" --runs "$NITER" "cc0 $FILE -x -a \"s {$PARAM}\" -L ./src/main/resources/" --export-csv "$DEST"
clean_param_csv "$DEST" "$PARAM" "$STAT_COLS"
rm a.out
rm -rf *.dSYM
