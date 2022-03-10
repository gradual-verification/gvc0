FILE="$1"
NPATHS="$2"
JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"
CSV="./verify.csv"

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

hyperfine --warmup 1 --runs 1 -i -L files $FINAL_LIST "java -jar $JAR {files}" --show-output --export-csv $CSV

echo "Benchmarks completed."
echo "Cleaning CSV file..."

REWRITTEN=""
while read line; do
  IFS=',' read -ra COLUMNS <<< "$line";
  FILE=$(echo ${COLUMNS[0]} | awk '{print $NF}');
  ID=$(basename $FILE | sed 's/\.[^.]*$//');
  LINE=$ID
  for i in "${COLUMNS[@]:1:-1}"; do
    LINE="$LINE,$i"
  done
  REWRITTEN="$REWRITTEN\n$LINE"
done < $CSV
echo $REWRITTEN > $CSV
echo "CSV file cleaned."