DIR="$1"
EXP="$2"
JAR="$3"

if [[ $1 != */ ]]
then
  DIR="$DIR/"
fi
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

hyperfine --warmup 1 --runs 1 -i -L files $FINAL_LIST "java -jar $JAR {files}" --show-output --export-csv ./verify.csv

while read line; do
  IFS=',' read -ra COLUMNS <<< "$line";
  FILE=$(echo ${COLUMNS[0]} | awk '{print $NF}');
  ID=$(basename $FILE | sed 's/\.[^.]*$//');
  LINE=$ID
  for i in "${COLUMNS[@]:1}"; do
    LINE="$LINE,$i"
  done
  echo $LINE
done < ./verified.csv