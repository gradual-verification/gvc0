CSV="./exec.csv"
EXE="./compiled/"
LOG="./bench_exec.log"

TARGETLIST=$(ls -m "$EXE")
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

echo "Beginning executions..."
hyperfine --runs 1 -i -L files $FINAL_LIST "$EXE/{files} >> $LOG 2>&1" --export-csv $CSV >> $LOG 2>&1
echo "Executions completed."

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


