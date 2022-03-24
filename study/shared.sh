JAR="target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar"
SUCCESS="[\033[0;32m✓\033[0m] -"
START="[\033[0;35m*\033[0m] -"
ERR="[\033[0;31mx\033[0m] -"
HYPERFINE_COLS=",mean,stddev,median,user,system,min,max"
export C0_MAX_ARRAYSIZE=10000000000000000

success () {
  echo "$SUCCESS $1"
}
info () {
  echo "$START $1"
}
err () {
  echo "$ERR $1"
}

filename_noext(){
  return "$(basename "$1" | sed 's/\.[^/]*$//')";
}

clean_param_csv () {
  REWRITTEN=""
  while read line; do
    IFS=',' read -ra COLUMNS <<< "$line";
    ID=$(filename_noext "${COLUMNS[8]}")
    if [[ "$ID" != "parameter_$2" ]]
      then
        LINE=$ID
        unset 'COLUMNS[${#COLUMNS[@]}-1]'
        for i in "${COLUMNS[@]:1}"; do
          LINE="$LINE,$i"
        done
        REWRITTEN="$REWRITTEN\n$LINE"
      else
        REWRITTEN="$3"
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

