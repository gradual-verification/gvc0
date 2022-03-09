DIR="$1"
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
hyperfine --warmup 1 --runs 1 -i -L files $FINAL_LIST 'java -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar {files}' --show-output

