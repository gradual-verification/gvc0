source ./study/shared.sh
for FILE in './study/stress/c0/*';
do ./study/stress.sh "$FILE" -d=./study/stress/csv/bst_none.csv	-u=100 -s=1 -i=6 echo
done;



#./study/stress.sh ./study/stress/composite_none.c0 -d=./study/stress/csv/composite_none.csv -u=100 -s=1 -i=6
#./study/stress.sh ./study/stress/list_none.c0 -d=./study/stress/csv/list_none.csv -u=100 -s=1 -i=6
#./study/stress.sh ./study/stress/bst_all.c0 -d=./study/stress/csv/bst_all.csv -u=100 -s=1 -i=6
#./study/stress.sh ./study/stress/composite_all.c0 -d=./study/stress/csv/composite_all.csv -u=100 -s=1 -i=6
#./study/stress.sh ./study/stress/list_all.c0 -d=./study/stress/csv/list_all.csv -u=100 -s=1 -i=6
