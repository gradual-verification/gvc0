for FILE in $1; do
  ID=${FILE%%.*};
  cc0 FILE ./a.out;
  done