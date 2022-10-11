#!/bin/bash -u
set -eE

temp_file=$(mktemp)
dafny_command=$1

function on_exit()
{
    echo "Remove temporary file $temp_file"
    rm $temp_file || true
}

trap "on_exit" ERR

check_for_errors() {
    echo "Checking for errors"
    grep -q 'Dafny program verifier finished with.* 0 errors' $temp_file
    ! grep -q 'has no body' $temp_file
}

verify_file() {
    echo "Verifying file $1..."
    $dafny_command  /noCheating:1  /vcsLoad:1 /trace  /timeLimit:10000 /verifyAllModules $1 | tee $temp_file || true
    check_for_errors
}

shift 1
for arg in "$@"; do
  verify_file $arg
done

on_exit

echo "Verification was successful!"