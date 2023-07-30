#!/bin/bash -u

set -eE

Red='\033[0;31m'          # Red
Green='\033[0;32m'        # Green

docker_down() {
    docker-compose down -v --rmi all
}


trap 'exitfn $?' INT
trap 'exitfn $?' ERR

exitfn () {
    trap SIGINT              # Restore signal handling for SIGINT
    trap ERR
    docker_down
    echo -e $Red"ERROR OCCURRED"
    exit $1                   #   then exit script.
}

cd docker
docker-compose build 
docker-compose run dafny /home/dafny/docker/verify.sh /opt/dafny/dafny \
                src/proofs/no_slashable_attestations/main_theorem.dfy \
                src/proofs/no_slashable_blocks/main_theorem.dfy
                # src/proofs/implementation_refinement/attestation_creation/dvc_implementation_spec_proof.dfy \
                # src/proofs/implementation_refinement/attestation_creation/dvc_spec_spec_instr_refinement.dfy

docker_down
echo -e $Green"VERIFICATION WAS SUCCESSFUL!"
