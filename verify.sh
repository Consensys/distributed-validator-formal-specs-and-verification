#!/bin/bash -u

set -eE

docker_down() {
    docker-compose down -v --rmi all
}


trap "docker_down" INT
trap "docker_down" ERR

exitfn () {
    trap SIGINT              # Restore signal handling for SIGINT
    docker_down
    exit                     #   then exit script.
}

cd docker
docker-compose build 
docker-compose run dafny /home/dafny/docker/verify.sh /opt/dafny/dafny \
                src/proofs/no_slashable_attestations/main_theorem.dfy \
                src/proofs/implementation_refinement/attestation_creation/dvc_implementation_spec_proof.dfy \
                src/proofs/implementation_refinement/attestation_creation/dvc_spec_spec_instr_refinement.dfy

docker_down
