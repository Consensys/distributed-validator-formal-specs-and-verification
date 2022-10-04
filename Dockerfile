
FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install -y wget && \
    apt-get install -y unzip && \
    apt-get install -y libgomp1 && \
    apt-get install -y dotnet-sdk-6.0

RUN wget https://github.com/dafny-lang/dafny/releases/download/v3.8.1/dafny-3.8.1-x64-ubuntu-16.04.zip -O /opt/dafny.zip && (cd /opt && unzip dafny.zip && rm dafny.zip)

RUN mkdir /home/dafny
WORKDIR /home/dafny

ENTRYPOINT [ "/opt/dafny/dafny" ]