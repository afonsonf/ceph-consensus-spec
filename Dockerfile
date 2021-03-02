FROM ubuntu:latest

RUN apt-get update && apt-get install -y \
  wget \
  openjdk-8-jre-headless \
  && rm -rf /var/lib/apt/lists/*

RUN wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

RUN echo 'alias tla-sany="java -cp /tla2tools.jar tla2sany.SANY"' >> ~/.bashrc
RUN echo 'alias tla-tlc="java -cp /tla2tools.jar tlc2.TLC"' >> ~/.bashrc
RUN echo 'alias tla-trace="java -cp /tla2tools.jar tlc2.TraceExplorer"' >> ~/.bashrc
RUN echo 'alias tla-repl="java -cp /tla2tools.jar tlc2.REPL"' >> ~/.bashrc
