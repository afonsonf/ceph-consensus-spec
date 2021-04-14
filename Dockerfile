FROM ubuntu:latest

RUN apt-get update && apt-get install -y \
  openjdk-8-jre-headless \
  && rm -rf /var/lib/apt/lists/*

COPY tools /tools

RUN echo 'alias tla-sany="java -cp /tools/tla2tools.jar tla2sany.SANY"' >> ~/.bashrc
RUN echo 'alias tla-tlc="java -DTLA-Library=/tools/CommunityModules.jar -cp /tools/tla2tools.jar tlc2.TLC"' >> ~/.bashrc
RUN echo 'alias tla-trace="java -cp /tools/tla2tools.jar tlc2.TraceExplorer"' >> ~/.bashrc
RUN echo 'alias tla-repl="java -cp /tools/tla2tools.jar tlc2.REPL"' >> ~/.bashrc
